{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
module Data.DPHS.Typecheck.Fuzzi where

import Data.Semigroup
import Control.Monad
import Control.Monad.Catch
import qualified Data.Map.Strict as M
import qualified Data.Map.Merge.Strict as M

import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Annotation
import Data.Comp.Multi.Derive
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.Term hiding (Cxt)
import Optics

import Data.DPHS.Syntax
import Data.DPHS.SrcLoc
import Data.DPHS.Fuzzi
import Data.DPHS.Name

-- |Annotation for whether a program fragment is deterministic or probabilistic.
data ProbAnn = D | P deriving (Show, Eq, Ord)

-- |Annotation for whether a program fragment co-terminates or terminates.
data TermAnn = T | C deriving (Show, Eq, Ord)

instance Monoid ProbAnn where
  mempty = D

instance Semigroup ProbAnn where
  D <> D = D
  _ <> _ = P

instance Monoid TermAnn where
  mempty = T

instance Semigroup TermAnn where
  T <> T = T
  _ <> _ = C

data Sensitivity =
  Const Double
  | Sens Double
  deriving (Show, Eq, Ord)

asSens :: Sensitivity -> Sensitivity
asSens (Const _) = Sens 0
asSens s = s

isSubSens :: Sensitivity -> Sensitivity -> Bool
isSubSens (Const _) (Sens _)  = True
isSubSens (Const a) (Const b) = a == b
isSubSens (Sens a)  (Sens b) = a <= b
isSubSens (Sens _)  (Const _) = False

isNonSensitive :: Sensitivity -> Bool
isNonSensitive s = s `isSubSens` (Sens 0)

instance Semigroup Sensitivity where
  (Sens a) <> (Sens b) = Sens (a + b)
  (Sens a) <> (Const _) = Sens a
  (Const _) <> (Sens b) = Sens b
  (Const _) <> (Const _) = Sens 0

instance Monoid Sensitivity where
  mempty = Sens 0

type Cxt m = M.Map Name (InternalTypeInfo m)

--- |An intermediate type information value, that may not be grounded.
data InternalTypeInfo m =
  Atomic {
    -- |The type info of a grounded term.
    itiTypeInfo :: TypeInfo m
  }
  | Macro {
    -- |Delayed typechecker for a macro that is not yet instantiated.
    itiFunctionInfo :: InternalTypeInfo m -> m (InternalTypeInfo m)
  }

data TypeInfo m =
  ExprInfo {
    tiSensitivity :: Sensitivity,
    tiProbAnn :: ProbAnn,
    tiTermAnn :: TermAnn,
    tiEpsilon :: Double
  }
  | CmdInfo {
    tiPostContext :: Cxt m,
    tiProbAnn :: ProbAnn,
    tiTermAnn :: TermAnn,
    tiEpsilon :: Double,
    tiDelta   :: Double
  } 

makeFieldLabelsWith abbreviatedFieldLabels ''TypeInfo
makePrisms ''TypeInfo

makeFieldLabelsWith abbreviatedFieldLabels ''InternalTypeInfo
makePrisms ''InternalTypeInfo

-- |A default expression type information that can be modified by lenses.
exprInfo :: InternalTypeInfo m
exprInfo = Atomic (ExprInfo (Sens 0) D T 0)

atomicCmdInfo :: Cxt m -> ProbAnn -> TermAnn -> Double -> Double -> InternalTypeInfo m
atomicCmdInfo c p t e d = Atomic (CmdInfo c p t e d)

-- |Cast an internal type info into an expression type info.
asExprInfo :: InternalTypeInfo m -> Maybe (Sensitivity, ProbAnn, TermAnn, Double)
asExprInfo info =
  (,,,) <$> preview (#typeInfo % #sensitivity) info
        <*> preview (#typeInfo % #probAnn) info
        <*> preview (#typeInfo % #termAnn) info
        <*> preview (#typeInfo % #epsilon) info

-- |Cast an internal type info into a command type info
asCmdInfo :: InternalTypeInfo m -> Maybe (Cxt m, ProbAnn, TermAnn, Double, Double)
asCmdInfo info =
  (,,,,) <$> preview (#typeInfo % #postContext) info
         <*> preview (#typeInfo % #probAnn) info
         <*> preview (#typeInfo % #termAnn) info
         <*> preview (#typeInfo % #epsilon) info
         <*> preview (#typeInfo % #delta) info

type TypeChecker m = Cxt m -> m (InternalTypeInfo m)

class TyAlg (h :: (* -> *) -> * -> *) where
  tyAlg :: MonadThrow m => Alg h (K (TypeChecker m))

liftSum ''TyAlg

data TypeError =
  ExpectingAnExpression
  | BranchConditionProb
  | BranchConditionSensitive
  | CannotFindLoopInvariant
  | ExpectingLoopBodyCommand
  | ExpectingTrueBranchCommand
  | ExpectingFalseBranchCommand
  | LoopHasPrivacyCost Double Double
  | OutOfScopeVariable Name
  | SensitiveArrayIndex
  | SensitiveArraySize
  | DivergedTypeInfo Name
  | MergingMacroTypeInfo Name
  deriving (Show, Eq, Ord)

data PositionAndTypeError = PTE {
  _ptePosition :: Pos,
  _pteTypeError :: TypeError
  } deriving (Show, Eq)

instance Exception PositionAndTypeError

throwTE :: MonadThrow m => Pos -> TypeError -> m a
throwTE p e = throwM (PTE p e)

whenMissing :: MonadThrow m => Pos -> Name -> InternalTypeInfo m -> m a
whenMissing pos x _ = throwTE pos (DivergedTypeInfo x)

whenMatching :: MonadThrow m
             => Pos
             -> Name
             -> InternalTypeInfo m
             -> InternalTypeInfo m
             -> m (InternalTypeInfo m)
whenMatching pos x Macro{} Macro{} = throwTE pos (MergingMacroTypeInfo x)
whenMatching pos x (Atomic ty1) (Atomic ty2) =
  case (ty1, ty2) of
    (ExprInfo s1 p1 t1 eps1, ExprInfo s2 p2 t2 eps2) ->
      return . Atomic $ ExprInfo (s1 <> s2) (p1 <> p2) (t1 <> t2) (max eps1 eps2)
    (CmdInfo cxt1 p1 t1 eps1 del1, CmdInfo cxt2 p2 t2 eps2 del2) -> do
      cxt <- mergeBranchCxt pos cxt1 cxt2
      return . Atomic $ CmdInfo cxt (p1 <> p2) (t1 <> t2) (max eps1 eps2) (max del1 del2)
    _ -> throwTE pos (DivergedTypeInfo x) 
whenMatching pos x _ _ = throwTE pos (DivergedTypeInfo x)

mergeBranchCxt :: MonadThrow m => Pos -> Cxt m -> Cxt m -> m (Cxt m)
mergeBranchCxt p =
  let missingHelper = M.traverseMaybeMissing (whenMissing p)
      matchHelper = M.zipWithAMatched (whenMatching p)
  in M.mergeA missingHelper missingHelper matchHelper

-- For typechecking monadic commands, use the fact that monad bound names are globally unique, and pass them through the intermediate typing contexts as internal type info. However, these names should be used linearly, and once an intermediate has been consumed, remove it from the context.
