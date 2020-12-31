{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
module Data.DPHS.Typecheck.Fuzzi where

import Control.Monad
import Control.Monad.Catch
import qualified Data.Map.Strict as M

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

type Cxt = M.Map Name Sensitivity

data TypeInfo =
  ExprInfo {
    tiSensitivity :: Sensitivity,
    tiProbAnn :: ProbAnn,
    tiTermAnn :: TermAnn,
    tiEpsilon :: Double
  }
  | CmdInfo {
    tiPostContext :: Cxt,
    tiProbAnn :: ProbAnn,
    tiTermAnn :: TermAnn,
    tiEpsilon :: Double,
    tiDelta   :: Double
  } deriving (Show, Eq, Ord)

makeFieldLabelsWith abbreviatedFieldLabels ''TypeInfo
makePrisms ''TypeInfo

--- |An intermediate type information value, that may not be grounded.
data InternalTypeInfo m =
  Atomic {
    -- |The type info of a grounded term.
    itiTypeInfo :: TypeInfo
  }
  | Macro {
    -- |Delayed typechecker for a macro that is not yet instantiated.
    itiFunctionInfo :: TypeInfo -> m (InternalTypeInfo m)
  }

makeFieldLabelsWith abbreviatedFieldLabels ''InternalTypeInfo
makePrisms ''InternalTypeInfo

-- |A default expression type information that can be modified by lenses.
exprInfo :: InternalTypeInfo m
exprInfo = Atomic (ExprInfo (Sens 0) D T 0)

atomicCmdInfo :: Cxt -> ProbAnn -> TermAnn -> Double -> Double -> InternalTypeInfo m
atomicCmdInfo c p t e d = Atomic (CmdInfo c p t e d)

-- |Cast an internal type info into an expression type info.
asExprInfo :: InternalTypeInfo m -> Maybe (Sensitivity, ProbAnn, TermAnn, Double)
asExprInfo info =
  (,,,) <$> preview (#typeInfo % #sensitivity) info
        <*> preview (#typeInfo % #probAnn) info
        <*> preview (#typeInfo % #termAnn) info
        <*> preview (#typeInfo % #epsilon) info

-- |Cast an internal type info into a command type info
asCmdInfo :: InternalTypeInfo m -> Maybe (Cxt, ProbAnn, TermAnn, Double, Double)
asCmdInfo info =
  (,,,,) <$> preview (#typeInfo % #postContext) info
         <*> preview (#typeInfo % #probAnn) info
         <*> preview (#typeInfo % #termAnn) info
         <*> preview (#typeInfo % #epsilon) info
         <*> preview (#typeInfo % #delta) info

type TypeChecker m = Cxt -> m (InternalTypeInfo m)

class TyAlg (h :: (* -> *) -> * -> *) where
  tyAlg :: MonadThrow m => Alg h (K (TypeChecker m))

data TypeError =
  ExpectingAnExpression
  | BranchConditionProb
  | BranchConditionSensitive
  deriving (Show, Eq, Ord)

data PositionAndTypeError = PTE {
  _ptePosition :: Pos,
  _pteTypeError :: TypeError
  } deriving (Show, Eq)

instance Exception PositionAndTypeError

throwTE :: MonadThrow m => Pos -> TypeError -> m a
throwTE p e = throwM (PTE p e)

tyAlgEff :: MonadThrow m => Alg (EffF :&: Pos) (K (TypeChecker m))
tyAlgEff (Assign (V x) rhs :&: position) = K $ \cxt -> do
  tyRhs <- unK rhs cxt
  case asExprInfo tyRhs of
    Nothing -> throwTE position ExpectingAnExpression
    Just (s, p, t, e) ->
      let cxt' = M.insert x s cxt in
      return (atomicCmdInfo cxt' p t e 0)
tyAlgEff (Branch cond c1 c2 :&: position) = K $ \cxt -> do
  tyCond <- unK cond cxt
  case asExprInfo tyCond of
    Just (Sens 0, D, t, 0) -> do
      tyC1 <- unK c1 cxt
      tyC2 <- unK c2 cxt
      case (asCmdInfo tyC1, asCmdInfo tyC2) of
        (Just _, Just _) ->
          return undefined
        _ -> undefined
    Nothing -> throwTE position ExpectingAnExpression
    Just (Sens _, _, _, _) ->
      throwTE position BranchConditionSensitive
    Just (_, P, _, _) ->
      throwTE position BranchConditionProb

liftSum ''TyAlg
