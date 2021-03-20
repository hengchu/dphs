{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
module Data.DPHS.Typecheck.Fuzzi where

import Control.Monad
import Control.Monad.Catch
import Data.Semigroup
import Type.Reflection
import qualified Data.Map.Merge.Strict as M
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

asSens :: Sensitivity -> Double
asSens (Const _) = 0
asSens (Sens s) = s

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

type Cxt m = M.Map Name (ITypeInfo m)

--- |An intermediate type information value, that may not be grounded.
data ITypeInfo m where
  Atomic :: TypeInfo m -> ITypeInfo m
  Macro  :: (ITypeInfo m -> m (ITypeInfo m)) -> ITypeInfo m

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

newtype TypeChecker m a =
  TypeChecker { runTypeChecker :: Cxt m -> m (ITypeInfo m) }

class TyAlg (h :: (* -> *) -> * -> *) where
  tyAlg :: MonadThrow m => Alg h (TypeChecker m)

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
  | ExpectingType SomeTypeRep SomeTypeRep -- expected, actual
  | ExpectingNestedChecker
  | NotExpectingNestedChecker
  | ExpectingDeterminism
  | ExpectingZeroEpsilon
  deriving (Show, Eq, Ord)

data PositionAndTypeError = PTE {
  _ptePosition :: Pos,
  _pteTypeError :: TypeError
  } deriving (Show, Eq)

instance Exception PositionAndTypeError

throwTE :: MonadThrow m => Pos -> TypeError -> m a
throwTE p e = throwM (PTE p e)

expectAtomic :: MonadThrow m => Pos -> ITypeInfo m -> m (TypeInfo m)
expectAtomic _pos (Atomic t) = return t
expectAtomic pos _          = throwTE pos NotExpectingNestedChecker

expectMacro :: MonadThrow m => Pos -> ITypeInfo m -> m (ITypeInfo m -> m (ITypeInfo m))
expectMacro _pos (Macro f) = return f
expectMacro pos _         = throwTE pos ExpectingNestedChecker

-- For typechecking monadic commands, use the fact that monad bound names are globally unique, and pass them through the intermediate typing contexts as internal type info. However, these names should be used linearly, and once an intermediate has been consumed, remove it from the context.

tyMonadF :: MonadThrow m => Alg (MonadF :&: Pos) (TypeChecker m)
tyMonadF (Bind m k :&: p) = TypeChecker $ \cxt -> do
  mTi <- runTypeChecker m cxt
  kTyCheck <- runTypeChecker k cxt >>= expectMacro p
  kTyCheck mTi
tyMonadF (Ret e :&: _p) = TypeChecker $ \cxt -> do
  runTypeChecker e cxt

tyExprF :: MonadThrow m => Alg (ExprF :&: Pos) (TypeChecker m)
tyExprF (Deref (V x) :&: p) = TypeChecker $ \cxt -> do
  case M.lookup x cxt of
    Just xTi -> return xTi
    Nothing -> throwTE p (OutOfScopeVariable x)
tyExprF (Index arr idx :&: pos) = TypeChecker $ \cxt -> do
  arrTi <- runTypeChecker arr cxt >>= expectAtomic pos
  idxTi <- runTypeChecker idx cxt >>= expectAtomic pos
  case arrTi of
    ExprInfo arrS arrP arrT arrEps -> do
      when (arrP /= D) $ throwTE pos ExpectingDeterminism
      when (arrEps /= 0) $ throwTE pos ExpectingZeroEpsilon
      case idxTi of
        ExprInfo s p t eps -> do
          when (not $ isNonSensitive s) $ throwTE pos SensitiveArrayIndex
          return (Atomic (ExprInfo arrS (arrP <> p) (arrT <> t) eps))
        _ -> throwTE pos ExpectingAnExpression
    _ -> throwTE pos ExpectingAnExpression
tyExprF (Resize arr size :&: pos) = TypeChecker $ \cxt -> do
  arrTi <- runTypeChecker arr cxt >>= expectAtomic pos
  sizeTi <- runTypeChecker size cxt >>= expectAtomic pos
  case arrTi of
    ExprInfo arrS arrP arrT arrEps -> do
      when (arrP /= D) $ throwTE pos ExpectingDeterminism
      when (arrEps /= 0) $ throwTE pos ExpectingZeroEpsilon
      case sizeTi of
        ExprInfo s p t eps -> do
          when (not $ isNonSensitive s) $ throwTE pos SensitiveArraySize
          return (Atomic (ExprInfo arrS (arrP <> p) (arrT <> t) eps))
        _ -> throwTE pos ExpectingAnExpression
    _ -> throwTE pos ExpectingAnExpression
tyExprF (ArrLit xs :&: pos) = TypeChecker $ \cxt -> do
  xTis <- mapM (\checker -> runTypeChecker checker cxt >>= expectAtomic pos) xs
  let totalSens :: Maybe Sensitivity = foldMap (\ti -> preview #sensitivity ti) xTis
  let p = foldMap (\ti -> ti ^. #probAnn) xTis
  let t = foldMap (\ti -> ti ^. #termAnn) xTis
  let eps = getSum $ foldMap (\ti -> Sum (ti ^. #epsilon)) xTis
  case totalSens of
    Just s -> return (Atomic (ExprInfo s p t eps))
    Nothing -> throwTE pos ExpectingAnExpression

tyPrivMechF :: MonadThrow m => Alg (PrivMechF :&: Pos) (TypeChecker m)
tyPrivMechF (Laplace center width :&: pos) = TypeChecker $ \cxt -> do
  centerTi <- runTypeChecker center cxt >>= expectAtomic pos
  case centerTi of
    ExprInfo (asSens -> s) _ t e -> do
      let e' = s / width
      return (Atomic (ExprInfo (Sens 0) P t (e+e')))
    _ -> throwTE pos ExpectingAnExpression


