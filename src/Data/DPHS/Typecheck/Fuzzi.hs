{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
module Data.DPHS.Typecheck.Fuzzi where

import Control.Monad
import Control.Monad.Catch
import Data.Semigroup
import qualified Data.Map.Merge.Strict as M
import qualified Data.Map.Strict as M

import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Annotation
import Data.Comp.Multi.Derive
import Data.Comp.Multi.HFunctor
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
  | ExpectingACommand
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
  | ExpectingNestedChecker
  | NotExpectingNestedChecker
  | ExpectingDeterminism
  | ExpectingZeroEpsilon
  | ExpectingZeroDelta
  | ExpectingZeroSensitivity
  | ExpectingTermination
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

tyMonadF :: MonadThrow m => Alg (SeqF :&: Pos) (TypeChecker m)
tyMonadF (Seq a b :&: pos) = TypeChecker $ \cxt -> do
  aTi <- runTypeChecker a cxt >>= expectAtomic pos
  case aTi of
    CmdInfo cxt' p t e d -> do
      bTi <- runTypeChecker b cxt' >>= expectAtomic pos
      (return . Atomic) (bTi & #probAnn %~ (<> p)
                         & #termAnn %~ (<> t)
                         & #epsilon %~ (+ e)
                         & #delta %~ (+ d))
    ExprInfo{} -> throwTE pos ExpectingACommand
      
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

tyLambdaF :: MonadThrow m => Alg (LambdaF :&: Pos) (TypeChecker m)
tyLambdaF (Lam (V x) body :&: _pos) = TypeChecker $ \cxt -> do
  (return . Macro) $ \xTy -> do
    let cxt' = M.insert x xTy cxt
    runTypeChecker body cxt'
tyLambdaF (App f arg :&: pos) = TypeChecker $ \cxt -> do
  fTi <- runTypeChecker f cxt >>= expectMacro pos
  argTi <- runTypeChecker arg cxt
  fTi argTi
tyLambdaF (Var (V x) :&: pos) = TypeChecker $ \cxt -> do
  case M.lookup x cxt of
    Nothing -> throwTE pos (OutOfScopeVariable x)
    Just t -> return t

mergeContext :: MonadThrow m => Pos -> Cxt m -> Cxt m -> m (Cxt m)
mergeContext pos = M.mergeA missingHelper missingHelper mergeHelper
  where missingHelper = M.traverseMissing (\v _ -> throwTE pos (OutOfScopeVariable v))
        mergeVar x t1 t2 =
          case (t1, t2) of
            ( Atomic (ExprInfo s1 _ _ _)
              , Atomic (ExprInfo s2 _ _ _)
              ) -> return (Atomic (ExprInfo (s1 <> s2) D T 0))
            ( Atomic (CmdInfo{})
              , _
              ) -> throwTE pos ExpectingAnExpression
            ( _,
              Atomic (CmdInfo{})
              ) -> throwTE pos ExpectingAnExpression
            _ -> throwTE pos (MergingMacroTypeInfo x)
        mergeHelper = M.zipWithAMatched mergeVar

isEquivalent :: Cxt m -> Cxt m -> Bool
isEquivalent m1 m2 =
  M.isSubmapOfBy isSubIType m1 m2 && M.isSubmapOfBy isSubIType m2 m1
  where isSubIType (Atomic (ExprInfo s1 _ _ _)) (Atomic (ExprInfo s2 _ _ _)) = isSubSens s1 s2
        isSubIType (Macro _)                    (Macro _) = True
        isSubIType _                            _         = False

tyEffF :: MonadThrow m => Alg (EffF :&: Pos) (TypeChecker m)
tyEffF (Assign (V x) rhs :&: pos) = TypeChecker $ \cxt -> do
  rhsTi <- runTypeChecker rhs cxt >>= expectAtomic pos
  case rhsTi of
    ExprInfo s P t eps -> do
      when (not $ isNonSensitive s) $ throwTE pos ExpectingZeroSensitivity
      let cxt' = M.insert x (Atomic $ ExprInfo (Sens 0) D T 0) cxt
      (return . Atomic) $ CmdInfo cxt' P t eps 0        
    ExprInfo s D t eps -> do
      when (eps /= 0) $ throwTE pos ExpectingZeroEpsilon
      let cxt' = M.insert x (Atomic $ ExprInfo s D T 0) cxt
      (return . Atomic) $ CmdInfo cxt' D t 0 0
    CmdInfo{} -> throwTE pos ExpectingAnExpression
tyEffF (Branch e c1 c2 :&: pos) = TypeChecker $ \cxt -> do
  eTi <- runTypeChecker e cxt >>= expectAtomic pos
  c1Ti <- runTypeChecker c1 cxt >>= expectAtomic pos
  c2Ti <- runTypeChecker c2 cxt >>= expectAtomic pos
  case eTi of
    ExprInfo s p t eps -> do
      when (p /= D) $ throwTE pos ExpectingDeterminism
      when (not $ isNonSensitive s) $ throwTE pos BranchConditionSensitive
      when (eps /= 0) $ throwTE pos ExpectingZeroEpsilon
      case (c1Ti, c2Ti) of
        (CmdInfo cxt1 p1 t1 eps1 dlt1, CmdInfo cxt2 p2 t2 eps2 dlt2) -> do
          cxt' <- mergeContext pos cxt1 cxt2
          (return . Atomic) (CmdInfo cxt' (p1 <> p2) (t <> t1 <> t2) (max eps1 eps2) (max dlt1 dlt2))
        _ -> throwTE pos ExpectingACommand
    CmdInfo{} -> throwTE pos ExpectingAnExpression
tyEffF (While e c :&: pos) = TypeChecker $ \cxt -> do
  eTi <- runTypeChecker e cxt >>= expectAtomic pos
  cTi <- runTypeChecker c cxt >>= expectAtomic pos
  case eTi of
    ExprInfo s p _t eps -> do
      when (not $ isNonSensitive s) $ throwTE pos ExpectingZeroSensitivity
      when (p /= D) $ throwTE pos ExpectingDeterminism
      when (eps /= 0) $ throwTE pos ExpectingZeroEpsilon
      case cTi of
        CmdInfo cxt' p _t eps dlt -> do
          when (not $ isEquivalent cxt cxt') $ throwTE pos CannotFindLoopInvariant
          when (p /= D) $ throwTE pos ExpectingDeterminism
          when (eps /= 0) $ throwTE pos ExpectingZeroEpsilon
          when (dlt /= 0) $ throwTE pos ExpectingZeroDelta
          (return . Atomic) $ CmdInfo cxt' D C 0 0
        _ -> throwTE pos ExpectingACommand
    _ -> throwTE pos ExpectingAnExpression

tyExtensionF :: (MonadThrow m, FreshM m)
             => Alg (ExtensionF :&: Pos) (TypeChecker m)
tyExtensionF (BMap x f :&: pos) = TypeChecker $ \cxt -> do
  fChecker <- runTypeChecker f cxt >>= expectMacro pos
  fOutTi0 <- fChecker (Atomic (ExprInfo (Sens 0) D T 0))
  fOutTiInf <- fChecker (Atomic (ExprInfo (Sens inf) D T 0))
  case (fOutTi0, fOutTiInf) of
    ( Atomic (ExprInfo s0 p0 t0 eps0)
      , Atomic (ExprInfo _sInf pInf tInf epsInf)
      ) -> do
      when (not $ isNonSensitive s0) $ throwTE pos ExpectingZeroSensitivity
      when (p0 /= D || pInf /= D) $ throwTE pos ExpectingDeterminism
      when (t0 /= T || tInf /= T) $ throwTE pos ExpectingTermination
      when (eps0 /= 0 || epsInf /= 0) $ throwTE pos ExpectingZeroEpsilon
      xTi <- runTypeChecker x cxt >>= expectAtomic pos
      case xTi of
        ExprInfo xSens _ _ _ ->
          (return . Atomic) (ExprInfo xSens D T 0)
        _ -> throwTE pos ExpectingAnExpression
    _ -> throwTE pos ExpectingAnExpression    
  where inf = 1/0
tyExtensionF (BSum bound x :&: pos) = TypeChecker $ \cxt -> do
  undefined
