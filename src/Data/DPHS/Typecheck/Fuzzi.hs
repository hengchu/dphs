{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
module Data.DPHS.Typecheck.Fuzzi where

--import Debug.Trace
import Data.Functor.Identity
import Control.Monad
import Control.Monad.Catch
import Data.Semigroup
import Control.Monad.State.Strict
import qualified Data.Map.Merge.Strict as M
import qualified Data.Map.Strict as M

import Data.Comp.Multi.Term hiding (Cxt)
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Annotation
import Data.Comp.Multi.Derive
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

scaleSens :: Double -> Sensitivity -> Sensitivity
scaleSens _k (Const _) = Sens 0
scaleSens  k (Sens s) = Sens (s * k)

sensMult :: Sensitivity -> Sensitivity -> Sensitivity
sensMult (Const k1) (Const k2) = Const (k1 * k2)
sensMult (Const k) (Sens s) = Sens (abs (k * s))
sensMult (Sens s) (Const k) = Sens (abs (k * s))
sensMult (Sens 0) (Sens 0) = Sens 0
sensMult _        _        = Sens inf
  where inf = 1/0

sensDiv :: Sensitivity -> Sensitivity -> Sensitivity
sensDiv (Const k1) (Const k2) = Const (k1 / k2)
sensDiv (Sens s) (Const k) = Sens (abs (k / s))
sensDiv (Sens 0) (Sens 0) = Sens 0
sensDiv _        _        = Sens inf
  where inf = 1/0

sensMod :: Sensitivity -> Sensitivity -> Sensitivity
sensMod (Const k1) (Const k2) = Const (fromIntegral @Integer $ round k1 `mod` round k2)
sensMod (Sens 0) (Const _k) = Sens 0
sensMod (Sens _) (Const k) = Sens k
sensMod _        _        = Sens inf
  where inf = 1/0

instance Semigroup Sensitivity where
  (Sens a) <> (Sens b) = Sens (a + b)
  (Sens a) <> (Const _) = Sens a
  (Const _) <> (Sens b) = Sens b
  (Const _) <> (Const _) = Sens 0

instance Monoid Sensitivity where
  mempty = Sens 0

type Cxt m = M.Map Name (ITypeInfo m)

weakenConst :: Cxt m -> Cxt m
weakenConst = M.map go
  where go (Atomic (ExprInfo s p t eps)) = Atomic (ExprInfo (Sens $ asSens s) p t eps)
        go a = a

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
  | NegativeBSumBound
  | NegativePartitionCount
  | DivisionBySensitiveTerm
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

tySeqF :: MonadThrow m => Alg (SeqF :&: Pos) (TypeChecker m)
tySeqF (Seq a b :&: pos) = TypeChecker $ \cxt -> do
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
          -- TODO: only need to weaken const for modified variables
          when (not $ isEquivalent (weakenConst cxt) (weakenConst cxt')) $ throwTE pos CannotFindLoopInvariant
          when (p /= D) $ throwTE pos ExpectingDeterminism
          when (eps /= 0) $ throwTE pos ExpectingZeroEpsilon
          when (dlt /= 0) $ throwTE pos ExpectingZeroDelta
          (return . Atomic) $ CmdInfo (weakenConst cxt') D C 0 0
        _ -> throwTE pos ExpectingACommand
    _ -> throwTE pos ExpectingAnExpression

tyExtensionF :: MonadThrow m
             => Alg (ExtensionF :&: Pos) (TypeChecker m)
tyExtensionF (BMap x f :&: pos) = TypeChecker $ \cxt -> do
  fChecker <- runTypeChecker f cxt >>= expectMacro pos
  fOutTi0 <- fChecker (Atomic (ExprInfo (Sens 0) D T 0)) >>= expectAtomic pos
  fOutTiInf <- fChecker (Atomic (ExprInfo (Sens inf) D T 0)) >>= expectAtomic pos
  case (fOutTi0, fOutTiInf) of
    ( ExprInfo s0 p0 t0 eps0
      , ExprInfo _sInf pInf tInf epsInf
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
  when (bound < 0) $ throwTE pos NegativeBSumBound
  xTi <- runTypeChecker x cxt >>= expectAtomic pos
  case xTi of
    ExprInfo s p t eps -> do
      when (p /= D) $ throwTE pos ExpectingDeterminism
      when (eps /= 0) $ throwTE pos ExpectingZeroEpsilon
      (return . Atomic) (ExprInfo (scaleSens bound s) D t 0) 
    _ -> throwTE pos ExpectingACommand
tyExtensionF (AMap x f :&: pos) = TypeChecker $ \cxt -> do
  fChecker <- runTypeChecker f cxt >>= expectMacro pos
  fOutTi0 <- fChecker (Atomic (ExprInfo (Sens 0) D T 0)) >>= expectAtomic pos
  fOutTi1 <- fChecker (Atomic (ExprInfo (Sens 1) D T 0)) >>= expectAtomic pos
  case (fOutTi0, fOutTi1) of
    ( ExprInfo s0 p0 t0 eps0
      , ExprInfo s1 p1 t1 eps1
      ) -> do
      when (not $ isNonSensitive s0) $ throwTE pos ExpectingZeroSensitivity
      when (p0 /= D || p1 /= D) $ throwTE pos ExpectingDeterminism
      when (eps0 /= 0 || eps1 /= 0) $ throwTE pos ExpectingZeroEpsilon
      xTi <- runTypeChecker x cxt >>= expectAtomic pos
      case xTi of
        ExprInfo xSens _ t _ ->
          let k = case s1 of
                Sens k -> k
                Const _ -> 0
          in (return . Atomic) (ExprInfo (scaleSens k xSens) D (t <> t0 <> t1) 0)
        _ -> throwTE pos ExpectingAnExpression
    _ -> throwTE pos ExpectingAnExpression
tyExtensionF (Part n x f :&: pos) = TypeChecker $ \cxt -> do
  when (n < 0) $ throwTE pos NegativePartitionCount
  fChecker <- runTypeChecker f cxt >>= expectMacro pos
  fOutTi0 <- fChecker (Atomic (ExprInfo (Sens 0) D T 0)) >>= expectAtomic pos
  fOutTiInf <- fChecker (Atomic (ExprInfo (Sens inf) D T 0)) >>= expectAtomic pos
  case (fOutTi0, fOutTiInf) of
    ( ExprInfo s0 p0 t0 eps0
      , ExprInfo _sInf pInf tInf epsInf
      ) -> do
      when (not $ isNonSensitive s0) $ throwTE pos ExpectingZeroSensitivity
      when (p0 /= D || pInf /= D) $ throwTE pos ExpectingDeterminism
      when (t0 /= T || tInf /= T) $ throwTE pos ExpectingTermination
      when (eps0 /= 0 || epsInf /= 0) $ throwTE pos ExpectingZeroEpsilon
      xTi <- runTypeChecker x cxt >>= expectAtomic pos
      case xTi of
        ExprInfo s _ _ _ ->
          (return . Atomic) (ExprInfo s D T 0)
        _ -> throwTE pos ExpectingACommand
    _ -> throwTE pos ExpectingAnExpression
  where inf = 1/0
tyExtensionF (AdvComp n omega c :&: pos) = TypeChecker $ \cxt -> do
  cTi <- runTypeChecker c cxt >>= expectAtomic pos
  case cTi of
    CmdInfo cxt' p t eps dlt -> do
      let nDouble = fromIntegral n
      let eps' = eps * sqrt (2 * nDouble * log (1/omega)) +
                 nDouble * eps * (exp eps - 1)
      let dlt' = nDouble * dlt + omega
      when (not $ isEquivalent cxt cxt') $ throwTE pos CannotFindLoopInvariant
      (return . Atomic) (CmdInfo cxt' p t eps' dlt')
    _ -> throwTE pos ExpectingACommand

tyArithF :: MonadThrow m => Alg (ArithF :&: Pos) (TypeChecker m)
tyArithF (IntLit v :&: _) =
  TypeChecker $ \_cxt -> (return . Atomic) (ExprInfo (Const (fromIntegral v)) D T 0) 
tyArithF (FracLit v :&: _) =
  TypeChecker $ \_cxt -> (return . Atomic) (ExprInfo (Const (fromRational v)) D T 0) 
tyArithF (Add e1 e2 :&: pos) = TypeChecker $ \cxt -> do
  e1Ti <- runTypeChecker e1 cxt >>= expectAtomic pos
  e2Ti <- runTypeChecker e2 cxt >>= expectAtomic pos
  case (e1Ti, e2Ti) of
    ( ExprInfo s1 p1 t1 eps1
      , ExprInfo s2 p2 t2 eps2
      ) ->
      case (s1, s2) of
        (Const k1, Const k2) ->
          (return . Atomic) (ExprInfo (Const (k1 + k2)) (p1 <> p2) (t1 <> t2) (eps1+eps2))
        _ ->
          (return . Atomic) (ExprInfo (s1 <> s2) (p1 <> p2) (t1 <> t2) (eps1+eps2))
    _ -> throwTE pos ExpectingAnExpression
tyArithF (Sub e1 e2 :&: pos) = TypeChecker $ \cxt -> do
  e1Ti <- runTypeChecker e1 cxt >>= expectAtomic pos
  e2Ti <- runTypeChecker e2 cxt >>= expectAtomic pos
  case (e1Ti, e2Ti) of
    ( ExprInfo s1 p1 t1 eps1
      , ExprInfo s2 p2 t2 eps2
      ) ->
      case (s1, s2) of
        (Const k1, Const k2) ->
          (return . Atomic) (ExprInfo (Const (k1 - k2)) (p1 <> p2) (t1 <> t2) (eps1+eps2))
        _ ->
          (return . Atomic) (ExprInfo (s1 <> s2) (p1 <> p2) (t1 <> t2) (eps1+eps2))
    _ -> throwTE pos ExpectingAnExpression
tyArithF (Abs e :&: pos) = TypeChecker $ \cxt -> do
  eTi <- runTypeChecker e cxt >>= expectAtomic pos
  case eTi of
    ExprInfo s p t eps ->
      case s of
        Const k -> (return . Atomic) (ExprInfo (Const (abs k)) p t eps)
        _ -> (return . Atomic) (ExprInfo s p t eps) -- true by reverse triangle inequality
    _ -> throwTE pos ExpectingAnExpression
tyArithF (Signum e :&: pos) = TypeChecker $ \cxt -> do
  eTi <- runTypeChecker e cxt >>= expectAtomic pos
  case eTi of
    ExprInfo s p t eps ->
      case s of
        Const k -> (return . Atomic) (ExprInfo (Const (signum k)) p t eps)
        Sens 0 -> (return . Atomic) (ExprInfo (Sens 0) p t eps)
        _ -> (return . Atomic) (ExprInfo (Sens 2) p t eps)
    _ -> throwTE pos ExpectingAnExpression
tyArithF (Mult e1 e2 :&: pos) = TypeChecker $ \cxt -> do
  e1Ti <- runTypeChecker e1 cxt >>= expectAtomic pos
  e2Ti <- runTypeChecker e2 cxt >>= expectAtomic pos
  case (e1Ti, e2Ti) of
    ( ExprInfo s1 p1 t1 eps1
      , ExprInfo s2 p2 t2 eps2
      ) ->
      (return . Atomic) (ExprInfo (sensMult s1 s2) (p1 <> p2) (t1 <> t2) (eps1+eps2))
    _ -> throwTE pos ExpectingAnExpression
tyArithF (Div e1 e2 :&: pos) = TypeChecker $ \cxt -> do
  e1Ti <- runTypeChecker e1 cxt >>= expectAtomic pos
  e2Ti <- runTypeChecker e2 cxt >>= expectAtomic pos
  case (e1Ti, e2Ti) of
    ( ExprInfo s1 p1 t1 eps1
      , ExprInfo s2 p2 t2 eps2
      ) -> do
      when (not $ isNonSensitive s2) $ throwTE pos DivisionBySensitiveTerm
      case s2 of
        Const _ ->
          (return . Atomic) (ExprInfo (sensDiv s1 s2) (p1 <> p2) (t1 <> t2) (eps1+eps2))
        Sens _ ->
          (return . Atomic) (ExprInfo (sensDiv s1 s2) (p1 <> p2) C (eps1+eps2))
    _ -> throwTE pos ExpectingAnExpression
tyArithF (IDiv e1 e2 :&: pos) = TypeChecker $ \cxt -> do
  e1Ti <- runTypeChecker e1 cxt >>= expectAtomic pos
  e2Ti <- runTypeChecker e2 cxt >>= expectAtomic pos
  case (e1Ti, e2Ti) of
    ( ExprInfo s1 p1 t1 eps1
      , ExprInfo s2 p2 t2 eps2
      ) -> do
      when (not $ isNonSensitive s2) $ throwTE pos DivisionBySensitiveTerm
      case s2 of
        Const _ ->
          (return . Atomic) (ExprInfo (sensDiv s1 s2) (p1 <> p2) (t1 <> t2) (eps1+eps2))
        Sens _ ->
          (return . Atomic) (ExprInfo (sensDiv s1 s2) (p1 <> p2) C (eps1+eps2))
    _ -> throwTE pos ExpectingAnExpression
tyArithF (IMod e1 e2 :&: pos) = TypeChecker $ \cxt -> do
  e1Ti <- runTypeChecker e1 cxt >>= expectAtomic pos
  e2Ti <- runTypeChecker e2 cxt >>= expectAtomic pos
  case (e1Ti, e2Ti) of
    ( ExprInfo s1 p1 t1 eps1
      , ExprInfo s2 p2 t2 eps2
      ) -> do
      when (not $ isNonSensitive s2) $ throwTE pos DivisionBySensitiveTerm
      case s2 of
        Const _ ->
          (return . Atomic) (ExprInfo (sensMod s1 s2) (p1 <> p2) (t1 <> t2) (eps1+eps2))
        Sens _ ->
          (return . Atomic) (ExprInfo (sensMod s1 s2) (p1 <> p2) C (eps1+eps2))
    _ -> throwTE pos ExpectingAnExpression
tyArithF (Exp e :&: pos) = TypeChecker $ \cxt -> do
  eTi <- runTypeChecker e cxt >>= expectAtomic pos
  case eTi of
    ExprInfo s p t eps ->
      case s of
        Const k -> (return . Atomic) $ ExprInfo (Const (exp k)) p t eps
        Sens 0 -> (return . Atomic) $ ExprInfo (Sens 0) p t eps
        Sens _ -> (return . Atomic) $ ExprInfo (Sens inf) p t eps
    _ -> throwTE pos ExpectingAnExpression
  where inf = 1/0
tyArithF (Log e :&: pos) = TypeChecker $ \cxt -> do
  eTi <- runTypeChecker e cxt >>= expectAtomic pos
  case eTi of
    ExprInfo s p t eps ->
      case s of
        Const k -> (return . Atomic) $ ExprInfo (Const (log k)) p t eps
        Sens 0 -> (return . Atomic) $ ExprInfo (Sens 0) p t eps
        Sens _ -> (return . Atomic) $ ExprInfo (Sens inf) p t eps
    _ -> throwTE pos ExpectingAnExpression
  where inf = 1/0
tyArithF (Sqrt e :&: pos) = TypeChecker $ \cxt -> do
  eTi <- runTypeChecker e cxt >>= expectAtomic pos
  case eTi of
    ExprInfo s p t eps ->
      case s of
        Const k -> (return . Atomic) $ ExprInfo (Const (sqrt k)) p t eps
        Sens 0 -> (return . Atomic) $ ExprInfo (Sens 0) p t eps
        Sens _ -> (return . Atomic) $ ExprInfo (Sens inf) p t eps
    _ -> throwTE pos ExpectingAnExpression
  where inf = 1/0

sensCmpM :: MonadThrow m => Pos -> TypeInfo m -> TypeInfo m -> m (ITypeInfo m)
sensCmpM _pos (ExprInfo s1 p1 t1 eps1) (ExprInfo s2 p2 t2 eps2) =
  case (isNonSensitive s1, isNonSensitive s2) of
    (True, True) ->
      (return . Atomic) (ExprInfo (Sens 0) (p1 <> p2) (t1 <> t2) (eps1+eps2))
    _ ->
      (return . Atomic) (ExprInfo (Sens inf) (p1 <> p2) (t1 <> t2) (eps1+eps2))
  where inf = 1/0
sensCmpM pos _ _ = throwTE pos ExpectingAnExpression

tyCompareF :: MonadThrow m => Alg (CompareF :&: Pos) (TypeChecker m)
tyCompareF (IsEq e1 e2 :&: pos) = TypeChecker $ \cxt -> do
  e1Ti <- runTypeChecker e1 cxt >>= expectAtomic pos
  e2Ti <- runTypeChecker e2 cxt >>= expectAtomic pos
  sensCmpM pos e1Ti e2Ti
tyCompareF (IsNeq e1 e2 :&: pos) = TypeChecker $ \cxt -> do
  e1Ti <- runTypeChecker e1 cxt >>= expectAtomic pos
  e2Ti <- runTypeChecker e2 cxt >>= expectAtomic pos
  sensCmpM pos e1Ti e2Ti
tyCompareF (IsLt e1 e2 :&: pos) = TypeChecker $ \cxt -> do
  e1Ti <- runTypeChecker e1 cxt >>= expectAtomic pos
  e2Ti <- runTypeChecker e2 cxt >>= expectAtomic pos
  sensCmpM pos e1Ti e2Ti
tyCompareF (IsLe e1 e2 :&: pos) = TypeChecker $ \cxt -> do
  e1Ti <- runTypeChecker e1 cxt >>= expectAtomic pos
  e2Ti <- runTypeChecker e2 cxt >>= expectAtomic pos
  sensCmpM pos e1Ti e2Ti
tyCompareF (IsGt e1 e2 :&: pos) = TypeChecker $ \cxt -> do
  e1Ti <- runTypeChecker e1 cxt >>= expectAtomic pos
  e2Ti <- runTypeChecker e2 cxt >>= expectAtomic pos
  sensCmpM pos e1Ti e2Ti
tyCompareF (IsGe e1 e2 :&: pos) = TypeChecker $ \cxt -> do
  e1Ti <- runTypeChecker e1 cxt >>= expectAtomic pos
  e2Ti <- runTypeChecker e2 cxt >>= expectAtomic pos
  sensCmpM pos e1Ti e2Ti
tyCompareF (And e1 e2 :&: pos)  = TypeChecker $ \cxt -> do
  e1Ti <- runTypeChecker e1 cxt >>= expectAtomic pos
  e2Ti <- runTypeChecker e2 cxt >>= expectAtomic pos
  sensCmpM pos e1Ti e2Ti
tyCompareF (Or e1 e2 :&: pos)  = TypeChecker $ \cxt -> do
  e1Ti <- runTypeChecker e1 cxt >>= expectAtomic pos
  e2Ti <- runTypeChecker e2 cxt >>= expectAtomic pos
  sensCmpM pos e1Ti e2Ti
tyCompareF (Neg e :&: pos) = TypeChecker $ \cxt -> do
  runTypeChecker e cxt >>= expectAtomic pos >>= return . Atomic

instance TyAlg (ArithF :&: Pos) where
  tyAlg = tyArithF
instance TyAlg (CompareF :&: Pos) where
  tyAlg = tyCompareF
instance TyAlg (ExprF :&: Pos) where
  tyAlg = tyExprF
instance TyAlg (PrivMechF :&: Pos) where
  tyAlg = tyPrivMechF
instance TyAlg (EffF :&: Pos) where
  tyAlg = tyEffF
instance TyAlg (LambdaF :&: Pos) where
  tyAlg = tyLambdaF
instance TyAlg (SeqF :&: Pos) where
  tyAlg = tySeqF
instance TyAlg (ExtensionF :&: Pos) where
  tyAlg = tyExtensionF

typecheck' :: MonadThrow m
          => Term (WithPos NSFuzziF1) (FuzziM ())
          -> TypeChecker m (FuzziM ())
typecheck' = cata tyAlg

type CheckerMonad = StateT NameState (Either SomeException)

runCheckerMonad :: CheckerMonad a -> NameState -> Either SomeException a
runCheckerMonad act st = flip evalStateT st act

stripMacros :: Cxt m -> M.Map Name Sensitivity
stripMacros = runIdentity . M.traverseMaybeWithKey go
  where go _ (Atomic (ExprInfo s _ _ _)) = return (Just s)
        go _ _ = return Nothing

typecheck :: Term (WithPos NSFuzziF1) (FuzziM ())
          -> M.Map Name Double -- ^initial sensitivity context
          -> Either SomeException (M.Map Name Sensitivity, ProbAnn, TermAnn, Double, Double)
typecheck term initialCxt =
  let initialCxt' = M.map (\s -> Atomic $ ExprInfo (Sens s) D T 0) initialCxt
      typeInfo = runCheckerMonad (runTypeChecker (typecheck' term) initialCxt' >>= expectAtomic (Pos Nothing)) empty
  in do
    ti <- typeInfo
    case ti of
      CmdInfo cxt p t e d -> return (stripMacros cxt, p, t, e, d) 
      _ -> throwTE (Pos Nothing) ExpectingACommand
