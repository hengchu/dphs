{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
module Data.DPHS.Typecheck.Fuzzi where

--import Debug.Trace
import Control.Monad
import Control.Monad.Catch
import Data.Foldable
import Type.Reflection hiding (App)
import qualified Data.Map.Strict as M

import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Annotation
import Data.Comp.Multi.Derive
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.Term hiding (Cxt)
import Optics

import Data.DPHS.SrcLoc
import Data.DPHS.Algebra
import Data.DPHS.Fuzzi
import Data.DPHS.Syntax

data InternalSens  =
  InternalSensConst Double
  | InternalSensSensitive Double
  deriving (Show, Eq, Ord)

type Sens  = Double
type Eps   = Double
type Delta = Double

approx :: InternalSens -> Sens
approx (InternalSensConst _) = 0
approx (InternalSensSensitive s) = s

sensAdd :: InternalSens -> InternalSens -> InternalSens
sensAdd (InternalSensConst a1) (InternalSensConst a2) = InternalSensConst (a1 + a2)
sensAdd (approx -> s1) (approx -> s2) = InternalSensSensitive (s1 + s2)

sensSub :: InternalSens -> InternalSens -> InternalSens
sensSub (InternalSensConst a1) (InternalSensConst a2) = InternalSensConst (a1 - a2)
sensSub (approx -> s1) (approx -> s2) = InternalSensSensitive (s1 + s2)

-- assume |x1 - x2| <= s
-- 1. if x1 and x2 both <= 0, then
--    |abs x1 - abs x2| = |-x1 - (-x2)| = |x2 - x1| = |x1 - x2| <= s
-- 2. if x1 and x2 both > 0, then
--    |abs x1 - abs x2| = |x1 - x2| <= s
-- 3. if x1 <= 0 and x2 > 0, then
--    |abs x1 - abs x2| = |-x1-x2| = |x1+x2|, this is unbounded
sensAbs :: InternalSens -> InternalSens
sensAbs (InternalSensConst a) = InternalSensConst (abs a)
sensAbs (InternalSensSensitive s)
  | s == 0 = InternalSensSensitive 0
  | otherwise = InternalSensSensitive infinity

sensSignum :: InternalSens -> InternalSens
sensSignum (InternalSensConst a) = InternalSensConst (signum a)
sensSignum (InternalSensSensitive s)
  | s == 0 = InternalSensSensitive 0
  | otherwise = InternalSensSensitive 2.0 -- because signum is either -1, 0, or 1

sensExp :: InternalSens -> InternalSens
sensExp (InternalSensConst k) = InternalSensConst (exp k)
sensExp (approx -> s)
  | s == 0 = InternalSensSensitive 0
  | otherwise = InternalSensSensitive infinity

infinity :: Double
infinity = read "Infinity"

sensMult :: InternalSens -> InternalSens -> InternalSens
sensMult (InternalSensConst a1) (InternalSensConst a2) = InternalSensConst (a1 * a2)
sensMult (InternalSensConst k) (approx -> s)
  | s == infinity = InternalSensSensitive infinity
  | otherwise = InternalSensSensitive (abs k * s)
sensMult (approx -> s) (InternalSensConst k)
  | s == infinity = InternalSensSensitive infinity
  | otherwise = InternalSensSensitive (abs k * s)
sensMult (approx -> s1) (approx -> s2)
  | s1 == 0 && s2 == 0 = InternalSensSensitive 0
  | otherwise = InternalSensSensitive infinity

sensDiv :: InternalSens -> InternalSens -> InternalSens
sensDiv (InternalSensConst a1) (InternalSensConst a2) = InternalSensConst (a1 / a2)
sensDiv (approx -> s) (InternalSensConst k)
  | s == infinity = InternalSensSensitive infinity
  | otherwise = InternalSensSensitive (s / abs k)
sensDiv (approx -> s1) (approx -> s2)
  | s1 == 0 && s2 == 0 = InternalSensSensitive 0
  | otherwise = InternalSensSensitive infinity

sensIDiv :: InternalSens -> InternalSens -> InternalSens
sensIDiv (InternalSensConst a1) (InternalSensConst a2) =
  InternalSensConst (realToFrac @Integer $ round a1 `div` round a2)
sensIDiv (approx -> s) (InternalSensConst k)
  | s == infinity = InternalSensSensitive infinity
  | otherwise = InternalSensSensitive (realToFrac @Integer . ceiling $ s / abs k)
sensIDiv (approx -> s1) (approx -> s2)
  | s1 == 0 && s2 == 0 = InternalSensSensitive 0
  | otherwise = InternalSensSensitive infinity

sensIMod :: InternalSens -> InternalSens -> InternalSens
sensIMod (InternalSensConst a1) (InternalSensConst a2) =
  InternalSensConst (realToFrac @Integer $ round a1 `mod` round a2)
sensIMod (approx -> _) (InternalSensConst k) =
  InternalSensSensitive (abs k-1)
sensIMod (approx -> s1) (approx -> s2)
  | s1 == 0 && s2 == 0 = InternalSensSensitive 0
  | otherwise = InternalSensSensitive infinity

sensBoolBinop :: InternalSens -> InternalSens -> InternalSens
sensBoolBinop (approx -> s1) (approx -> s2)
  | s1 == 0 && s2 == 0 = InternalSensSensitive 0
  | otherwise = InternalSensSensitive infinity

data AnyVariable :: * where
  AnyVariable :: Typeable a => Variable a -> AnyVariable

instance Show AnyVariable where
  show (AnyVariable vb) = show vb

instance Eq AnyVariable where
  (AnyVariable (v1 :: _ a1)) == (AnyVariable (v2 :: _ a2)) =
    case eqTypeRep (typeRep @a1) (typeRep @a2) of
      Just HRefl -> v1 == v2
      Nothing -> False

instance Ord AnyVariable where
  compare (AnyVariable (v1 :: _ a1)) (AnyVariable (v2 :: _ a2)) =
    case eqTypeRep tr1 tr2 of
      Just HRefl -> compare v1 v2
      Nothing -> compare (SomeTypeRep tr1) (SomeTypeRep tr2)
    where tr1 = typeRep @a1
          tr2 = typeRep @a2

type Cxt m = M.Map AnyVariable (Ty m)
type Typechecker m = Cxt m -> m (Cxt m, Ty m, Eps, Delta)

data Ty m =
  AtomicTy {
    tySensitivity :: InternalSens
    }
  | FunTy {
      -- |Typechecking for lambdas are "lazy"---in the sense that the type of a lambda
      -- is not directly representable in the type language itself. Rather, it is
      -- given as a function that produces a type when the argument type is provided.
      -- We need some sort of "grounded" theorem that says, if the type of the term is
      -- atomic, then the produced type will be atomic.
      tyFunType :: Ty m -> Typechecker m
    }

data TypeErrorKind =
  InternalError String
  | UnknownVariable AnyVariable
  | LogNonPositiveConstant Double
  | SqrtNegativeConstant Double
  | LaplaceWidthMustBeConstant
  | BranchOnSensitiveCondition
  | CannotDetermineLoopInvariantContext
  | LoopBodyAddsPrivacyCost
  deriving (Show, Eq, Ord)

data TypeError = TypeError {
  typeErrorKind :: TypeErrorKind,
  typeErrorPosition :: Pos
  } deriving (Show, Eq)

instance Exception TypeError
instance Exception TypeErrorKind

makeFieldLabels ''TypeError

allAtomic :: MonadThrow m => Cxt m -> m (M.Map AnyVariable InternalSens)
allAtomic cxt = traverse go cxt
  where go (AtomicTy sens) = return sens
        go _ = throwM (InternalError "expected typing context to only contain atomic sensitivities")

atomicConst :: Double -> Ty m
atomicConst = AtomicTy . InternalSensConst

atomicSensitive :: Double -> Ty m
atomicSensitive = AtomicTy . InternalSensSensitive

makeFieldLabels ''Ty
makePrisms ''Ty

data CoTerm =
    ExprCoTerm {
      coTermTermination :: Bool
      }
  | StmtCoTerm {
      coTermTermination :: Bool
      }
  deriving (Show, Eq, Ord)

makeFieldLabels ''CoTerm

data AssignForm m =
  IsAssignForm {
    assignFormVariable :: AnyVariable,
    -- |a function that updates the
    -- typing context using the
    -- type of the assignment RHS
    assignFormEffect   :: Cxt m -> Ty m -> m (Cxt m)
  }
  | NotAssignment

makeFieldLabels ''AssignForm
makePrisms ''AssignForm

class SensCheck (h :: (* -> *) -> * -> *) where
  sensCheckAlg :: MonadThrow m => Alg h (K (Typechecker m))

class AssignFormCheck (h :: (* -> *) -> * -> *) where
  assignFormAlg :: MonadThrow m => Alg h (K (AssignForm m))

class TyCheck (h :: (* -> *) -> * -> *) where
  tyCheckAlg :: MonadThrow m => Alg h (K (Typechecker m) :* K (AssignForm m))

liftSum ''SensCheck
liftSum ''AssignFormCheck
liftSum ''TyCheck

instance {-# OVERLAPPABLE #-} AssignFormCheck h where
  assignFormAlg _ = K NotAssignment

instance
  {-# OVERLAPPABLE #-}
  ( SensCheck h
  , AssignFormCheck h
  , HFunctor h
  ) => TyCheck h where
  tyCheckAlg = prodAlg sensCheckAlg assignFormAlg

unwrapOr :: (MonadThrow m, Exception e) => e -> Maybe a -> m a
unwrapOr _ (Just a) = return a
unwrapOr e Nothing  = throwM e

instance SensCheck (LambdaF :&: Pos) where
  sensCheckAlg (Lam x (unK -> checkBody) :&: _pos) =
    K $ \outerCxt ->
    let funTy = review _FunTy $ \argTy innerCxt -> do
          let xvar = AnyVariable x
          let innerCxt' = M.insert xvar argTy innerCxt
          (postCxt, postTy, eps, delta) <- checkBody innerCxt'
          return (M.delete xvar postCxt, postTy, eps, delta)
    in return $ (outerCxt, funTy, 0, 0)
  sensCheckAlg (App (unK -> checkFun) (unK -> checkArg) :&: pos) =
    K $ \cxt -> do
    (postArgCxt, argTy, epsArg, deltaArg) <- checkArg cxt
    (_, funTy, _, _) <- checkFun postArgCxt
    funTc <- preview #funType funTy &
      unwrapOr (TypeError (InternalError "expected function type") pos)
    (postCxt, resultTy, epsApp, deltaApp) <- funTc argTy postArgCxt
    return (postCxt, resultTy, epsArg + epsApp, deltaArg + deltaApp)
  sensCheckAlg (Var x :&: pos) =
    K $ \cxt -> do
    let xvar = AnyVariable x
    xTy <- M.lookup xvar cxt & unwrapOr (TypeError (UnknownVariable xvar) pos)
    return (cxt, xTy, 0, 0)

instance SensCheck (MonadF :&: Pos) where
  sensCheckAlg (Bind (unK -> checkPre) (unK -> checkPost) :&: pos) =
    K $ \preCxt -> do
    (middleCxt, middleTy, epsPre, deltaPre) <- checkPre preCxt
    (_, postFunTy :: Ty _, _, _) <- checkPost middleCxt
    postFunTc <- preview #funType postFunTy &
      unwrapOr (TypeError (InternalError "expected function type") pos)
    (postCxt, postTy, epsPost, deltaPost) <- postFunTc middleTy middleCxt
    return (postCxt, postTy, epsPre + epsPost, deltaPre + deltaPost)
  sensCheckAlg (Ret (unK -> check) :&: _pos) =
    K check

tyCheckBinop :: MonadThrow m
             => (InternalSens -> InternalSens -> InternalSens)
             -> Pos
             -> Typechecker m
             -> Typechecker m
             -> K (Typechecker m) a
tyCheckBinop joinTy pos checkLhs checkRhs = K $ \cxt -> do
  (cxt1, lhsTy, eps1, delta1) <- checkLhs cxt
  (cxt2, rhsTy, eps2, delta2) <- checkRhs cxt1
  lhsSens <- preview #sensitivity lhsTy
               & unwrapOr (TypeError (InternalError "expected atomic sensitivity") pos)
  rhsSens <- preview #sensitivity rhsTy
               & unwrapOr (TypeError (InternalError "expected atomic sensitivity") pos)
  return (cxt2, AtomicTy $ lhsSens `joinTy` rhsSens, eps1+eps2, delta1+delta2)

sensLog :: MonadThrow m => InternalSens -> m InternalSens
sensLog (InternalSensConst k)
  | k <= 0 = throwM (LogNonPositiveConstant k)
  | otherwise = return $ InternalSensConst (log k)
sensLog (approx -> s)
  | s == 0 = return $ InternalSensSensitive 0
  | otherwise = return $ InternalSensSensitive infinity

sensSqrt :: MonadThrow m => InternalSens -> m InternalSens
sensSqrt (InternalSensConst k)
  | k < 0 = throwM (SqrtNegativeConstant k)
  | otherwise = return $ InternalSensConst (sqrt k)
sensSqrt (approx -> s)
  | s == 0 = return $ InternalSensSensitive 0
  | otherwise = return $ InternalSensSensitive infinity

instance SensCheck (ArithF :&: Pos) where
  sensCheckAlg (IntLit k :&: _pos) =
    K $ \cxt -> return (cxt, atomicConst (realToFrac k), 0, 0)
  sensCheckAlg (FracLit k :&: _pos) =
    K $ \cxt -> return (cxt, atomicConst (realToFrac k), 0, 0)
  sensCheckAlg (Add (unK -> checkLhs) (unK -> checkRhs) :&: pos) =
    tyCheckBinop sensAdd pos checkLhs checkRhs
  sensCheckAlg (Sub (unK -> checkLhs) (unK -> checkRhs) :&: pos) =
    tyCheckBinop sensSub pos checkLhs checkRhs
  sensCheckAlg (Abs (unK -> check) :&: pos) =
    K $ \cxt -> do
    (cxt', ty, eps, delta) <- check cxt
    sens <- preview #sensitivity ty
              & unwrapOr (TypeError (InternalError "expected atomic sensitivity") pos)
    return (cxt', AtomicTy $ sensAbs sens, eps, delta)
  sensCheckAlg (Signum (unK -> check) :&: pos) =
    K $ \cxt -> do
    (cxt', ty, eps, delta) <- check cxt
    sens <- preview #sensitivity ty
              & unwrapOr (TypeError (InternalError "expected atomic sensitivity") pos)
    return (cxt', AtomicTy $ sensSignum sens, eps, delta)
  sensCheckAlg (Mult (unK -> checkLhs) (unK -> checkRhs) :&: pos) =
    tyCheckBinop sensMult pos checkLhs checkRhs
  sensCheckAlg (Div (unK -> checkLhs) (unK -> checkRhs) :&: pos) =
    tyCheckBinop sensDiv pos checkLhs checkRhs
  sensCheckAlg (IDiv (unK -> checkLhs) (unK -> checkRhs) :&: pos) =
    tyCheckBinop sensIDiv pos checkLhs checkRhs
  sensCheckAlg (IMod (unK -> checkLhs) (unK -> checkRhs) :&: pos) =
    tyCheckBinop sensIMod pos checkLhs checkRhs
  sensCheckAlg (Exp (unK -> check) :&: pos) =
    K $ \cxt -> do
    (cxt', ty, eps, delta) <- check cxt
    sens <- preview #sensitivity ty
              & unwrapOr (TypeError (InternalError "expected atomic sensitivity") pos)
    return (cxt', AtomicTy $ sensExp sens, eps, delta)
  sensCheckAlg (Log (unK -> check) :&: pos) =
    K $ \cxt -> do
    (cxt', ty, eps, delta) <- check cxt
    sens <- preview #sensitivity ty
              & unwrapOr (TypeError (InternalError "expected atomic sensitivity") pos)
    newSens <- sensLog sens
    return (cxt', AtomicTy newSens, eps, delta)
  sensCheckAlg (Sqrt (unK -> check) :&: pos) =
    K $ \cxt -> do
    (cxt', ty, eps, delta) <- check cxt
    sens <- preview #sensitivity ty
              & unwrapOr (TypeError (InternalError "expected atomic sensitivity") pos)
    newSens <- sensSqrt sens
    return (cxt', AtomicTy newSens, eps, delta)

instance SensCheck (CompareF :&: Pos) where
  sensCheckAlg (IsEq (unK -> checkLhs) (unK -> checkRhs) :&: pos) =
    tyCheckBinop sensBoolBinop pos checkLhs checkRhs
  sensCheckAlg (IsNeq (unK -> checkLhs) (unK -> checkRhs) :&: pos) =
    tyCheckBinop sensBoolBinop pos checkLhs checkRhs
  sensCheckAlg (IsLt (unK -> checkLhs) (unK -> checkRhs) :&: pos) =
    tyCheckBinop sensBoolBinop pos checkLhs checkRhs
  sensCheckAlg (IsLe (unK -> checkLhs) (unK -> checkRhs) :&: pos) =
    tyCheckBinop sensBoolBinop pos checkLhs checkRhs
  sensCheckAlg (IsGt (unK -> checkLhs) (unK -> checkRhs) :&: pos) =
    tyCheckBinop sensBoolBinop pos checkLhs checkRhs
  sensCheckAlg (IsGe (unK -> checkLhs) (unK -> checkRhs) :&: pos) =
    tyCheckBinop sensBoolBinop pos checkLhs checkRhs
  sensCheckAlg (And (unK -> checkLhs) (unK -> checkRhs) :&: pos) =
    tyCheckBinop sensBoolBinop pos checkLhs checkRhs
  sensCheckAlg (Or (unK -> checkLhs) (unK -> checkRhs) :&: pos) =
    tyCheckBinop sensBoolBinop pos checkLhs checkRhs
  sensCheckAlg (Neg (unK -> check) :&: _pos) = K check

instance SensCheck (ExprF :&: Pos) where
  sensCheckAlg (Deref x :&: pos) =
    K $ \cxt -> do
      xTy <- M.lookup xvar cxt & unwrapOr (TypeError (UnknownVariable xvar) pos)
      return (cxt, xTy, 0, 0)
    where xvar = AnyVariable x
  sensCheckAlg (Index (unK -> checkArr) (unK -> checkIdx) :&: pos) =
    K $ \cxt -> do
      (cxt1, arrTy, eps1, delta1) <- checkArr cxt
      (cxt2, idxTy, eps2, delta2) <- checkIdx cxt1
      idxSens <-
        preview #sensitivity idxTy
          & unwrapOr (TypeError (InternalError "expecting atomic sensitivity") pos)
      case approx idxSens of
        0 -> return (cxt2,
                     arrTy,
                     eps1+eps2,
                     delta1+delta2)
        _ -> return (cxt2,
                     AtomicTy $ InternalSensSensitive infinity,
                     eps1+eps2,
                     delta1+delta2)
  sensCheckAlg (ArrLit (map unK -> checkElems) :&: pos) =
    K $ \cxt -> do
      (cxt', elemTys, eps, delta) <- foldrM go (cxt, [], 0, 0) checkElems
      elemsSens <-
        traverse
          (unwrapOr (TypeError (InternalError "expected atomic sensitivity") pos)
           . preview #sensitivity)
          elemTys
      return $ (cxt', AtomicTy $ foldr sensAdd (InternalSensSensitive 0) elemsSens, eps, delta)
    where go checkFun (lastCxt, tyAcc, epsAcc, deltaAcc) = do
            (cxt', ty, eps, delta) <- checkFun lastCxt
            return (cxt', ty:tyAcc, eps+epsAcc, delta+deltaAcc)

instance {-# OVERLAPPING #-} AssignFormCheck (ExprF :&: Pos) where
  assignFormAlg (Deref x :&: _pos) =
    let xvar = AnyVariable x in
      K $ IsAssignForm xvar (\cxt ty -> return $ M.insert xvar ty cxt)
  assignFormAlg (Index (unK -> arr) _ :&: pos) =
    case arr of
      IsAssignForm var _ -> K $ IsAssignForm var (newEff var)
      NotAssignment -> K NotAssignment
    where newEff var cxt ty =
            case M.lookup var cxt of
              Nothing -> return $ M.insert var ty cxt
              Just ty' -> do
                sens <- preview #sensitivity ty
                          & unwrapOr (TypeError (InternalError "expected atomic sensitivity") pos)
                sens' <- preview #sensitivity ty'
                          & unwrapOr (TypeError (InternalError "expected atomic sensitivity") pos)
                return $ M.insert var (AtomicTy (sens `sensAdd` sens')) cxt
  assignFormAlg _ = K NotAssignment

instance SensCheck (PrivMechF :&: Pos) where
  sensCheckAlg (Laplace (unK -> checkWidth) (unK -> checkCenter) :&: pos) =
    K $ \cxt -> do
    (cxt1, widthTy, eps1, delta1) <- checkWidth cxt
    (cxt2, centerTy, eps2, delta2) <- checkCenter cxt1
    widthSens <- preview #sensitivity widthTy
                   & unwrapOr (TypeError (InternalError "expecting an atomic sensitivity") pos)
    centerSens <- preview #sensitivity centerTy
                   & unwrapOr (TypeError (InternalError "expecting an atomic sensitivity") pos)
    case {-traceShow widthSens $ -}widthSens of
      InternalSensConst width ->
        return (cxt2,
                AtomicTy $ InternalSensSensitive 0,
                approx centerSens / width + eps1 + eps2,
                delta1 + delta2)
      _ -> throwM (TypeError LaplaceWidthMustBeConstant pos)

instance SensCheck (EffF :&: Pos) where
  sensCheckAlg (Assign _ _ :&: pos) =
    K $ \_ -> throwM (TypeError (InternalError "this branch should never run") pos)
  sensCheckAlg (Branch (unK -> checkCond) (unK -> checkTrue) (unK -> checkFalse) :&: pos) =
    K $ \cxt -> do
    (cxt1, condTy, epsCond,  deltaCond)  <- checkCond  cxt
    (cxt2, _,      epsTrue,  deltaTrue)  <- checkTrue  cxt1
    (cxt3, _,      epsFalse, deltaFalse) <- checkFalse cxt2
    condSens <- preview #sensitivity condTy
                  & unwrapOr (TypeError (InternalError "expected atomic sensitivity") pos)
    case approx condSens of
      0 -> do
        cxt' <- pointwiseMax cxt2 cxt3
        return (cxt',
                AtomicTy $ InternalSensSensitive 0,
                epsCond + max epsTrue epsFalse,
                deltaCond + max deltaTrue deltaFalse)
      _ -> throwM (TypeError BranchOnSensitiveCondition pos)
    where
      -- TODO: impl this
      pointwiseMax :: MonadThrow m => Cxt m -> Cxt m -> m (Cxt m)
      pointwiseMax cxt1 _cxt2 = return cxt1
  sensCheckAlg (While (unK -> checkCond) (unK -> checkBody) :&: pos) =
    K $ \cxt -> do
    (cxt1, condTy, epsCond, deltaCond) <- checkCond cxt
    (cxt2, _,      epsBody, deltaBody) <- checkBody cxt1
    isInvariant <- checkInvariance cxt1 cxt2
    condSens <- preview #sensitivity condTy
                  & unwrapOr (TypeError (InternalError "expected atomic sensitivity") pos)
    when (approx condSens /= 0) $
      throwM (TypeError BranchOnSensitiveCondition pos)
    when (not isInvariant) $
      throwM (TypeError CannotDetermineLoopInvariantContext pos)
    case (epsBody, deltaBody) of
      (0, 0) -> return (cxt2, AtomicTy $ InternalSensSensitive 0, epsCond, deltaCond)
      _      -> throwM (TypeError LoopBodyAddsPrivacyCost pos)
    where
      -- TODO: implement this
      checkInvariance :: MonadThrow m => Cxt m -> Cxt m -> m Bool
      checkInvariance _ _ = return True

instance SensCheck (ExtensionF :&: Pos) where

instance TyCheck (ExprF :&: Pos) where
  tyCheckAlg (Index arr idx :&: pos) =
    Prod sens assn
    where
      Prod (unK -> checkSensArr) (unK -> assignArr) = arr
      Prod (unK -> checkSensIdx) (unK -> assignIdx) = idx
      sens = sensCheckAlg $ Index (K checkSensArr) (K checkSensIdx) :&: pos
      assn = K $
        case unK . assignFormAlg $ Index (K assignArr) (K assignIdx) of
          NotAssignment -> NotAssignment
          IsAssignForm assnVar eff -> IsAssignForm assnVar $ \cxt ty -> do
            (_, idxTy, _, _) <- checkSensIdx cxt
            idxSens <- preview #sensitivity idxTy
                         & unwrapOr (InternalError "expected atomic sensitivity")
            case approx idxSens of
              0 -> eff cxt ty
              _ -> return $ M.insert assnVar (AtomicTy $ InternalSensSensitive infinity) cxt

  tyCheckAlg a = prodAlg sensCheckAlg assignFormAlg a

instance TyCheck (EffF :&: Pos) where
  tyCheckAlg (Assign lhs rhs :&: pos) =
    Prod sens assn
    where
      Prod _                     (unK -> assignLhs) = lhs
      Prod (unK -> checkSensRhs) (unK -> assignRhs) = rhs
      sens = K $ \cxt -> do
        (cxt', rhsTy, eps, delta) <- checkSensRhs cxt
        assignEff <- preview #effect assignLhs
                       & unwrapOr (TypeError (InternalError "expected assignment form") pos)
        updatedCxt' <- assignEff cxt' rhsTy
        return (updatedCxt', AtomicTy $ InternalSensSensitive 0, eps, delta)
      assn = assignFormAlg $ Assign (K assignLhs) (K assignRhs)

  tyCheckAlg a = prodAlg sensCheckAlg assignFormAlg a

-- |The top-level typechecker for a 'Fuzzi' program.
tyCheck :: MonadThrow m => Term (WithPos NFuzziF) a -> Typechecker m
tyCheck = unK . prj1 . cata tyCheckAlg
