{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
module Data.DPHS.Typecheck.Fuzzi where

import Type.Reflection hiding (App)
import qualified Data.Map.Strict as M
import Data.Foldable
import Control.Monad.Catch

import Optics
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Derive
import Data.Comp.Multi.HFunctor

import Data.DPHS.Syntax
import Data.DPHS.Fuzzi

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
type Typechecker m = Cxt m -> m (Cxt m, Ty m)

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

class TyCheck (h :: (* -> *) -> * -> *) where
  tyCheckAlg :: MonadThrow m => Alg h (K (Typechecker m))

liftSum ''TyCheck

data TypeError =
  InternalError String
  | UnknownVariable AnyVariable
  | LogNonPositiveConstant Double
  | SqrtNegativeConstant Double
  deriving (Show, Eq, Ord)

instance Exception TypeError

unwrapOr :: (MonadThrow m, Exception e) => e -> Maybe a -> m a
unwrapOr _ (Just a) = return a
unwrapOr e Nothing  = throwM e

instance TyCheck LambdaF where
  tyCheckAlg (Lam x (unK -> checkBody)) =
    K $ \outerCxt ->
    let funTy = review _FunTy $ \argTy innerCxt -> do
          let xvar = AnyVariable x
          let innerCxt' = M.insert xvar argTy innerCxt
          (postCxt, postTy) <- checkBody innerCxt'
          return (M.delete xvar postCxt, postTy)
    in return $ (outerCxt, funTy)
  tyCheckAlg (App (unK -> checkFun) (unK -> checkArg)) =
    K $ \cxt -> do
    (postArgCxt, argTy) <- checkArg cxt
    (_, funTy) <- checkFun postArgCxt
    funTc <- preview #funType funTy &
      unwrapOr (InternalError "expected function type")
    funTc argTy postArgCxt
  tyCheckAlg (Var x) =
    K $ \cxt -> do
    let xvar = AnyVariable x
    xTy <- M.lookup xvar cxt & unwrapOr (UnknownVariable xvar)
    return (cxt, xTy)

instance TyCheck MonadF where
  tyCheckAlg (Bind (unK -> checkPre) (unK -> checkPost)) =
    K $ \preCxt -> do
    (middleCxt, middleTy) <- checkPre preCxt
    (_, postFunTy :: Ty _) <- checkPost middleCxt
    postFunTc <- preview #funType postFunTy &
      unwrapOr (InternalError "expected function type")
    postFunTc middleTy middleCxt
  tyCheckAlg (Ret (unK -> check)) =
    K check

tyCheckBinop :: MonadThrow m
             => (InternalSens -> InternalSens -> InternalSens)
             -> Typechecker m
             -> Typechecker m
             -> K (Typechecker m) a
tyCheckBinop join checkLhs checkRhs = K $ \cxt -> do
  (cxt1, lhsTy) <- checkLhs cxt
  (cxt2, rhsTy) <- checkRhs cxt1
  lhsSens <- preview #sensitivity lhsTy
               & unwrapOr (InternalError "expected atomic sensitivity")
  rhsSens <- preview #sensitivity rhsTy
               & unwrapOr (InternalError "expected atomic sensitivity")
  return (cxt2, AtomicTy $ lhsSens `join` rhsSens)

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

instance TyCheck ArithF where
  tyCheckAlg (IntLit k) = K $ \cxt -> return (cxt, atomicConst (realToFrac k))
  tyCheckAlg (FracLit k) = K $ \cxt -> return (cxt, atomicConst (realToFrac k))
  tyCheckAlg (Add (unK -> checkLhs) (unK -> checkRhs)) =
    tyCheckBinop sensAdd checkLhs checkRhs
  tyCheckAlg (Sub (unK -> checkLhs) (unK -> checkRhs)) =
    tyCheckBinop sensSub checkLhs checkRhs
  tyCheckAlg (Abs (unK -> check)) =
    K $ \cxt -> do
    (cxt', ty) <- check cxt
    sens <- preview #sensitivity ty
              & unwrapOr (InternalError "expected atomic sensitivity")
    return (cxt', AtomicTy $ sensAbs sens)
  tyCheckAlg (Signum (unK -> check)) =
    K $ \cxt -> do
    (cxt', ty) <- check cxt
    sens <- preview #sensitivity ty
              & unwrapOr (InternalError "expected atomic sensitivity")
    return (cxt', AtomicTy $ sensSignum sens)
  tyCheckAlg (Mult (unK -> checkLhs) (unK -> checkRhs)) =
    tyCheckBinop sensMult checkLhs checkRhs
  tyCheckAlg (Div (unK -> checkLhs) (unK -> checkRhs)) =
    tyCheckBinop sensDiv checkLhs checkRhs
  tyCheckAlg (IDiv (unK -> checkLhs) (unK -> checkRhs)) =
    tyCheckBinop sensIDiv checkLhs checkRhs
  tyCheckAlg (IMod (unK -> checkLhs) (unK -> checkRhs)) =
    tyCheckBinop sensIMod checkLhs checkRhs
  tyCheckAlg (Exp (unK -> check)) =
    K $ \cxt -> do
    (cxt', ty) <- check cxt
    sens <- preview #sensitivity ty
              & unwrapOr (InternalError "expected atomic sensitivity")
    return (cxt', AtomicTy $ sensExp sens)
  tyCheckAlg (Log (unK -> check)) =
    K $ \cxt -> do
    (cxt', ty) <- check cxt
    sens <- preview #sensitivity ty
              & unwrapOr (InternalError "expected atomic sensitivity")
    newSens <- sensLog sens
    return (cxt', AtomicTy newSens)
  tyCheckAlg (Sqrt (unK -> check)) =
    K $ \cxt -> do
    (cxt', ty) <- check cxt
    sens <- preview #sensitivity ty
              & unwrapOr (InternalError "expected atomic sensitivity")
    newSens <- sensSqrt sens
    return (cxt', AtomicTy newSens)

instance TyCheck CompareF where
  tyCheckAlg (IsEq (unK -> checkLhs) (unK -> checkRhs)) =
    tyCheckBinop sensBoolBinop checkLhs checkRhs
  tyCheckAlg (IsNeq (unK -> checkLhs) (unK -> checkRhs)) =
    tyCheckBinop sensBoolBinop checkLhs checkRhs
  tyCheckAlg (IsLt (unK -> checkLhs) (unK -> checkRhs)) =
    tyCheckBinop sensBoolBinop checkLhs checkRhs
  tyCheckAlg (IsLe (unK -> checkLhs) (unK -> checkRhs)) =
    tyCheckBinop sensBoolBinop checkLhs checkRhs
  tyCheckAlg (IsGt (unK -> checkLhs) (unK -> checkRhs)) =
    tyCheckBinop sensBoolBinop checkLhs checkRhs
  tyCheckAlg (IsGe (unK -> checkLhs) (unK -> checkRhs)) =
    tyCheckBinop sensBoolBinop checkLhs checkRhs
  tyCheckAlg (And (unK -> checkLhs) (unK -> checkRhs)) =
    tyCheckBinop sensBoolBinop checkLhs checkRhs
  tyCheckAlg (Or (unK -> checkLhs) (unK -> checkRhs)) =
    tyCheckBinop sensBoolBinop checkLhs checkRhs
  tyCheckAlg (Neg (unK -> check)) = K check

instance TyCheck ExprF where
  tyCheckAlg (Deref x) =
    K $ \cxt -> do
      xTy <- M.lookup xvar cxt & unwrapOr (UnknownVariable xvar)
      return (cxt, xTy)
    where xvar = AnyVariable x
  tyCheckAlg (Index (unK -> checkArr) (unK -> checkIdx)) =
    K $ \cxt -> do
      (cxt1, arrTy) <- checkArr cxt
      (cxt2, idxTy) <- checkIdx cxt1
      idxSens <- preview #sensitivity idxTy
                   & unwrapOr (InternalError "expecting atomic sensitivity")
      case approx idxSens of
        0 -> return (cxt2, arrTy)
        _ -> return (cxt2, AtomicTy $ InternalSensSensitive infinity)
  tyCheckAlg (ArrLit (map unK -> checkElems)) =
    K $ \cxt -> do
      (cxt', elemTys) <- foldrM go (cxt, []) checkElems
      elemsSens <- traverse (unwrapOr (InternalError "expected atomic sensitivity") . preview #sensitivity) elemTys
      return $ (cxt', AtomicTy $ foldr sensAdd (InternalSensSensitive 0) elemsSens)
    where go checkFun (lastCxt, tyAcc) = do
            (cxt', ty) <- checkFun lastCxt
            return (cxt', ty:tyAcc)

instance TyCheck PrivMechF where
  tyCheckAlg (Laplace (unK -> checkWidth) (unK -> checkCenter)) =
    undefined
