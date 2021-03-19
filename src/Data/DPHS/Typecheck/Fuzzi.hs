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

liftSum ''TyAlg

instance TyAlg (EffF :&: Pos) where
  tyAlg = tyAlgEff

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
  deriving (Show, Eq, Ord)

data PositionAndTypeError = PTE {
  _ptePosition :: Pos,
  _pteTypeError :: TypeError
  } deriving (Show, Eq)

instance Exception PositionAndTypeError

throwTE :: MonadThrow m => Pos -> TypeError -> m a
throwTE p e = throwM (PTE p e)

mergeBranchCxt :: Cxt -> Cxt -> Cxt
mergeBranchCxt =
  M.merge M.dropMissing M.dropMissing merge
  where merge = M.zipWithAMatched (\_ s1 s2 -> pure $ max s1 s2)

-- |Typecheck the commands fragment.
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
    Just (asSens -> Sens 0, D, t, 0) -> do
      tyC1 <- unK c1 cxt
      tyC2 <- unK c2 cxt
      case (asCmdInfo tyC1, asCmdInfo tyC2) of
        (Just (postCxt1, p1, t1, eps1, dlt1), Just (postCxt2, p2, t2, eps2, dlt2)) ->
          let cxt' = mergeBranchCxt postCxt1 postCxt2 in
          return $
            atomicCmdInfo cxt'
              (p1 <> p2)
              (t <> t1 <> t2)
              (max eps1 eps2)
              (max dlt1 dlt2)
        (Just _, Nothing) -> throwTE position ExpectingFalseBranchCommand
        (Nothing, _) -> throwTE position ExpectingTrueBranchCommand
    Just (_, P, _, _) ->
      throwTE position BranchConditionProb
    Just (_, D, _, _) ->
      throwTE position BranchConditionSensitive
    Nothing -> throwTE position ExpectingAnExpression
tyAlgEff (While cond c :&: position) = K $ \cxt -> do
  tyCond <- unK cond cxt
  case asExprInfo tyCond of
    Just (isNonSensitive -> True, D, tCond, _) -> do
      tyC <- unK c cxt
      case asCmdInfo tyC of
        Just (postCxt, p, tBody, 0, 0) -> do
          when (cxt /= postCxt) $
            throwTE position CannotFindLoopInvariant
          return $ atomicCmdInfo cxt p (tCond <> tBody) 0 0
        Just (_, _, _, eps, delta) ->
          throwTE position (LoopHasPrivacyCost eps delta)
        Nothing ->
          throwTE position ExpectingLoopBodyCommand
    Just (_, D, _, _) ->
      throwTE position BranchConditionSensitive
    Just (_, P, _, _) ->
      throwTE position BranchConditionProb
    Nothing ->
      throwTE position ExpectingAnExpression

tyAlgExpr :: MonadThrow m => Alg (ExprF :&: Pos) (K (TypeChecker m))
tyAlgExpr (Deref (V x) :&: position) = K $ \cxt -> do
  case M.lookup x cxt of
    Nothing -> throwTE position (OutOfScopeVariable x)
    Just ty -> (return . Atomic) (ExprInfo ty D T 0)
tyAlgExpr (Index checkArr checkIdx :&: position) = K $ \cxt -> do
  arrTy <- unK checkArr cxt
  idxTy <- unK checkIdx cxt
  case ( asExprInfo arrTy
       , asExprInfo idxTy) of
    ( Just (arrSens, arrProb, arrTerm, eps1)
      , Just (idxSens, idxProb, idxTerm, eps2)) -> do
      when (not $ isNonSensitive idxSens) $
        throwTE position SensitiveArrayIndex
      return . Atomic $
        ExprInfo arrSens (arrProb <> idxProb) (arrTerm <> idxTerm) (eps1+eps2)
    _ -> throwTE position ExpectingAnExpression
tyAlgExpr (Resize checkArr checkSize :&: position) = K $ \cxt -> do
  arrTy <- unK checkArr cxt
  sizeTy <- unK checkSize cxt
  case ( asExprInfo arrTy
       , asExprInfo sizeTy) of
    ( Just (arrSens, arrProb, arrTerm, eps1)
      , Just (sizeSens, sizeProb, sizeTerm, eps2)) -> do
      when (not $ isNonSensitive sizeSens) $
        throwTE position SensitiveArraySize
      return . Atomic $
        ExprInfo arrSens (arrProb <> sizeProb) (arrTerm <> sizeTerm) (eps1+eps2)
    _ -> throwTE position ExpectingAnExpression
tyAlgExpr (ArrLit checkInners :&: position) = K $ \cxt -> do
  innerTys <- mapM (\checkTy -> unK checkTy cxt) checkInners
  case traverse asExprInfo innerTys of
    Just innerExprTys ->
      let totalSens = foldMap (\einfo -> einfo ^. _1) innerExprTys
          aggrProbAnn = foldMap (\einfo -> einfo ^. _2) innerExprTys
          aggrTermAnn = foldMap (\einfo -> einfo ^. _3) innerExprTys
          totalEps = getSum $ foldMap (\einfo -> Sum (einfo ^. _4)) innerExprTys
      in return . Atomic $
           ExprInfo totalSens aggrProbAnn aggrTermAnn totalEps
    Nothing -> throwTE position ExpectingAnExpression
