{-# LANGUAGE CPP #-}

module Data.DPHS.SEval where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Data.Text (pack)
import Optics
import Prelude hiding (iterate)
import Text.Printf
import qualified Data.DList as DL
import qualified Data.Map.Strict as M
import qualified Data.Vector as V
import qualified Streamly as S
import qualified Streamly.Prelude as S

import Type.Reflection

import Data.DPHS.DPCheck
import Data.DPHS.Logging
import Data.DPHS.Name
import Data.DPHS.SolverZ3
import Data.DPHS.SrcLoc
import Data.DPHS.Symbolic
import Data.DPHS.Syntax
import qualified Data.DPHS.StreamUtil as SU

import Data.Comp.Multi

data Step a where
  Stepped :: a -> Step a
  PendingBranch :: SBool -> (Bool -> a) -> Step a
  PendingNoise  :: SReal -> Double -> (SReal -> a) -> Step a
  Normal :: Step a

mapStep :: (a -> b) -> Step a -> Step b
mapStep f (Stepped a)                   = Stepped (f a)
mapStep f (PendingBranch scond k)       = PendingBranch scond (f . k)
mapStep f (PendingNoise center width k) = PendingNoise center width (f . k)
mapStep _ Normal                        = Normal

type Carrier = WithPos DPCheckF

#define DEF_BRANCH _ -> error $ "step: Normal is only returned on normalized terms " ++ show pos

-- |'step' is not structurally recursive, so we do direct definition
-- by projection and pattern matching.
step :: forall i. Cxt Hole Carrier I i -> Step (Cxt Hole Carrier I i)
step (Hole (I _)) = Normal
-- All EffF cases.
step (project @(EffF :&: Pos) -> Just (Branch (cond :: _ bool) t f :&: pos)) =
  case typeCase of
    Left HRefl ->
      case step cond of
        Normal ->
          case cond of
            Hole (I vcond) -> PendingBranch vcond (\cond -> if cond then t else f)
            DEF_BRANCH
        other -> mapStep (\cond -> iABranch pos cond t f) other
    Right HRefl ->
      case step cond of
        Normal ->
          case cond of
            Hole (I vcond) -> if vcond then step t else step f
            DEF_BRANCH
        other -> mapStep (\cond -> iABranch pos cond t f) other
  where
    typeCase :: Either (bool :~~: SBool) (bool :~~: Bool)
    typeCase =
      case eqTypeRep (typeRep @bool) (typeRep @SBool) of
        Just HRefl -> Left HRefl
        Nothing ->
          case eqTypeRep (typeRep @bool) (typeRep @Bool) of
            Just HRefl -> Right HRefl
            Nothing -> error "step: expect branch condition to be either Bool or SBool"
step (project @(EffF :&: Pos) -> Just (Laplace center width :&: pos)) =
  case eqTypeRep (typeRep @i) (typeRep @(SymM SReal)) of
    Just HRefl ->
      case step center of
        Normal ->
          case center of
            Hole (I symCenter) ->
              PendingNoise symCenter width (\noise -> iARet pos (Hole (I noise)))
            DEF_BRANCH
        other -> mapStep (\center -> iALaplace pos center width) other
    Nothing -> error "step: expecting SymM monad for symbolic execution"

-- All XLambdaF cases.
step (project @(XLambdaF :&: Pos) -> Just (XLam _f :&: _pos)) = Normal
step (project @(XLambdaF :&: Pos) -> Just (XApp f arg :&: pos)) =
  case (f', arg') of
    (Normal, Normal) ->
      case project @(XLambdaF :&: Pos) f of
        Just (XLam fun :&: _funPos) -> Stepped (fun arg)
        DEF_BRANCH
    (Normal, otherArg) ->
      mapStep (\arg -> inject $ XApp f arg :&: pos) otherArg
    (otherF, _       ) ->
      mapStep (\f -> inject $ XApp f arg :&: pos) otherF
  where f' = step f
        arg' = step arg
step (project @(XLambdaF :&: Pos) -> Just (XVar v :&: pos)) =
  error $ "step: out-of-scope variable " ++ show v ++ " at " ++ show pos

-- All MonadF cases.
step (project @(MonadF :&: Pos) -> Just (Bind m f :&: pos)) =
  case (m', f') of
    (Normal, Normal) ->
      case ( project @(MonadF :&: Pos) m
           , project @(XLambdaF :&: Pos) f
           ) of
        (Just (Ret v :&: _vPos), Just (XLam cont :&: _contPos)) -> Stepped (cont v)
        DEF_BRANCH
    (otherM, Normal) ->
      mapStep (\m -> iABind pos m f) otherM
    (_,      otherF) ->
      mapStep (\cont -> iABind pos m cont) otherF
  where m' = step m
        f' = step f
step (project @(MonadF :&: Pos) -> Just (Ret v :&: pos)) =
  case step v of
    Normal -> Normal
    other -> mapStep (iARet pos) other

-- All CompareF cases.
step (project @(CompareF :&: Pos) -> Just (IsEq lhs rhs :&: pos)) =
  case (lhs', rhs') of
    (Normal, Normal) ->
      case (lhs, rhs) of
        (Hole (I vlhs), Hole (I vrhs)) -> Stepped (Hole (I (vlhs .== vrhs)))
        DEF_BRANCH
    (Normal, rhs2) -> mapStep (\rhs -> iAIsEq pos lhs rhs) rhs2
    (lhs2, _) -> mapStep (\lhs -> iAIsEq pos lhs rhs) lhs2
  where lhs' = step lhs
        rhs' = step rhs
step (project @(CompareF :&: Pos) -> Just (IsNeq lhs rhs :&: pos)) =
  case (lhs', rhs') of
    (Normal, Normal) ->
      case (lhs, rhs) of
        (Hole (I vlhs), Hole (I vrhs)) -> Stepped (Hole (I (vlhs ./= vrhs)))
        DEF_BRANCH
    (Normal, rhs2) -> mapStep (\rhs -> iAIsNeq pos lhs rhs) rhs2
    (lhs2, _) -> mapStep (\lhs -> iAIsNeq pos lhs rhs) lhs2
  where lhs' = step lhs
        rhs' = step rhs
step (project @(CompareF :&: Pos) -> Just (IsLt lhs rhs :&: pos)) =
  case (lhs', rhs') of
    (Normal, Normal) ->
      case (lhs, rhs) of
        (Hole (I vlhs), Hole (I vrhs)) -> Stepped (Hole (I (vlhs .< vrhs)))
        DEF_BRANCH
    (Normal, rhs2) -> mapStep (\rhs -> iAIsLt pos lhs rhs) rhs2
    (lhs2, _) -> mapStep (\lhs -> iAIsLt pos lhs rhs) lhs2
  where lhs' = step lhs
        rhs' = step rhs
step (project @(CompareF :&: Pos) -> Just (IsLe lhs rhs :&: pos)) =
  case (lhs', rhs') of
    (Normal, Normal) ->
      case (lhs, rhs) of
        (Hole (I vlhs), Hole (I vrhs)) -> Stepped (Hole (I (vlhs .<= vrhs)))
        DEF_BRANCH
    (Normal, rhs2) -> mapStep (\rhs -> iAIsLe pos lhs rhs) rhs2
    (lhs2, _) -> mapStep (\lhs -> iAIsLe pos lhs rhs) lhs2
  where lhs' = step lhs
        rhs' = step rhs
step (project @(CompareF :&: Pos) -> Just (IsGt lhs rhs :&: pos)) =
  case (lhs', rhs') of
    (Normal, Normal) ->
      case (lhs, rhs) of
        (Hole (I vlhs), Hole (I vrhs)) -> Stepped (Hole (I (vlhs .> vrhs)))
        DEF_BRANCH
    (Normal, rhs2) -> mapStep (\rhs -> iAIsGt pos lhs rhs) rhs2
    (lhs2, _) -> mapStep (\lhs -> iAIsGt pos lhs rhs) lhs2
  where lhs' = step lhs
        rhs' = step rhs
step (project @(CompareF :&: Pos) -> Just (IsGe lhs rhs :&: pos)) =
  case (lhs', rhs') of
    (Normal, Normal) ->
      case (lhs, rhs) of
        (Hole (I vlhs), Hole (I vrhs)) -> Stepped (Hole (I (vlhs .>= vrhs)))
        DEF_BRANCH
    (Normal, rhs2) -> mapStep (\rhs -> iAIsGe pos lhs rhs) rhs2
    (lhs2, _) -> mapStep (\lhs -> iAIsGe pos lhs rhs) lhs2
  where lhs' = step lhs
        rhs' = step rhs
step (project @(CompareF :&: Pos) -> Just (Neg term :&: pos)) =
  case term' of
    Normal ->
      case term of
        Hole (I value) -> Stepped (Hole (I (neg value)))
        DEF_BRANCH
    other -> mapStep (\term -> iANeg pos term) other
  where term' = step term
step (project @(CompareF :&: Pos) -> Just (And lhs rhs :&: pos)) =
  case (lhs', rhs') of
    (Normal, Normal) ->
      case (lhs, rhs) of
        (Hole (I vlhs), Hole (I vrhs)) -> Stepped (Hole (I (vlhs .&& vrhs)))
        DEF_BRANCH
    (Normal, rhs2) -> mapStep (\rhs -> iAAnd pos lhs rhs) rhs2
    (lhs2, _) -> mapStep (\lhs -> iAAnd pos lhs rhs) lhs2
  where lhs' = step lhs
        rhs' = step rhs
step (project @(CompareF :&: Pos) -> Just (Or lhs rhs :&: pos)) =
  case (lhs', rhs') of
    (Normal, Normal) ->
      case (lhs, rhs) of
        (Hole (I vlhs), Hole (I vrhs)) -> Stepped (Hole (I (vlhs .|| vrhs)))
        DEF_BRANCH
    (Normal, rhs2) -> mapStep (\rhs -> iAOr pos lhs rhs) rhs2
    (lhs2, _) -> mapStep (\lhs -> iAOr pos lhs rhs) lhs2
  where lhs' = step lhs
        rhs' = step rhs
step (project @(CompareF :&: Pos) -> Just (CTrue :&: _pos)) = Stepped (Hole (I true))
step (project @(CompareF :&: Pos) -> Just (CFalse :&: _pos)) = Stepped (Hole (I false))

-- All ArithF cases.
step (project @(ArithF :&: Pos) -> Just (IntLit value :&: _pos)) =
  Stepped (Hole (I (fromIntegral value)))
step (project @(ArithF :&: Pos) -> Just (FracLit value :&: _pos)) =
  Stepped (Hole (I (realToFrac value)))
step (project @(ArithF :&: Pos) -> Just (Add lhs rhs :&: pos)) =
  case (lhs', rhs') of
    (Normal, Normal) ->
      case (lhs, rhs) of
        (Hole (I vlhs), Hole (I vrhs)) -> Stepped (Hole (I (vlhs + vrhs)))
        DEF_BRANCH
    (Normal, rhs2) -> mapStep (\rhs -> iAAdd pos lhs rhs) rhs2
    (lhs2, _) -> mapStep (\lhs -> iAAdd pos lhs rhs) lhs2
  where lhs' = step lhs
        rhs' = step rhs
step (project @(ArithF :&: Pos) -> Just (Sub lhs rhs :&: pos)) =
  case (lhs', rhs') of
    (Normal, Normal) ->
      case (lhs, rhs) of
        (Hole (I vlhs), Hole (I vrhs)) -> Stepped (Hole (I (vlhs - vrhs)))
        DEF_BRANCH
    (Normal, rhs2) -> mapStep (\rhs -> iASub pos lhs rhs) rhs2
    (lhs2, _) -> mapStep (\lhs -> iASub pos lhs rhs) lhs2
  where lhs' = step lhs
        rhs' = step rhs
step (project @(ArithF :&: Pos) -> Just (Abs term :&: pos)) =
  case term' of
    Normal ->
      case term of
        Hole (I value) -> Stepped (Hole (I (abs value)))
        DEF_BRANCH
    other -> mapStep (\term -> iAAbs pos term) other
  where term' = step term
step (project @(ArithF :&: Pos) -> Just (Signum term :&: pos)) =
  case term' of
    Normal ->
      case term of
        Hole (I value) -> Stepped (Hole (I (signum value)))
        DEF_BRANCH
    other -> mapStep (\term -> iASignum pos term) other
  where term' = step term
step (project @(ArithF :&: Pos) -> Just (Mult lhs rhs :&: pos)) =
  case (lhs', rhs') of
    (Normal, Normal) ->
      case (lhs, rhs) of
        (Hole (I vlhs), Hole (I vrhs)) -> Stepped (Hole (I (vlhs * vrhs)))
        DEF_BRANCH
    (Normal, rhs2) -> mapStep (\rhs -> iAMult pos lhs rhs) rhs2
    (lhs2, _) -> mapStep (\lhs -> iAMult pos lhs rhs) lhs2
  where lhs' = step lhs
        rhs' = step rhs
step (project @(ArithF :&: Pos) -> Just (Div lhs rhs :&: pos)) =
  case (lhs', rhs') of
    (Normal, Normal) ->
      case (lhs, rhs) of
        (Hole (I vlhs), Hole (I vrhs)) -> Stepped (Hole (I (vlhs / vrhs)))
        DEF_BRANCH
    (Normal, rhs2) -> mapStep (\rhs -> iADiv pos lhs rhs) rhs2
    (lhs2, _) -> mapStep (\lhs -> iADiv pos lhs rhs) lhs2
  where lhs' = step lhs
        rhs' = step rhs
step (project @(ArithF :&: Pos) -> Just (IDiv lhs rhs :&: pos)) =
  case (lhs', rhs') of
    (Normal, Normal) ->
      case (lhs, rhs) of
        (Hole (I vlhs), Hole (I vrhs)) -> Stepped (Hole (I (vlhs `idiv` vrhs)))
        DEF_BRANCH
    (Normal, rhs2) -> mapStep (\rhs -> iAIDiv pos lhs rhs) rhs2
    (lhs2, _) -> mapStep (\lhs -> iAIDiv pos lhs rhs) lhs2
  where lhs' = step lhs
        rhs' = step rhs
step (project @(ArithF :&: Pos) -> Just (IMod lhs rhs :&: pos)) =
  case (lhs', rhs') of
    (Normal, Normal) ->
      case (lhs, rhs) of
        (Hole (I vlhs), Hole (I vrhs)) -> Stepped (Hole (I (vlhs `imod` vrhs)))
        DEF_BRANCH
    (Normal, rhs2) -> mapStep (\rhs -> iAIMod pos lhs rhs) rhs2
    (lhs2, _) -> mapStep (\lhs -> iAIMod pos lhs rhs) lhs2
  where lhs' = step lhs
        rhs' = step rhs
step (project @(ArithF :&: Pos) -> Just (Exp term :&: pos)) =
  case term' of
    Normal ->
      case term of
        Hole (I value) -> Stepped (Hole (I (exp value)))
        DEF_BRANCH
    other -> mapStep (\term -> iAExp pos term) other
  where term' = step term
step (project @(ArithF :&: Pos) -> Just (Log term :&: pos)) =
  case term' of
    Normal ->
      case term of
        Hole (I value) -> Stepped (Hole (I (log value)))
        DEF_BRANCH
    other -> mapStep (\term -> iALog pos term) other
  where term' = step term
step (project @(ArithF :&: Pos) -> Just (Sqrt term :&: pos)) =
  case term' of
    Normal ->
      case term of
        Hole (I value) -> Stepped (Hole (I (sqrt value)))
        DEF_BRANCH
    other -> mapStep (\term -> iASqrt pos term) other
  where term' = step term

-- All ListF cases.
step (project @(ListF :&: Pos) -> Just (Nil :&: _pos)) = Stepped (Hole (I DL.empty))
step (project @(ListF :&: Pos) -> Just (Cons hd tl :&: pos)) =
  case (hd', tl') of
    (Normal, Normal) ->
      case (hd, tl) of
        (Hole (I vhd), Hole (I vtl)) -> Stepped (Hole (I (DL.cons vhd vtl)))
        DEF_BRANCH
    (Normal, _) -> mapStep (\tl -> iACons pos hd tl) tl'
    _ -> mapStep (\hd -> iACons pos hd tl) hd'
  where hd' = step hd
        tl' = step tl
step (project @(ListF :&: Pos) -> Just (Snoc hd tl :&: pos)) =
  case (hd', tl') of
    (Normal, Normal) ->
      case (hd, tl) of
        (Hole (I vhd), Hole (I vtl)) -> Stepped (Hole (I (DL.snoc vhd vtl)))
        DEF_BRANCH
    (Normal, _) -> mapStep (\tl -> iASnoc pos hd tl) tl'
    _ -> mapStep (\hd -> iASnoc pos hd tl) hd'
  where hd' = step hd
        tl' = step tl

-- All MaybeF cases.
step (project @(MaybeF :&: Pos) -> Just (Nothing_ :&: _pos)) = Stepped (Hole (I Nothing))
step (project @(MaybeF :&: Pos) -> Just (Just_ a :&: pos)) =
  case a' of
    Normal ->
      case a of
        Hole (I va) -> Stepped (Hole (I (Just va)))
        DEF_BRANCH
    other -> mapStep (\a -> iAJust_ pos a) other
  where a' = step a

step _other = error "step: unhandled syntactic form"

#undef DEF_BRANCH

type PathConditions = [SBool]

data Work a where
  Continue :: SymState
           -> PathConditions
           -> Cxt Hole Carrier I a
           -> Work a

data IntermediateResult a = IntermediateResult {
  irValue :: a
  , irPathConditions :: PathConditions
  , irSymbolicState :: SymState
  }
  deriving (Show, Eq)

data Result a = Result {
  rValue :: a
  , rPathConditions :: PathConditions
  , rSymbolicTrace :: V.Vector SymInstr
  }
  deriving (Show, Eq)

makeFieldLabelsWith abbreviatedFieldLabels ''IntermediateResult
makeFieldLabelsWith abbreviatedFieldLabels ''Result

finalizeResult :: IntermediateResult a -> Result a
finalizeResult ir =
  Result (ir ^. #value) (ir ^. #pathConditions) (V.fromList . DL.toList $ ir ^. #symbolicState % #symbolicTrace)

iterate :: forall m a.
           ( MonadIO m
           , MonadLogger m
           )
        => S.SerialT m (Work (SymM a))
        ->  m ( S.SerialT m (IntermediateResult a)
              , S.SerialT m (Work (SymM a))
              )
iterate = go S.nil S.nil
  where go :: S.SerialT m (IntermediateResult a)
           -> S.SerialT m (Work (SymM a)) -- ^work list of items that has been stepped in this iteration already
           -> S.SerialT m (Work (SymM a)) -- ^work list of items to be stepped in this iteration
           -> m ( S.SerialT m (IntermediateResult a)
                , S.SerialT m (Work (SymM a))
                )
        go results konts worklist = do
          hasWork <- S.uncons @S.SerialT worklist
          case hasWork of
            Nothing -> return (results, konts)
            Just (Continue st pcs term, more) -> do
              case step term of
                Stepped term' -> go results (Continue st pcs term' `S.cons` konts) more
                PendingBranch sbool k -> do
                  let trueConds = sbool:pcs
                  let falseConds = (neg sbool):pcs
                  let sampleCount = st ^. #sampleCounter

                  $(logDebug) (pack $ printf "checking path consistency for %s" (show trueConds))
                  trueConsistency <- liftIO $ checkConsistency trueConds sampleCount
                  $(logDebug) (pack $ printf "path is %s" (show trueConsistency))

                  $(logDebug) (pack $ printf "checking path consistency for %s" (show falseConds))
                  falseConsistency <- liftIO $ checkConsistency falseConds sampleCount
                  $(logDebug) (pack $ printf "path is %s" (show falseConsistency))

                  case (trueConsistency, falseConsistency) of
                    (Ok, Ok) -> go results (Continue st trueConds (k True) `S.cons`
                                            Continue st falseConds (k False) `S.cons`
                                            konts) more
                    (Ok, Inconsistent) -> go results (Continue st trueConds (k True) `S.cons` konts) more
                    (Inconsistent, Ok) -> go results (Continue st falseConds (k False) `S.cons` konts) more
                    _ -> go results konts more
                PendingNoise center width k ->
                  let (instr, st') = runSymM st $ do
                        sample <- laplaceNoise center width
                        shift  <- SReal . SVar <$> gfresh "shift"
                        cost   <- SReal . SVar <$> gfresh "cost"
                        return $ SymInstr sample shift cost
                      actualSt' = st' & (#symbolicTrace %~ flip DL.snoc instr)
                  in go results (Continue actualSt' pcs (k (instr ^. #sample)) `S.cons` konts) more
                Normal ->
                  case project @(MonadF :&: Pos) term of
                    Just (Ret vterm :&: _pos) ->
                      case vterm of
                        Hole (I val) -> go (IntermediateResult val pcs st `S.cons` results) konts more
                        _other -> error "iterate: expected first-order value on normalized term"
                    _other -> error "iterate: expected (Ret _) on normalized term"

explore :: ( MonadIO m
           , MonadLogger m
           )
        => S.SerialT m (Work (SymM a))
        -> S.SerialT m (IntermediateResult a)
explore work = do
  (results, more) <- lift $ iterate work
  hasMore <- lift $ S.uncons @S.SerialT more
  case hasMore of
    Just _ -> S.wSerial results (explore more)
    Nothing -> results

seval :: (MonadLogger m, MonadIO m) => Cxt Hole Carrier I (SymM a) -> S.SerialT m (Result a)
seval term =
  S.map finalizeResult
  $ explore . S.fromList
  $ [Continue (SymState empty DL.empty 0) [] term]

type GroupKey a = (a, V.Vector SymInstr)

groupStep :: ( Ord a
             , MonadLogger m
             , MonadIO m
             )
          => Result a
          -> M.Map (GroupKey a) SBool
          -> m (SU.Need (M.Map (GroupKey a) SBool))
groupStep (Result output pcs trace) acc =
  fmap SU.More (M.alterF go (output, trace) acc)
  where go Nothing     = (return . Just) (conjunct pcs)
        go (Just cond) = (return . Just) (cond .|| conjunct pcs)

groupExtract :: forall m a.
                ( MonadLogger m
                , MonadIO m
                )
             => M.Map (GroupKey a) SBool -> m (S.SerialT m (Result a))
groupExtract = go . M.toList
  where go :: [(GroupKey a, SBool)] -> m (S.SerialT m (Result a))
        go []                            = return S.nil
        go (((output, strace), pc):more) = do
          tail <- go more
          return $ (Result output [pc] strace) S..: tail

groupOptimization ::
  ( Ord a
  , MonadLogger m
  , MonadIO m
  ) => SU.GeneralizedTake m (Result a)
groupOptimization =
  SU.GeneralizedTake groupStep (return M.empty) groupExtract
