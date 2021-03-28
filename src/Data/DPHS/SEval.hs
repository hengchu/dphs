{-# LANGUAGE CPP #-}

module Data.DPHS.SEval where

import Type.Reflection
import qualified GHC.TypeLits as GHC

import Data.DPHS.Syntax
import Data.DPHS.SrcLoc
import Data.DPHS.DPCheck
import Data.DPHS.Symbolic

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

#define DEF_BRANCH _ -> error "step: Normal is only returned on normalized terms"

-- |'step' is not structurally recursive, so we do direct definition
-- by projection and pattern matching.
step :: forall i h. Cxt h Carrier I i -> Step (Cxt h Carrier I i)
step (Hole (I _)) = Normal
-- All EffF cases.
step (project @(EffF :&: Pos) -> Just (Branch (cond :: _ bool) t f :&: pos)) =
  case eqTypeRep (typeRep @bool) (typeRep @SBool) of
    Just HRefl -> mapStep (\c -> iABranch pos c t f) (step cond)
    Nothing ->
      case eqTypeRep (typeRep @bool) (typeRep @Bool) of
        Just HRefl ->
          case step cond of
            Normal  ->
              case cond of
                Hole (I v) -> if v then Stepped t else Stepped f
                DEF_BRANCH
            other -> mapStep (\c -> iABranch pos c t f) other
        Nothing -> error "step: expecting branch condition to be Bool or SBool"
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
          
#undef DEF_BRANCH

type family ExtractHole (a :: *) where
  ExtractHole (Cxt h _ _ _) = h
  ExtractHole a =
    GHC.TypeError ('GHC.Text "Cannot extract hole from type: " 'GHC.:<>: 'GHC.ShowType a)
