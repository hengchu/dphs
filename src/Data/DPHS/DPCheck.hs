{-# OPTIONS -Wno-missing-signatures #-}

module Data.DPHS.DPCheck where

import Data.Comp.Multi
import Data.Comp.Multi.Derive
import Optics
import Optics.TH

import Control.Monad.State.Strict
import Data.Functor.Compose
import Data.Kind
import GHC.Stack
import Type.Reflection
import qualified GHC.TypeLits as GHC

import Data.DPHS.Name
import Data.DPHS.Symbolic
import Data.DPHS.Syntax
import Data.DPHS.Syntactic
import Data.DPHS.HXFunctor
import Data.DPHS.SrcLoc

class ( Monad m
      , Fractional (Noise m)
      ) => NoiseM m where
  type Noise m :: *

  -- |Syntax for sampling laplace noise.
  laplaceNoise :: Noise m -> Double -> m (Noise m)

data EffF :: (* -> *) -> * -> * where
  Branch :: ( SynBool bool
            , Typeable bool
            ) => r bool -> r a -> r a -> EffF r a
  Laplace :: ( real ~ Noise m
             , NoiseM m
             , Typeable m
             , Typeable real
             ) => r real -> Double -> EffF r (m real)

$(derive [makeHFunctor, makeHFoldable, makeHTraversable,
          smartConstructors, smartAConstructors]
         [''EffF])

type DPCheckF = ArithF :+: CompareF 
                :+: EffF :+: XLambdaF :+: MonadF :+: ContainerF

type NDPCheckF = ArithF :+: CompareF
                 :+: EffF :+: LambdaF :+: MonadF :+: ContainerF

instance
  ( EffF :<: tgt
  , EffF :&: Pos :<: tgtPos
  , tgtPos ~ WithPos tgt
  , DistAnn tgt Pos tgtPos
  ) => HOASToNamed (EffF :&: Pos) tgtPos where
  hoasToNamedAlg (Branch cond t f :&: pos) = 
    Compose $ iABranch pos <$> getCompose cond <*> getCompose t <*> getCompose f
  hoasToNamedAlg (Laplace center width :&: pos) =
    Compose $ iALaplace pos <$> getCompose center <*> pure width

if_ :: forall bool a.
       ( SyntacticPos DPCheckF a
       , Typeable bool
       , SynBool bool
       , CheckBool bool
       , HasCallStack
       ) => Term (WithPos DPCheckF) bool -> a -> a -> a
if_ cond t f =
  fromDeepRepr' $ iABranch (fromCallStack callStack) cond (toDeepRepr' t) (toDeepRepr' f)

laplace ::
  ( HasCallStack
  , real ~ Noise m
  , NoiseM m
  , Typeable m
  , Typeable real
  ) => Term (WithPos DPCheckF) real
  -> Double
  -> EmMon (Term (WithPos DPCheckF)) m real
laplace center width =
  fromDeepRepr' $ iALaplace (fromCallStack callStack) center width

data SymState = SymState {
  ssNames :: NameState,
  ssSampleCounter :: Int
  } deriving (Show, Eq, Ord)

-- |The Monad for symbolic execution of DPCheck programs.
newtype SymM a = SymM { runSymM :: State SymState a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadState SymState
           ) via (State SymState)

type family UnsupportedBoolType b where
  UnsupportedBoolType b =
    GHC.TypeError ('GHC.Text "Unsupported boolean type: "
                   'GHC.:<>: 'GHC.ShowType b) 

type family CheckBool (b :: *) :: Constraint where
  CheckBool Bool = ()
  CheckBool SBool = ()
  CheckBool b = UnsupportedBoolType b

makeFieldLabelsWith abbreviatedFieldLabels ''SymState

instance FreshM SymM where
  getNameState = get >>= \st -> return $ st ^. #names
  modifyNameState f = modify (\st -> st & #names .~ f (st ^. #names))

instance NoiseM SymM where
  type Noise SymM = SReal

  laplaceNoise (SReal center) width = do
    i <- get >>= \st -> return $ st ^. #sampleCounter
    shift <- SReal . SVar <$> gfresh "shift"
    return $ (SReal (SLap i width)) + shift
