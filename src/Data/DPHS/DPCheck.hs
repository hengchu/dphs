{-# OPTIONS -Wno-missing-signatures #-}

module Data.DPHS.DPCheck where

import Data.DList hiding (Cons, Nil)
import Data.Comp.Multi
import Data.Comp.Multi.Derive
import Optics

import Text.Printf
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

instance ShowHF EffF where
  showHF (Branch cond t1 t2) = K (printf "if %s then %s else %s" (unK cond) (unK t1) (unK t2))
  showHF (Laplace center width) = K (printf "laplace %s %f" (unK center) width)

data ListF :: (* -> *) -> * -> * where
  Nil  :: ListF r (DList a)
  Cons :: r a -> r (DList a) -> ListF r (DList a)
  Snoc :: r (DList a) -> r a -> ListF r (DList a)
$(derive [makeShowHF, makeEqHF, makeOrdHF,
          makeHFunctor, makeHFoldable, makeHTraversable]
         [''ListF])

iNil :: ListF :<: f => Cxt h f x (DList a)
iNil = inject Nil

iANil ::
  ( ListF :<: s
  , DistAnn s p f
  ) => p -> Cxt h f x (DList a)
iANil p = Term (injectA p (inj Nil))

iCons :: ListF :<: f => Cxt h f x a -> Cxt h f x (DList a) -> Cxt h f x (DList a)
iCons hd tl = inject (Cons hd tl)

iACons ::
  ( ListF :<: s
  , DistAnn s p f
  ) => p -> Cxt h f x a -> Cxt h f x (DList a) -> Cxt h f x (DList a)
iACons p hd tl = Term (injectA p (inj (Cons hd tl)))

iSnoc :: ListF :<: f => Cxt h f x (DList a) -> Cxt h f x a -> Cxt h f x (DList a)
iSnoc hd tl = inject (Snoc hd tl)

iASnoc ::
  ( ListF :<: s
  , DistAnn s p f
  ) => p -> Cxt h f x (DList a) -> Cxt h f x a -> Cxt h f x (DList a)
iASnoc p hd tl = Term (injectA p (inj (Snoc hd tl)))

type DPCheckF = ArithF :+: CompareF
                :+: EffF :+: XLambdaF :+: MonadF :+: ListF

type NDPCheckF = ArithF :+: CompareF
                 :+: EffF :+: LambdaF :+: MonadF :+: ListF

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

nil :: (HasCallStack, Typeable a) => Term (WithPos DPCheckF) (DList a)
nil = iANil (fromCallStack callStack)

cons ::
  ( HasCallStack
  , Typeable a
  ) => Term (WithPos DPCheckF) a -> Term (WithPos DPCheckF) (DList a) -> Term (WithPos DPCheckF) (DList a)
cons = iACons (fromCallStack callStack)

snoc ::
  ( HasCallStack
  , Typeable a
  ) => Term (WithPos DPCheckF) (DList a) -> Term (WithPos DPCheckF) a -> Term (WithPos DPCheckF) (DList a)
snoc = iASnoc (fromCallStack callStack)

data SymInstr = SymInstr {
  siSample :: SReal
  , siShift :: SReal
  , siCost :: SReal
  } deriving (Show, Eq, Ord)

data SymState = SymState {
  -- |The state for generating fresh names.
  ssNames :: NameState,
  -- |The list of symbolic sample, shift, and cost.
  ssSymbolicTrace :: DList SymInstr,
  ssSampleCounter :: Int
  } deriving (Show, Eq)

-- |The Monad for symbolic execution of DPCheck programs.
newtype SymM a = SymM { runSymM_ :: State SymState a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadState SymState
           ) via (State SymState)

runSymM :: SymState -> SymM a -> (a, SymState)
runSymM st = flip runState st . runSymM_

type family UnsupportedBoolType b where
  UnsupportedBoolType b =
    GHC.TypeError ('GHC.Text "Unsupported boolean type: "
                   'GHC.:<>: 'GHC.ShowType b)

type family CheckBool (b :: *) :: Constraint where
  CheckBool Bool = ()
  CheckBool SBool = ()
  CheckBool b = UnsupportedBoolType b

makeFieldLabelsWith abbreviatedFieldLabels ''SymInstr
makeFieldLabelsWith abbreviatedFieldLabels ''SymState

instance FreshM SymM where
  getNameState = get >>= \st -> return $ st ^. #names
  modifyNameState f = modify (\st -> st & #names .~ f (st ^. #names))

instance NoiseM SymM where
  type Noise SymM = SReal

  laplaceNoise (SReal center) width = do
    i <- get >>= \st -> return $ st ^. #sampleCounter
    modify $ \st -> st & #sampleCounter %~ (+1)
    return $ (SReal (SLap i center width))
