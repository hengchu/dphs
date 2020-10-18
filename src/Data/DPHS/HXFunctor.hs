module Data.DPHS.HXFunctor where

import Unsafe.Coerce

import Data.DPHS.Name

import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.Sum
import Data.Comp.Multi.Term
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Annotation

import Data.Functor.Compose

-- |A higher-order exponential functor. Useful for embedding terms with HOAS
-- binders.
class HXFunctor (h :: (* -> *) -> * -> *) where
  hxmap ::
    (forall a. f a -> g a) ->
    (forall a. g a -> f a) ->
    (forall a. h f a -> h g a)

instance {-# OVERLAPPABLE #-} HFunctor h => HXFunctor h where
  hxmap f _ = hfmap f

instance {-# OVERLAPPING #-}
  ( HXFunctor h1
  , HXFunctor h2
  , h1 :<: (h1 :+: h2)
  , h2 :<: (h1 :+: h2)
  ) => HXFunctor (h1 :+: h2) where
  hxmap f g =
    caseH
      (\left -> inj $ hxmap f g left)
      (\right -> inj $ hxmap f g right)

instance {-# OVERLAPPING #-}
  HXFunctor h => HXFunctor (h :&: p) where
  hxmap f g (term :&: p) =
    hxmap @h f g term :&: p

class HOASToNamed (h :: (* -> *) -> * -> *) (tgt :: (* -> *) -> * -> *) where
  -- |Algebra for converting a HOAS representation with carrier 'h' into a term
  -- that uses named representation 'tgt'. The conversion is provided a
  -- freshness context through the monad 'm'.
  hoasToNamedAlg :: FreshM m => Alg h (Compose m (Term tgt))

instance ( HOASToNamed h1 tgt
         , HOASToNamed h2 tgt
         ) => HOASToNamed (h1 :+: h2) tgt where
  hoasToNamedAlg = caseH (hoasToNamedAlg @h1) (hoasToNamedAlg @h2)

hxcata ::
  forall h f.
  HXFunctor h =>
  Alg h f ->
  (forall a. Context h f a -> f a)
hxcata _   (Hole term) = term
hxcata alg (Term term) = alg . go $ term
  where
    go = hxmap (hxcata alg) Hole

-- |Just like 'toCxt', but only needs an exponential functor.
xtoCxt :: HXFunctor h => Term h a -> Context h f a
xtoCxt = unsafeCoerce
