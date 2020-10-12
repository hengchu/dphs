module Data.DPHS.HXFunctor where

import Data.Comp.Multi.Term

-- |A higher-order exponential functor. Useful for embedding terms with HOAS
-- binders.
class HXFunctor (h :: (* -> *) -> * -> *) where
  hxmap ::
    (forall a. f a -> g a) ->
    (forall a. g a -> f a) ->
    (forall a. h f a -> h g a)

hxcata ::
  forall h f.
  HXFunctor h =>
  (forall a. h f a -> f a) ->
  (forall a. Context h f a -> f a)
hxcata _   (Hole term) = term
hxcata alg (Term term) = alg . go $ term
  where
    go = hxmap (hxcata alg) Hole
