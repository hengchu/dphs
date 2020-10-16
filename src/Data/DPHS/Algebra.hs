module Data.DPHS.Algebra where

import Data.Comp.Multi.Algebra
import Data.Comp.Multi.HFunctor

data (f :: * -> *) :* (g :: * -> *) :: * -> * where
  Prod :: f a -> g a -> (f :* g) a

-- |Left projection of product.
prj1 :: (f :* g) a -> f a
prj1 (Prod a _) = a

-- |Right projection of product.
prj2 :: (f :* g) a -> g a
prj2 (Prod _ b) = b

-- |Combine two independent algebra.
prodAlg :: HFunctor h
        => Alg h f1
        -> Alg h f2
        -> Alg h (f1 :* f2)
prodAlg alg1 alg2 h = Prod (alg1 hf1) (alg2 hf2)
  where hf1 = hfmap prj1 h
        hf2 = hfmap prj2 h
