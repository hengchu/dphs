{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.DPHS.Types where

import Data.Type.Equality

newtype Array a = Array [a]
  deriving (Show, Eq, Ord, Functor)

newtype Bag a = Bag [a]
  deriving (Show, Eq, Ord, Functor)

data Nat = O | S Nat deriving (Show, Eq, Ord)

data SNat (n :: Nat) where
  SO :: SNat 'O
  SS :: SNat a -> SNat ('S a)

-- |Tests whether two nat singletons are equal, and return a proof
-- that can be used the refine the input types when they match.
snatEq :: forall (a :: Nat) (b :: Nat). SNat a -> SNat b -> Maybe (a :~: b)
snatEq SO SO = Just Refl
snatEq (SS a) (SS b) = do
  Refl <- snatEq a b
  return Refl
snatEq _ _ = Nothing

class Index (i :: Nat) (n :: Nat) where
  at_ :: Vec n a -> SNat i -> a

instance Index 'O ('S n) where
  at_ (Cons x _xs) SO = x

instance Index a b => Index ('S a) ('S b) where
  at_ (Cons _ xs) (SS n) = at_ xs n

-- |A generalized homogeneous tuple type.
data Vec (n :: Nat) a where
  Nil  :: Vec 'O a
  Cons :: a -> Vec n a -> Vec ('S n) a

type N0  = 'O
type N1  = 'S N0
type N2  = 'S N1
type N3  = 'S N2
type N4  = 'S N3
type N5  = 'S N4
type N6  = 'S N5
type N7  = 'S N6
type N8  = 'S N7
type N9  = 'S N8
type N10 = 'S N9

type V0 = Vec N0
type V1 = Vec N1
type V2 = Vec N2
type V3 = Vec N3
type V4 = Vec N4
type V5 = Vec N5
type V6 = Vec N6
type V7 = Vec N7
type V8 = Vec N8
type V9 = Vec N9
type V10 = Vec N10

instance Show (SNat 'O) where
  show _ = "0"
instance {-# OVERLAPPABLE #-}
  Show (SNat n) => Show (SNat ('S n)) where
  -- extremely inefficient... but OK for small numbers?
  show (SS n) = show $ 1 + (read (show n) :: Int)

class SingNat (a :: Nat) where
  singNat :: SNat a

instance SingNat 'O where
  singNat = SO
instance SingNat a => SingNat ('S a) where
  singNat = SS (singNat @a)
