{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.DPHS.Types where

import Unsafe.Coerce
import Data.Type.Equality

newtype Array a = Array [a]
  deriving (Show, Eq, Ord, Functor)

newtype Bag a = Bag [a]
  deriving (Show, Eq, Ord, Functor)

data Nat = O | S Nat deriving (Show, Eq, Ord)

data SNat (n :: Nat) where
  SO :: SNat 'O
  SS :: SNat a -> SNat ('S a)

withSingNat :: SNat n -> (SingNat n => r) -> r
withSingNat n k =
  case n of
    SO -> k
    SS n' -> withSingNat n' $ k

withBounded :: forall n r. SingNat n => SNat ('S n) -> (Bounded (Fin ('S n)) => r) -> r
withBounded (SS n) k =
  case singNat @n of
    SO -> k
    SS (n' :: _ n') -> withSingNat n' $ withBounded @n' n k

-- |Tests whether two nat singletons are equal, and return a proof
-- that can be used the refine the input types when they match.
snatEq :: forall (a :: Nat) (b :: Nat). SNat a -> SNat b -> Maybe (a :~: b)
snatEq SO SO = Just Refl
snatEq (SS a) (SS b) = do
  Refl <- snatEq a b
  return Refl
snatEq _ _ = Nothing

class VecAt (i :: Nat) (n :: Nat) where
  at_ :: Vec n a -> SNat i -> a

instance VecAt 'O ('S n) where
  at_ (Cons x _xs) SO = x

instance VecAt a b => VecAt ('S a) ('S b) where
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

instance Functor (Vec n) where
  fmap _f Nil = Nil
  fmap f (Cons x xs) = Cons (f x) (fmap f xs)

class Representable f => Indexable f where
  index :: f a -> Key f -> a

class Representable f where
  type Key f :: *
  tabulate :: (Key f -> a) -> f a

data Fin (n :: Nat) where
  FO :: Fin ('S n)
  FS :: Fin n -> Fin ('S n)

deriving instance Show (Fin n)

instance SingNat n => Enum (Fin n) where
  toEnum 0 =
    case singNat @n of
      SO -> error "impossible"
      SS _ -> FO
  toEnum x
    | x < 0 = error "toEnum @(Fin n): negative value"
    | otherwise =
      case singNat @n of
        SO -> error "impossible"
        SS (n' :: _ n') -> withSingNat n' $ FS $ toEnum @(Fin n') (x-1)

  fromEnum FO = 0
  fromEnum (FS n) = 1+fromEnum (weaken n)

instance {-# OVERLAPPING #-}
  Bounded (Fin N1) where
  minBound = FO
  maxBound = FO

instance {-# OVERLAPPABLE #-}
  Bounded (Fin n) => Bounded (Fin ('S n)) where
  minBound = FO
  maxBound = FS (maxBound @(Fin n))
  
weaken :: Fin n -> Fin ('S n)
weaken = unsafeCoerce
{-
weaken FO = FO
weaken (FS n) = FS (weaken n)
-}

instance SingNat n => Indexable (Vec n) where
  index Nil          _ = error "impossible"
  index (Cons x  _)  FO = x
  index (Cons _x xs) (FS i) =
    case singNat @n of
      SS n' -> withSingNat n' $ index xs i

instance SingNat n => Representable (Vec n) where
  type Key (Vec n) = Fin n

  tabulate g =
    case singNat @n of
      SO -> Nil
      SS (n' :: SNat n') -> withSingNat n' $ Cons (g FO) $ tabulate (\tail -> g (weaken tail))

-- |Convert a list into a vector with a statically known length, while
-- checking to ensure this list has that length.
fromList :: forall n a. SingNat n => [a] -> Maybe (Vec n a)
fromList [] =
  case singNat @n of
    SO -> Just Nil
    SS _ -> Nothing
fromList (x:xs) =
  case singNat @n of
    SO -> Nothing
    SS (n' :: _ n') -> withSingNat n' $ Cons <$> pure x <*> fromList @n' xs

toList :: Vec n a -> [a]
toList Nil = []
toList (Cons x xs) = x:(toList xs)

instance Show a => Show (Vec n a) where
  show xs = show (toList xs)
