module Data.DPHS.Types where

newtype Array a = Array [a]
  deriving (Show, Eq, Ord, Functor)

newtype Bag a = Bag [a]
  deriving (Show, Eq, Ord, Functor)
