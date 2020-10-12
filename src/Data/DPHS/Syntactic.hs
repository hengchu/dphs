module Data.DPHS.Syntactic where

import Type.Reflection

class Syntactic (f :: * -> *) a where
  type DeepRepr a :: *

  toDeepRepr   :: a -> f (DeepRepr a)
  fromDeepRepr :: f (DeepRepr a) -> a

-- | The shallow representation of monadic values.
newtype Mon f m a = Mon {runMon :: forall b. Typeable b => (a -> f (m b)) -> f (m b)}
  deriving (Functor)

instance Applicative (Mon f m) where
  pure a = Mon $ \k -> k a
  f <*> a = f >>= \f' -> a >>= \a' -> return (f' a')

instance Monad (Mon f m) where
  return a = Mon $ \k -> k a
  Mon m >>= f = Mon $ \k -> m (\a -> runMon (f a) k)
