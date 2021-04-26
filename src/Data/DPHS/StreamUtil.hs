module Data.DPHS.StreamUtil where

import qualified Streamly as S
import qualified Streamly.Prelude as S

data Need s =
  Enough s | More s

-- |'GeneralizedTake' gives a flexible encoding for consuming a bounded prefix
-- from an potentially infinite stream.
data GeneralizedTake m a where
  GeneralizedTake :: (a -> s -> m (Need s))   -- ^step
                  -> m s                      -- ^initial
                  -> (s -> m (S.SerialT m a)) -- ^extract
                  -> GeneralizedTake m a

-- |Execute a 'GeneralizedTake' on the given stream.
take :: forall m a.
        Monad m
     => GeneralizedTake m a
     -> S.SerialT m a
     -> m (S.SerialT m a)
take (GeneralizedTake step initial extract) stream = do
  acc <- initial
  go acc step extract stream
  where go :: forall s.
              s
           -> (a -> s -> m (Need s))
           -> (s -> m (S.SerialT m a))
           -> S.SerialT m a
           -> m (S.SerialT m a)
        go acc step extract stream = do
          hasMore <- S.uncons @S.SerialT stream
          case hasMore of
            Nothing -> extract acc
            Just (head, tail) -> do
              status <- step head acc
              case status of
                More   nextAcc -> go nextAcc step extract tail
                Enough nextAcc -> extract nextAcc
