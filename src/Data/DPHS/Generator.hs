module Data.DPHS.Generator where

import Data.Functor.Compose

import System.Random.MWC
import System.Random.MWC.Distributions

newtype Similar a = Similar (a, a)
  deriving (Show, Eq, Ord, Functor)

fmapInner :: Functor f => (a -> b) -> Similar (f a) -> Similar (f b)
fmapInner f = getCompose . fmap f . Compose

left :: Similar a -> a
left (Similar (a, _)) = a

right :: Similar a -> a
right (Similar (_, a)) = a

l1List :: Double -> IO (Similar [Double])
l1List diff = do
  seed <- createSystemRandom
  (size :: Int) <- uniformRM (3, 10) seed
  list1 <- sequence (take size $ repeat (standard seed))
  diffs <- sequence (take size $ repeat (standard seed))
  let totalDiff   = sum (map abs diffs)
      scale       = diff / (totalDiff + 0.1)
      actualDiffs = map (*scale) diffs
      list2       = zipWith (+) list1 actualDiffs
  return (Similar (list1, list2))

lInfList :: Double -> IO (Similar [Double])
lInfList diff = do
  seed <- createSystemRandom
  (size :: Int) <- uniformRM (3, 10) seed
  list1 <- sequence (take size $ repeat (standard seed))
  diffs <- sequence (take size $ repeat (uniformRM (-diff, diff) seed))
  let list2 = zipWith (+) list1 diffs
  return (Similar (list1, list2))
