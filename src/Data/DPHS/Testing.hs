{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.DPHS.Testing where

import Data.DPHS.DPCheck
import Data.DPHS.HXFunctor
import Data.DPHS.SEval
import Data.DPHS.SrcLoc
import Data.DPHS.TEval
import Data.DPHS.Symbolic
import Data.DPHS.Logging

import Optics
import qualified Data.Map.Strict as M
import qualified Data.Vector as V
import Control.Monad.Catch
import Control.Monad

import Data.Comp.Multi

-- | Each key in a 'Bucket' is a group of traces that share a coupling, under
-- the pointwise equality proof technique.
type Bucket a = M.Map (Key a) (V.Vector (V.Vector Call, Val a))

data DPCheckError =
  DifferentTraceSize String -- The given result a has different trace size.
  deriving (Show, Eq, Ord)

instance Exception DPCheckError

-- |A typeclass that gives projections from a value with type 'a' to its
-- grouping key 'Key a', and the underlying value 'Val a'.
class Ord (Key a) => GroupBy a where
  type Key a :: *
  type Val a :: *

  key :: a -> Key a
  val :: a -> Val a

profile :: ( Show a
          , GroupBy a
          )
       => Int -- ^number of trials to run
       -> Term (WithPos DPCheckF) (InstrDist a) -- ^the program to run
       -> IO (Bucket a) -- ^the gathered bucket
profile ntrials prog = do
  results <- replicateM ntrials (instrument (instrEval prog))
  intermediate <- buildBucket results
  return (fmap V.fromList intermediate)

buildBucket :: ( Show a
               , GroupBy a
               )
            => [(V.Vector Call, a)]
            -> IO (M.Map (Key a) [(V.Vector Call, Val a)])
buildBucket []                     = return M.empty
buildBucket ((trace, result):more) = do
  let k = key result
      v = val result
      tup = (trace, v)
      size = length trace
  tail <- buildBucket more
  M.alterF (go size tup) k tail
  where go _size tup Nothing   = return (Just [tup])
        go _size tup (Just []) = return (Just [tup])
        go size  tup (Just xs@(x:_)) = do
          when (length (fst x) /= size) $
            throwM (DifferentTraceSize (show result))
          return (Just (tup:xs))

type Model = ()

type GeneralStrategy a b =
  Bucket a -- ^the bucket of profiled inputs
  -> SerialLogging (Result b) -- ^a (potentially infinite) stream of symbolic results
  -> LoggingT IO (SerialLogging Model) -- ^a finite stream of models to be
                                       -- checked: each model represents the
                                       -- "approximate proof" for a single
                                       -- output under the pointwise proof
                                       -- technique. Note that this stream must
                                       -- be finite, because the bucket only has
                                       -- finite amount of keys in it.

data SEvalStrategy a b where
  Exhaust :: SEvalStrategy a b -- ^Use all of the symbolic results --- does not
                               -- terminate if the program is infinite.
  ExhaustOrd :: MatchOrd a b => SEvalStrategy a b -- ^Use all of the symbolic
                                                  -- results, but use a more
                                                  -- efficient matching
                                                  -- algorithm --- does not
                                                  -- terminate if the program is
                                                  -- infinite.
  General :: GeneralStrategy a b -> SEvalStrategy a b

exhaustOrd ::
  forall a b. MatchOrd (Key a) b => GeneralStrategy a b
exhaustOrd bkt stream =
  exhaustOrdImpl @a @b M.empty (V.fromList (M.toList bkt)) stream

-- |Find the index of a matching group of trace, using binary search.
binSearch :: MatchOrd k b => V.Vector (k, v) -> b -> Maybe Int
binSearch arr k =
  let end = length arr
      idx = go 0 end
  in if idx >= end
     then Nothing
     else case matchOrd (fst $ arr V.! idx) k of
            EQ -> Just idx
            _  -> Nothing
        -- |do binary search in the range [start, end)
  where go :: Int -> Int -> Int
        go start end
          | start >= end = start
          | otherwise =
            let mid = start + (end - start) `div` 2
            in case matchOrd (fst $ arr V.! mid) k of
                 LT -> go (mid+1) end
                 EQ -> go start mid
                 GT -> go start mid

exhaustOrdImpl ::
  forall a b. MatchOrd (Key a) b
  => M.Map (Key a) Model
  -> V.Vector (Key a, V.Vector (V.Vector Call, Val a))
  -> SerialLogging (Result b)
  -> LoggingT IO (SerialLogging Model)
exhaustOrdImpl models bkt stream = do
  undefined

sevalStrategy :: SEvalStrategy a b
              -> GeneralStrategy a b
sevalStrategy = undefined

instance GroupBy Int where
  type Key Int = Int
  type Val Int = Int

  key = id
  val = id

instance GroupBy Double where
  type Key Double = Double
  type Val Double = Double

  key = id
  val = id

instance Ord a => GroupBy (InstrValue a) where
  type Key (InstrValue a) = DistShape a
  type Val (InstrValue a) = a

  key iv = iv ^. #provenance
  val iv = iv ^. #value

instance GroupBy a => GroupBy [a] where
  type Key [a] = [Key a]
  type Val [a] = [Val a]

  key = fmap key
  val = fmap val
