{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.DPHS.Testing where

import Data.DPHS.DPCheck
import Data.DPHS.SEval
import Data.DPHS.SrcLoc
import Data.DPHS.TEval
import Data.DPHS.Symbolic
import Data.DPHS.Syntax
import Data.DPHS.Logging

import Optics
import qualified Data.Map.Strict as M
import qualified Data.Vector as V
import Control.Monad.Catch
import Control.Monad
import Data.Semigroup

import Data.Comp.Multi
import qualified Streamly as S
import qualified Streamly.Data.Fold as S
import qualified Streamly.Internal.Data.Fold.Types as S
import qualified Streamly.Prelude as S

-- | Each key in a 'Bucket' is a group of traces that share a coupling, under
-- the pointwise equality proof technique.
type Bucket a = M.Map (Key a) (V.Vector (V.Vector Call, Val a))

data DPCheckError =
  DifferentTraceSize String -- The given result a has different trace size.
  | DivergingSymbolicState SymState SymState
  deriving (Show, Eq)

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

-- There are a few cases of the symbolic execution result.

-- 1. outputs with fully determined shapes (outputs with Eq, Ord, and is not a symbolic output)
-- 2. purely symbolic outputs
-- 3. containers (we do not have symbolic containers) with purely symbolic outputs
-- 4. containers with mixed symbolic and static outputs

-- 1. we can do optimization
-- 2. nothing can be ruled out, all paths need to be considered for each trace
-- 3. can statically rule out some matches
-- 4. can statically rule out some matches

-- So, 2 is the most general case. We need to present all path conditions, and
-- all symbolic trace to a bucket in the case of 2, and build a disjunction
-- among all symbolic paths.

-- We can use defunctionalized "strategy" combinators to let the user enable
-- various optimizations in a type-safe manner, by requiring typeclass
-- constraints on those outputs that can be optimized.

-- optimizations:
-- 1. pre-disjunction of path conditions?
-- 1. if output has Ord, binary search to match path with bucket?
-- 3. not much...
-- 4. not much...

-- In the most general case, we essentially have a table like this...
--     pc1 pc2 pc3 pc4 ... pc_n
-- tr1   \/  \/  \/   \/  \/    (disjunction between path conditions)
--    /\                        (conjunction between traces)
-- tr2
--    /\
-- tr3
--    /\
-- ...
--    /\
-- tr_n

-- but we want to delay building the disjunction until we actually receive the
-- trace. because knowing the trace let's us rule out some impossible matches,
-- resulting in smaller SMT model.

unpackSymSample :: SReal -> (Int, SReal, Double)
unpackSymSample (SReal (SLap idx center width)) = (idx, SReal center, width)
unpackSymSample other = error $ "unpackSymSample: expecting SLap constructor, got " ++ show other

-- |Couple a concrete trace with a symbolic trace. If we can statically
-- determinine that these two traces cannot be coupled, then produce 'Nothing'.
couple ::
  Match a b
  => V.Vector Call
  -> a
  -> PathConditions
  -> V.Vector SymInstr
  -> b
  -> Maybe SBool
couple ctrace cresult pcs strace sresult =
  case ( length strace > length ctrace
       , match cresult sresult
       ) of
    (True, _)  -> Nothing
    (_, Static False) -> Nothing
    (False, Static True) -> do
      costBounds <- V.zipWithM makeCostBound ctrace strace
      return (conjunct costBounds .&& conjunct pcs)
    (False, Symbolic equality) -> do
      costBounds <- V.zipWithM makeCostBound ctrace strace
      return (conjunct costBounds .&& conjunct pcs .&& equality)
  where makeCostBound :: Call -> SymInstr -> Maybe SBool
        makeCostBound call sinstr =
          let (_, center, width) = unpackSymSample (sinstr ^. #sample)
              cWidth = realToFrac (call ^. #width)
              lowerbound = abs (sinstr ^. #shift + center - (realToFrac $ call ^. #center)) / cWidth
          in if width == call ^. #width
             then Just (sinstr ^. #cost .>= lowerbound)
             else Nothing

coupleAllPathsFold ::
  Match a b
  => V.Vector Call
  -> a
  -> S.Fold (LoggingT IO) (Result b) SBool
coupleAllPathsFold ctrace cresult = S.Fold step (return sfalse) return
  where step acc (Result sresult pcs strace) =
          case couple ctrace cresult pcs strace sresult of
            Nothing -> return acc
            Just cond -> return (acc .|| cond)

-- |Couple a concrete trace with all possibly matching paths.
coupleAllPaths ::
  Match a b
  => V.Vector Call
  -> a
  -> SerialLogging (Result b)
  -> LoggingT IO SBool
coupleAllPaths ctrace cresult =
  S.fold (coupleAllPathsFold ctrace cresult)

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

conjunct :: Foldable t => t SBool -> SBool
conjunct = foldr (.&&) strue

disjunct :: Foldable t => t SBool -> SBool
disjunct = foldr (.||) sfalse

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
