{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.DPHS.Testing where

import Data.DPHS.DPCheck
import Data.DPHS.SEval
import Data.DPHS.SrcLoc
import Data.DPHS.TEval
import Data.DPHS.Symbolic
import Data.DPHS.Syntax
import Data.DPHS.Logging
import Data.DPHS.HXFunctor
import qualified Data.DPHS.StreamUtil as SU

import Control.Monad
import Control.Monad.Catch
import Optics
import qualified Data.DList as DL
import qualified Data.Map.Strict as M
import qualified Data.Vector as V

import Data.Comp.Multi
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

unpackSReal :: SReal -> SExp
unpackSReal (SReal e) = e

substituteSymbolicSamples
  :: V.Vector Call -> V.Vector SymInstr -> SExp -> SExp
substituteSymbolicSamples ctrace strace (SLap i _ _) =
  unpackSReal $ (realToFrac $ ctrace V.! i ^. #sample) + (strace V.! i) ^. #shift
substituteSymbolicSamples ctrace strace term =
  let recur = substituteSymbolicSamples ctrace strace
  in case term of
       SAdd a b -> SAdd (recur a) (recur b)
       SSub a b -> SSub (recur a) (recur b)
       SDiv a b -> SDiv (recur a) (recur b)
       SMult a b -> SMult (recur a) (recur b)
       SAbs a -> SAbs (recur a)
       SSignum a -> SSignum (recur a)
       SEq a b -> SEq (recur a) (recur b)
       SNeq a b -> SNeq (recur a) (recur b)
       SLt a b -> SLt (recur a) (recur b)
       SLe a b -> SLe (recur a) (recur b)
       SGt a b -> SGt (recur a) (recur b)
       SGe a b -> SGe (recur a) (recur b)
       SNeg a -> SNeg (recur a)
       SAnd a b -> SAnd (recur a) (recur b)
       SOr a b -> SOr (recur a) (recur b)
       _ -> term

substituteSBool :: V.Vector Call -> V.Vector SymInstr -> SBool -> SBool
substituteSBool ctrace strace (SBool term) =
  SBool $ substituteSymbolicSamples ctrace strace term

-- |Couple a concrete trace with a symbolic trace. If we can statically
-- determinine that these two traces cannot be coupled, then produce 'Nothing'.
couple ::
  Match a b
  => V.Vector Call
  -> a
  -> PathConditions
  -> V.Vector SymInstr
  -> b
  -> Double
  -> Maybe SBool
couple ctrace cresult pcs strace sresult eps =
  case ( length strace > length ctrace
       , match cresult sresult
       ) of
    (True, _)  -> Nothing
    (_, Static False) -> Nothing
    (False, Static True) -> do
      costBounds <- V.zipWithM makeCostBound ctrace strace
      let totalCost = sum (fmap (view #cost) strace)
      return . substituteSBool ctrace strace $
        (conjunct costBounds .&& conjunct pcs .&& totalCost .<= realToFrac eps)
    (False, Symbolic equality) -> do
      let totalCost = sum (fmap (view #cost) strace)
      costBounds <- V.zipWithM makeCostBound ctrace strace
      return . substituteSBool ctrace strace $
        (conjunct costBounds .&& conjunct pcs .&& equality .&& totalCost .<= realToFrac eps)
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
  -> Double
  -> S.Fold (LoggingT IO) (Result b) SBool
coupleAllPathsFold ctrace cresult eps =
  -- Note that using the default value of false implies that each concrete trace
  -- must have at least 1 matching path.
  S.Fold step (return sfalse) return
  where step acc (Result sresult pcs strace) =
          case couple ctrace cresult pcs strace sresult eps of
            Nothing -> return acc
            Just cond -> return (acc .|| cond)

-- To work with infinite symbolic result streams, we can design an interface
-- that gives a programmer the choice to decide how much of the infinite stream
-- should be consumed.

-- In practice, we are only interested in exhausting the paths that match things
-- that we observe from concrete executions. For some programs, like PrivTree,
-- the infinite stream is actually producing monotonically larger outputs, so we
-- can use a O(1) space cutoff strategy, which fits the idea of "streaming".

-- In general, maybe we could allow up to O(n) space for intermediate
-- aggregation to decide how much is consumed?

-- |Couple a concrete trace with all possibly matching paths.
coupleAllPaths ::
  Match a b
  => V.Vector Call
  -> a
  -> Double
  -> SerialLogging (Result b)
  -> LoggingT IO SBool
coupleAllPaths ctrace cresult eps =
  S.fold (coupleAllPathsFold ctrace cresult eps)

conjunctAllTraces ::
  Match a b
  => V.Vector (V.Vector Call, a)
  -> SerialLogging (Result b)
  -> Double
  -> LoggingT IO SBool
conjunctAllTraces traces stream eps = do
  traceModels <- mapM (\(ctrace, cresult) -> coupleAllPaths ctrace cresult eps stream) traces
  return (conjunct traceModels)

data SEvalOptimizationStrategy a where
  None  :: SEvalOptimizationStrategy a
  Group :: Ord a => SEvalOptimizationStrategy a

optimizeSymbolicStream ::
  SEvalOptimizationStrategy a
  -> SerialLogging (Result a)
  -> LoggingT IO (SerialLogging (Result a))
optimizeSymbolicStream None  s = return s
optimizeSymbolicStream Group s = SU.take groupOptimization s

-- |Top-level API for building an SMT model that is the approximate pointwise
-- equality proof, using the concrete and symbolic version of the same program.
-- TODO: need a few more tunable knobs.
-- 1. pre-optimization
approxProof ::
  forall a b.
  ( Show a
  , GroupBy a
  , Match (Val a) b
  )
  => Term (WithPos DPCheckF) (InstrDist a)
  -> Term (WithPos DPCheckF) (SymM      b)
  -> SEvalOptimizationStrategy b
  -> Int
  -> Double
  -> (forall a. LoggingT IO a -> IO a)
  -> IO (V.Vector SBool)
approxProof concrete symbolic symOptStrat ntrials eps runLogger = do
  bucket <- profile ntrials concrete
  optStream <- runLogger $ optimizeSymbolicStream symOptStrat (seval (xtoCxt symbolic))
  models <- runLogger $
            (fmap snd . M.toList) <$>
            mapM (\concrete -> conjunctAllTraces concrete optStream eps) bucket
  return (V.fromList models)

approxProofVerbose ::
  forall a b.
  ( Show a
  , GroupBy a
  , Match (Val a) b
  )
  => Term (WithPos DPCheckF) (InstrDist a)
  -> Term (WithPos DPCheckF) (SymM      b)
  -> SEvalOptimizationStrategy b
  -> Int
  -> Double
  -> IO (V.Vector SBool)
approxProofVerbose concrete symbolic symOptStrat ntrials eps =
  approxProof concrete symbolic symOptStrat ntrials eps runStderrColoredLoggingT

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

instance GroupBy Bool where
  type Key Bool = Bool
  type Val Bool = Bool

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

instance GroupBy a => GroupBy (DL.DList a) where
  type Key (DL.DList a) = DL.DList (Key a)
  type Val (DL.DList a) = DL.DList (Val a)

  key = fmap key
  val = fmap val
