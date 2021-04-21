{-# LANGUAGE UnboxedTuples #-}

module Data.DPHS.TEval where

import Optics

import Control.Monad.Primitive
import Control.Monad.Reader
import Data.IORef
import System.Random.MWC
import System.Random.MWC.Distributions
import Type.Reflection
import qualified Data.Vector as V

import Data.DPHS.Syntax
import Data.DPHS.DPCheck
import Data.DPHS.SrcLoc

import Data.Comp.Multi

data Call = Call {
  cCenter :: Double,
  cWidth  :: Double,
  cSample :: Double
  } deriving (Show, Eq, Ord)

makeFieldLabelsWith abbreviatedFieldLabels ''Call

type TraceMut = IORef [Call]

data InstrDistState = InstrDistState {
  idsTraceMut    :: TraceMut,
  idsStatefulGen :: Gen RealWorld
  }

makeFieldLabelsWith abbreviatedFieldLabels ''InstrDistState

initializeInstrDistState :: IO InstrDistState
initializeInstrDistState =
  InstrDistState <$> newIORef [] <*> createSystemRandom

newtype InstrDist a = InstrDist { runInstrDist_ :: ReaderT InstrDistState IO a }
  deriving ( Functor
           , Applicative
           , Monad
           ) via (ReaderT InstrDistState IO)
  deriving ( MonadReader InstrDistState
           , MonadIO
           , PrimMonad
           ) via (ReaderT InstrDistState IO)

data Bop = Plus | Minus | Mult | Div deriving (Show, Eq, Ord)
data Uop = Abs | Sign deriving (Show, Eq, Ord)

data DistShape a where
  Value   :: a   -> DistShape a
  Laplace :: Int -> DistShape Double -> Double -> DistShape Double
  Binop   :: Bop -> DistShape a -> DistShape a -> DistShape a
  Uop     :: Uop -> DistShape a -> DistShape a

deriving instance Show a => Show (DistShape a)
deriving instance Eq   a => Eq   (DistShape a)
deriving instance Ord  a => Ord  (DistShape a)

data InstrValue a = InstrValue {
  ivProvenance :: DistShape a
  , ivValue      :: a
  }
  deriving (Show, Eq, Ord)

makeFieldLabelsWith abbreviatedFieldLabels ''InstrValue

instance Num a => Num (DistShape a) where
  (+) = Binop Plus
  (-) = Binop Minus
  (*) = Binop Data.DPHS.TEval.Mult
  abs = Uop Data.DPHS.TEval.Abs
  signum = Uop Sign
  fromInteger = Value . fromInteger

instance Fractional a => Fractional (DistShape a) where
  (/) = Binop Data.DPHS.TEval.Div
  fromRational = Value . fromRational

instance Num a => Num (InstrValue a) where
  a + b = InstrValue (a ^. #provenance + b ^. #provenance) (a ^. #value + b ^. #value)
  a - b = InstrValue (a ^. #provenance - b ^. #provenance) (a ^. #value - b ^. #value)
  a * b = InstrValue (a ^. #provenance * b ^. #provenance) (a ^. #value * b ^. #value)
  abs a = InstrValue (abs $ a ^. #provenance) (abs $ a ^. #value)
  signum a = InstrValue (signum $ a ^. #provenance) (signum $ a ^. #value)
  fromInteger v = InstrValue (fromInteger v) (fromInteger v)

instance Fractional a => Fractional (InstrValue a) where
  a / b = InstrValue (a ^. #provenance / b ^. #provenance) (a ^. #value / b ^. #value)
  fromRational v = InstrValue (fromRational v) (fromRational v)

instance NoiseM InstrDist where
  type Noise InstrDist = InstrValue Double

  laplaceNoise center width = do
    prng <- gview #statefulGen
    traceRef <- gview #traceMut
    trace <- liftIO $ readIORef traceRef

    coin <- bernoulli 0.5 prng
    sample <- exponential width prng
    let actualSample = if coin then sample else -sample
        thisCall = Call (center ^. #value) width actualSample
        idx = length trace
        shape = Data.DPHS.TEval.Laplace idx (center ^. #provenance) width
    liftIO $ modifyIORef traceRef $ (thisCall:)

    return $ InstrValue shape actualSample

sample :: InstrDist a -> IO a
sample m =
  initializeInstrDistState >>= runReaderT (runInstrDist_ m)

instrument :: InstrDist a -> IO (V.Vector Call, a)
instrument m = do
  state <- initializeInstrDistState
  result <- runReaderT (runInstrDist_ m) state
  trace <- readIORef (state ^. #traceMut)
  -- list cons builds the trace in the reverse order so we must reverse the
  -- trace before returning it.
  return (V.fromList (reverse trace), result)

type Carrier = WithPos DPCheckF

teval :: Cxt Hole Carrier I a -> a
teval (Hole (I a)) = a

-- All XLambdaF cases
teval (project @(XLambdaF :&: Pos) -> Just (XLam fun :&: _pos)) = \arg ->
  teval (fun (Hole (I arg)))
teval (project @(XLambdaF :&: Pos) -> Just (XApp f arg :&: _pos)) =
  (teval f) (teval arg)
teval (project @(XLambdaF :&: Pos) -> Just (XVar v :&: pos)) =
  error $ "teval: out-of-scope variable " ++ show v ++ " at " ++ show pos

-- All MonadF cases
teval (project @(MonadF :&: Pos) -> Just (Bind m k :&: _pos)) = (teval m) >>= (teval k)
teval (project @(MonadF :&: Pos) -> Just (Ret a :&: _pos)) = return (teval a)

-- All EffF cases
teval (project @(EffF :&: Pos) -> Just (Branch (cond :: _ bool) a b :&: pos)) =
  case eqTypeRep (typeRep @bool) (typeRep @Bool) of
    Just HRefl -> if (teval cond) then (teval a) else (teval b)
    Nothing -> error $ "teval: expected Bool for branch guard at " ++ show pos
teval (project @(EffF :&: Pos) ->
       Just (Data.DPHS.DPCheck.Laplace center width :&: _pos)) =
  laplaceNoise (teval center) width

-- All CompareF cases
teval (project @(CompareF :&: Pos) -> Just (IsEq a b :&: _pos)) =
  teval a .== teval b
teval (project @(CompareF :&: Pos) -> Just (IsNeq a b :&: _pos)) =
  teval a ./= teval b
teval (project @(CompareF :&: Pos) -> Just (IsLt a b :&: _pos)) =
  teval a .< teval b
teval (project @(CompareF :&: Pos) -> Just (IsLe a b :&: _pos)) =
  teval a .<= teval b
teval (project @(CompareF :&: Pos) -> Just (IsGt a b :&: _pos)) =
  teval a .> teval b
teval (project @(CompareF :&: Pos) -> Just (IsGe a b :&: _pos)) =
  teval a .>= teval b
teval (project @(CompareF :&: Pos) -> Just (Neg a :&: _pos)) =
  neg (teval a)
teval (project @(CompareF :&: Pos) -> Just (Or a b :&: _pos)) =
  teval a .|| teval b

-- All ArithF cases
teval (project @(ArithF :&: Pos) -> Just (IntLit v :&: _pos)) = fromIntegral v
teval (project @(ArithF :&: Pos) -> Just (FracLit v :&: _pos)) = fromRational v
teval (project @(ArithF :&: Pos) -> Just (Add a b :&: _pos)) = teval a + teval b
teval (project @(ArithF :&: Pos) -> Just (Sub a b :&: _pos)) = teval a - teval b
teval (project @(ArithF :&: Pos) -> Just (Data.DPHS.Syntax.Abs a :&: _pos)) = abs (teval a)
teval (project @(ArithF :&: Pos) -> Just (Signum a :&: _pos)) = signum (teval a)
teval (project @(ArithF :&: Pos) -> Just (Data.DPHS.Syntax.Mult a b :&: _pos)) = teval a * teval b
teval (project @(ArithF :&: Pos) -> Just (Data.DPHS.Syntax.Div a b :&: _pos)) = teval a / teval b
