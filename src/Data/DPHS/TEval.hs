{-# LANGUAGE UnboxedTuples #-}

module Data.DPHS.TEval where

import Optics

import Control.Monad.Primitive
import Control.Monad.Reader
import Data.IORef
import System.Random.MWC
import System.Random.MWC.Distributions
import Type.Reflection
import qualified Data.DList as DL
import qualified Data.Vector as V

import Data.DPHS.Syntax
import Data.DPHS.DPCheck
import Data.DPHS.SrcLoc
import Data.DPHS.HXFunctor

import Data.Comp.Multi
import qualified Data.Comp.Ops as DCO

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

instance SynOrd a => SynOrd (InstrValue a) where
  type Cmp (InstrValue a) = Cmp a

  a .== b = a ^. #value .== b ^. #value
  a ./= b = a ^. #value ./= b ^. #value
  a .<  b = a ^. #value .<  b ^. #value
  a .<= b = a ^. #value .<= b ^. #value
  a .>  b = a ^. #value .>  b ^. #value
  a .>= b = a ^. #value .>= b ^. #value

instance NoiseM InstrDist where
  type Noise InstrDist = InstrValue Double

  laplaceNoise center width = do
    prng <- gview #statefulGen
    traceRef <- gview #traceMut
    trace <- liftIO $ readIORef traceRef

    coin <- bernoulli 0.5 prng
    sample <- exponential width prng
    let actualSample = center ^. #value + if coin then sample else -sample
        thisCall = Call (center ^. #value) width actualSample
        idx = length trace
        shape = Data.DPHS.TEval.Laplace idx (center ^. #provenance) width
    liftIO $ modifyIORef traceRef $ (thisCall:)

    return $ InstrValue shape actualSample

sample :: InstrDist a -> IO a
sample m =
  initializeInstrDistState >>= runReaderT (runInstrDist_ m)

-- |Sample from the given distribution, while producing a trace of calls to the
-- laplace noise command.
instrument :: InstrDist a -> IO (V.Vector Call, a)
instrument m = do
  state <- initializeInstrDistState
  result <- runReaderT (runInstrDist_ m) state
  trace <- readIORef (state ^. #traceMut)
  -- list cons builds the trace in the reverse order so we must reverse the
  -- trace before returning it.
  return (V.fromList (reverse trace), result)

type Carrier = WithPos DPCheckF

-- |Instrumented interpretation of a 'Carrier' term, fixed at the instrumentated
-- distribution monad type.
instrEval :: Term Carrier (InstrDist a) -> InstrDist a
instrEval = eval . xtoCxt

-- |Big-step evaluation of 'Carrier' terms.
eval :: Cxt Hole Carrier I a -> a
eval (Hole (I a)) = a

-- All XLambdaF cases
eval (project @(XLambdaF :&: Pos) -> Just (XLam fun :&: _pos)) = \arg ->
  eval (fun (Hole (I arg)))
eval (project @(XLambdaF :&: Pos) -> Just (XApp f arg :&: _pos)) =
  (eval f) (eval arg)
eval (project @(XLambdaF :&: Pos) -> Just (XVar v :&: pos)) =
  error $ "eval: out-of-scope variable " ++ show v ++ " at " ++ show pos

-- All MonadF cases
eval (project @(MonadF :&: Pos) -> Just (Bind m k :&: _pos)) = (eval m) >>= (eval k)
eval (project @(MonadF :&: Pos) -> Just (Ret a :&: _pos)) = return (eval a)

-- All EffF cases
eval (project @(EffF :&: Pos) -> Just (Branch (cond :: _ bool) a b :&: pos)) =
  case eqTypeRep (typeRep @bool) (typeRep @Bool) of
    Just HRefl -> if (eval cond) then (eval a) else (eval b)
    Nothing -> error $ "eval: expected Bool for branch guard at " ++ show pos
eval (project @(EffF :&: Pos) ->
       Just (Data.DPHS.DPCheck.Laplace center width :&: _pos)) =
  laplaceNoise (eval center) width

-- All CompareF cases
eval (project @(CompareF :&: Pos) -> Just (IsEq a b :&: _pos)) =
  eval a .== eval b
eval (project @(CompareF :&: Pos) -> Just (IsNeq a b :&: _pos)) =
  eval a ./= eval b
eval (project @(CompareF :&: Pos) -> Just (IsLt a b :&: _pos)) =
  eval a .< eval b
eval (project @(CompareF :&: Pos) -> Just (IsLe a b :&: _pos)) =
  eval a .<= eval b
eval (project @(CompareF :&: Pos) -> Just (IsGt a b :&: _pos)) =
  eval a .> eval b
eval (project @(CompareF :&: Pos) -> Just (IsGe a b :&: _pos)) =
  eval a .>= eval b
eval (project @(CompareF :&: Pos) -> Just (Neg a :&: _pos)) =
  neg (eval a)
eval (project @(CompareF :&: Pos) -> Just (Or a b :&: _pos)) =
  eval a .|| eval b
eval (project @(CompareF :&: Pos) -> Just (CTrue :&: _pos)) = true
eval (project @(CompareF :&: Pos) -> Just (CFalse :&: _pos)) = false

-- All ArithF cases
eval (project @(ArithF :&: Pos) -> Just (IntLit v :&: _pos)) = fromIntegral v
eval (project @(ArithF :&: Pos) -> Just (FracLit v :&: _pos)) = fromRational v
eval (project @(ArithF :&: Pos) -> Just (Add a b :&: _pos)) = eval a + eval b
eval (project @(ArithF :&: Pos) -> Just (Sub a b :&: _pos)) = eval a - eval b
eval (project @(ArithF :&: Pos) -> Just (Data.DPHS.Syntax.Abs a :&: _pos)) = abs (eval a)
eval (project @(ArithF :&: Pos) -> Just (Signum a :&: _pos)) = signum (eval a)
eval (project @(ArithF :&: Pos) -> Just (Data.DPHS.Syntax.Mult a b :&: _pos)) = eval a * eval b
eval (project @(ArithF :&: Pos) -> Just (Data.DPHS.Syntax.Div a b :&: _pos)) = eval a / eval b

-- All ListF cases.
eval (project @(ListF :&: Pos) -> Just (Nil :&: _pos)) = DL.empty
eval (project @(ListF :&: Pos) -> Just (Cons hd tl :&: _pos)) = DL.cons (eval hd) (eval tl)
eval (project @(ListF :&: Pos) -> Just (Snoc hd tl :&: _pos)) = DL.snoc (eval hd) (eval tl)

-- All MaybeF cases.
eval (project @(MaybeF :&: Pos) -> Just (Nothing_ :&: _pos)) = Nothing
eval (project @(MaybeF :&: Pos) -> Just (Just_ a :&: _pos))  = Just (eval a)

eval (Term (projectA -> _other DCO.:&: pos)) =
  error $ "eval: unhandled syntactic form at position " ++ show pos
