module Data.DPHS.SolverZ3 where

import qualified Data.Vector as V

import Data.DPHS.Syntax
import Data.DPHS.Symbolic

import Z3.Monad
import Control.Monad.Reader

allocateLapSamples ::
  MonadZ3 m => Int -> m (V.Vector AST)
allocateLapSamples n =
  V.forM (V.fromList [0..n]) $ \idx ->
    mkFreshRealVar ("lap_" ++ show idx)

toZ3AST ::
  ( MonadZ3 m
  , MonadReader (V.Vector AST) m
  ) => SExp -> m AST
toZ3AST (SI v) = mkInteger v
toZ3AST (SR v) = mkRational v
toZ3AST (SLap i _ _) = (V.! i) <$> ask
toZ3AST (SVar x) = do
  sym <- mkStringSymbol (show x)
  mkRealVar sym
toZ3AST (SAdd a b) = do
  a' <- toZ3AST a
  b' <- toZ3AST b
  mkAdd [a', b']
toZ3AST (SSub a b) = do
  a' <- toZ3AST a
  b' <- toZ3AST b
  mkSub [a', b']
toZ3AST (SDiv a b) = do
  a' <- toZ3AST a
  b' <- toZ3AST b
  mkDiv a' b'
toZ3AST (SMult a b) = do
  a' <- toZ3AST a
  b' <- toZ3AST b
  mkMul [a', b']
toZ3AST (SAbs a) = do
  a' <- toZ3AST a
  negA' <- toZ3AST $ case (-(SReal a)) of (SReal term) -> term
  cond <- toZ3AST $ case (SReal a .>= 0) of (SBool term) -> term
  mkIte cond a' negA'
toZ3AST (SSignum a) = do
  let condEq0 =
        case SReal a .== 0 of
          SBool term -> term
      condGt0 =
        case SReal a .> 0 of
          SBool term -> term

  condEq0' <- toZ3AST condEq0
  condGt0' <- toZ3AST condGt0
  zero <- mkInteger 0
  one <- mkInteger 1
  negOne <- mkInteger (-1)

  neqZeroBranch <- mkIte condGt0' one negOne
  mkIte condEq0' zero neqZeroBranch
toZ3AST (SEq a b) = do
  a' <- toZ3AST a
  b' <- toZ3AST b
  mkEq a' b'
toZ3AST (SNeq a b) = do
  a' <- toZ3AST a
  b' <- toZ3AST b
  mkDistinct [a', b']
toZ3AST (SLt a b) = do
  a' <- toZ3AST a
  b' <- toZ3AST b
  mkLt a' b'
toZ3AST (SLe a b) = do
  a' <- toZ3AST a
  b' <- toZ3AST b
  mkLe a' b'
toZ3AST (SGt a b) = do
  a' <- toZ3AST a
  b' <- toZ3AST b
  mkGt a' b'
toZ3AST (SGe a b) = do
  a' <- toZ3AST a
  b' <- toZ3AST b
  mkGe a' b'
toZ3AST (SNeg a) =
  toZ3AST a >>= mkNot
toZ3AST (SAnd a b) = do
  a' <- toZ3AST a
  b' <- toZ3AST b
  mkAnd [a', b']
toZ3AST (SOr a b) = do
  a' <- toZ3AST a
  b' <- toZ3AST b
  mkOr [a', b']
toZ3AST STrue = mkTrue
toZ3AST SFalse = mkFalse

data Consistency =
  Ok | Inconsistent deriving (Show, Eq, Ord)

checkConsistency ::
  [SBool] -> Int -> IO Consistency
checkConsistency pcs numSamples = evalZ3 $ do
  solverReset
  samples <- allocateLapSamples numSamples
  assertions <- flip runReaderT samples $
    forM pcs (\(SBool term) -> toZ3AST term)

  forM_ assertions solverAssertCnstr

  result <- solverCheck
  return $
    case result of
      Sat -> Ok
      Unsat -> Inconsistent
      Undef -> Ok
