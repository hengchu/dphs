module SpecTesting where

import Test.Hspec

import Data.Maybe
import qualified Data.Vector as V

import Control.Monad.IO.Class

import Data.DPHS.TEval
import Data.DPHS.DPCheck
import Data.DPHS.Symbolic
import Data.DPHS.Testing
import Data.DPHS.SolverZ3
import Data.DPHS.Logging
import Data.DPHS.Syntactic
import Data.DPHS.Examples.DPCheck

coupleTests :: SpecWith (Arg Expectation)
coupleTests = describe "Data.DPHS.Testing.couple" $ do
  it "successfully couples a simple example" $ do
    let calls = V.fromList [Call 0 1 1.5]
        sinstrs = V.fromList [SymInstr (SReal $ SLap 0 (SR 1.0) 1) (SReal $ SVar "shift_0") (SReal $ SVar "cost_0")]
        result = couple calls (1 :: Int) [] sinstrs (1 :: Int) 1.0
    print result
    result `shouldSatisfy` isJust

  it "successfully couples another simple example" $ do
    let calls = V.fromList [Call 0 1 1.5]
        sinstrs = V.fromList [SymInstr (SReal $ SLap 0 (SR 1.0) 1) (SReal $ SVar "shift_0") (SReal $ SVar "cost_0")]
        result = couple calls (1 :: Int) [] sinstrs (2 :: Int) 1.0
    result `shouldSatisfy` isNothing

  it "successfully matches concrete and symbolic outputs" $ do
    let calls = V.fromList [Call 0 1 1.5]
        sinstrs = V.fromList [SymInstr (SReal $ SLap 0 (SR 1.0) 1) (SReal $ SVar "shift_0") (SReal $ SVar "cost_0")]
        result = couple calls (1 :: Int) [] sinstrs (SInt $ SVar "output") 1.0
    print result
    result `shouldSatisfy` isJust

  it "rejects when symbolic trace is longer than concrete trace " $ do
    let calls = V.fromList [Call 0 1 1.5]
        sinstrs = V.fromList [SymInstr (SReal $ SLap 0 (SR 1.0) 1) (SReal $ SVar "shift_0") (SReal $ SVar "cost_0"),
                              SymInstr (SReal $ SLap 1 (SR 1.0) 1) (SReal $ SVar "shift_1") (SReal $ SVar "cost_1")]
        result = couple calls (1 :: Int) [] sinstrs (SInt $ SVar "output") 1.0
    result `shouldSatisfy` isNothing

approxProofTests :: SpecWith (Arg Expectation)
approxProofTests = describe "Data.DPHS.Testing.approxProof" $ do
  it "successfully constructs a valid proof for rnm on small inputs" $ do
    let xs1 = [1,2,3]
        xs2 = [2,1,3]
    solverResults <- liftIO $ do
      models <-
        approxProof
          (toDeepRepr' $ rnm xs1)
          (toDeepRepr' $ rnm xs2)
          100 2.0
          runStderrColoredLoggingT
      mapM (\mdl -> checkConsistency [mdl] 0) models
    solverResults `shouldSatisfy` (all (\r -> r == Ok))

  it "successfully detects error for rnm on small inputs when privacy budget is too small" $ do
    let xs1 = [1,2,3]
        xs2 = [2,1,3]
    solverResults <- liftIO $ do
      models <-
        approxProof
          (toDeepRepr' $ rnm xs1)
          (toDeepRepr' $ rnm xs2)
          100 0.5
          runStderrColoredLoggingT
      mapM (\mdl -> checkConsistency [mdl] 0) models
    solverResults `shouldSatisfy` (any (\r -> r == Inconsistent))
