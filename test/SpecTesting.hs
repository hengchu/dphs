module SpecTesting where

import Test.Hspec

import Data.Maybe
import qualified Data.Vector as V

import Control.Monad.IO.Class

import Data.DPHS.DPCheck
import Data.DPHS.Examples.DPCheck
import Data.DPHS.Generator
import Data.DPHS.Logging
import Data.DPHS.SolverZ3
import Data.DPHS.Symbolic
import Data.DPHS.Syntactic
import Data.DPHS.TEval
import Data.DPHS.Testing

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
    let xs1 = [1,2,3,4,5]
        xs2 = [2,1,3,5,4]
    solverResults <- liftIO $ do
      models <-
        runStderrColoredLoggingWarnT $
          approxProof
            (toDeepRepr' $ rnm xs1)
            (toDeepRepr' $ rnm xs2)
            Group
            100 2.0
      mapM (\mdl -> checkConsistency [mdl] 0) models
    solverResults `shouldSatisfy` (all (\r -> r == Ok))

  it "successfully detects error for rnm on small inputs when privacy budget is too small" $ do
    let xs1 = [1,2,3,5,4]
        xs2 = [2,1,3,4,5]
    solverResults <- liftIO $ do
      models <-
        runStderrColoredLoggingWarnT $
          approxProof
            (toDeepRepr' $ rnm xs1)
            (toDeepRepr' $ rnm xs2)
            Group
            100 0.5
      mapM (\mdl -> checkConsistency [mdl] 0) models
    solverResults `shouldSatisfy` (any (\r -> r == Inconsistent))

  it "successfully constructs a valid proof for svBoolean on small inputs" $ do
    let xs1 = [1,2,3,4,5,6,7,10]
        xs2 = [2,1,2,5,4,5,8,11]
    solverResults <- liftIO $ do
      models <-
        runStderrColoredLoggingWarnT $
          approxProof
            (toDeepRepr' $ svBoolean xs1 7 2)
            (toDeepRepr' $ svBoolean xs2 7 2)
            Group
            500
            1.0
      mapM (\mdl -> checkConsistency [mdl] 0) models
    solverResults `shouldSatisfy` (all (== Ok))

  it "successfully detects error for svBoolean on small inputs when budget is too small" $ do
    let xs1 = [1,2,3,4,5,6,7,10]
        xs2 = [2,1,2,5,4,5,8,11]
    solverResults <- liftIO $ do
      models <-
        runStderrColoredLoggingWarnT $
          approxProof
            (toDeepRepr' $ svBoolean xs1 7 2)
            (toDeepRepr' $ svBoolean xs2 7 2)
            Group
            500
            0.1
      mapM (\mdl -> checkConsistency [mdl] 0) models
    solverResults `shouldSatisfy` (any (== Inconsistent))

expectDPTests :: SpecWith (Arg Expectation)
expectDPTests = describe "Data.DPHS.Testing.expectDP" $ do
  it "successfully accepts rnm" $ do
    isDP <- runStderrColoredLoggingWarnT $ expectDP (lInfList 0 1 1.0) rnmTester Group 100 2.0
    isDP `shouldBe` True

  it "successfully accepts svBoolean" $ do
    isDP <- runStderrColoredLoggingWarnT $ expectDP (lInfList 10 0.1 1.0) (svBooleanTester 9.5 2) Group 100 1.0
    isDP `shouldBe` True

  it "successfully accepts svNumeric" $ do
    isDP <- runStderrColoredLoggingWarnT $ expectDP (lInfList 10 0.1 1.0) (svNumericTester 9.5 2) Group 100 2.0
    isDP `shouldBe` True

expectNotDPTests :: SpecWith (Arg Expectation)
expectNotDPTests = describe "Data.DPHS.Testing.expectNotDP" $ do
  it "successfully rejects rnm with low budget" $ do
    notDP <- runStderrColoredLoggingWarnT $ expectNotDP (lInfList 0 1 1.0) rnmTester Group 100 20 1.0
    notDP `shouldBe` True

  it "successfully rejects svBoolean with low budget" $ do
    notDP <- runStderrColoredLoggingWarnT $ expectNotDP (lInfList 10 0.1 1.0) (svBooleanTester 9.5 2) Group 500 20 0.2
    notDP `shouldBe` True

  -- takes too long to run on CI
  -- it "successfully rejects svBooleanUnbounded" $ do
  --   notDP <- runStderrColoredLoggingWarnT $ expectNotDP (lInfList 10 0.1 1.0) (svBooleanUnboundedTester 9.5) None 500 20 2.0
  --   notDP `shouldBe` True
