module SpecTesting where

import Test.Hspec

import Data.Maybe
import qualified Data.Vector as V

import Data.DPHS.TEval
import Data.DPHS.DPCheck
import Data.DPHS.Symbolic
import Data.DPHS.Testing

coupleTests :: SpecWith (Arg Expectation)
coupleTests = describe "Data.DPHS.Testing.couple" $ do
  it "successfully couples a simple example" $ do
    let calls = V.fromList [Call 0 1 1.5]
        sinstrs = V.fromList [SymInstr (SReal $ SLap 0 (SR 1.0) 1) (SReal $ SVar "shift_0") (SReal $ SVar "cost_0")]
        result = couple calls (1 :: Int) [] sinstrs (1 :: Int)
    print result
    result `shouldSatisfy` isJust

  it "successfully couples another simple example" $ do
    let calls = V.fromList [Call 0 1 1.5]
        sinstrs = V.fromList [SymInstr (SReal $ SLap 0 (SR 1.0) 1) (SReal $ SVar "shift_0") (SReal $ SVar "cost_0")]
        result = couple calls (1 :: Int) [] sinstrs (2 :: Int)
    result `shouldSatisfy` isNothing

  it "successfully matches concrete and symbolic outputs" $ do
    let calls = V.fromList [Call 0 1 1.5]
        sinstrs = V.fromList [SymInstr (SReal $ SLap 0 (SR 1.0) 1) (SReal $ SVar "shift_0") (SReal $ SVar "cost_0")]
        result = couple calls (1 :: Int) [] sinstrs (SInt $ SVar "output")
    print result
    result `shouldSatisfy` isJust

  it "rejects when symbolic trace is longer than concrete trace " $ do
    let calls = V.fromList [Call 0 1 1.5]
        sinstrs = V.fromList [SymInstr (SReal $ SLap 0 (SR 1.0) 1) (SReal $ SVar "shift_0") (SReal $ SVar "cost_0"),
                              SymInstr (SReal $ SLap 1 (SR 1.0) 1) (SReal $ SVar "shift_1") (SReal $ SVar "cost_1")]
        result = couple calls (1 :: Int) [] sinstrs (SInt $ SVar "output")
    result `shouldSatisfy` isNothing
