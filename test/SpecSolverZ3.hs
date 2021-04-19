module SpecSolverZ3 where

import Data.DPHS.Symbolic
import Data.DPHS.Syntax
import Data.DPHS.SolverZ3

import Test.Hspec

consistencyTests :: SpecWith (Arg Expectation)
consistencyTests = describe "Data.DPHS.SolverZ3.checkConsistency" $ do
  it "successfully checks trivial example" $ do
    let a = SVar "a"
    let b = SVar "b"
    let impossible = [a .>= b, a .< b]
    r <- checkConsistency impossible 10
    r `shouldBe` Inconsistent
    let possible = [a .>= b, a .<= b]
    r <- checkConsistency possible 10
    r `shouldBe` Ok
