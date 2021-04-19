module SpecSEval where

import Optics

import Data.DPHS.Examples.DPCheck
import Data.DPHS.SEval
import Data.DPHS.HXFunctor
import Data.DPHS.Syntactic
import Data.DPHS.Symbolic
import Data.DPHS.Syntax
import Data.DPHS.Logging

import Test.Hspec
import qualified Streamly.Prelude as S

sevalTests :: SpecWith (Arg Expectation)
sevalTests = describe "Data.DPHS.SEval.seval" $ do
  it "successfully evaluates trivial" $ do
    results <- runStdoutColoredLoggingT . S.toList $ seval . xtoCxt . toDeepRepr' $ trivial
    let lap0 = SReal $ SLap 0 0 1
    let lap1 = SReal $ SLap 1 1 1
    let lap2 = SReal $ SLap 1 0 1
    results !! 0 ^. #value `shouldBe` lap1
    results !! 0 ^. #pathConditions `shouldBe` [neg $ lap0 .>= 0]
    results !! 1 ^. #value `shouldBe` lap2
    results !! 1 ^. #pathConditions `shouldBe` [lap0 .>= 0]

  it "successfully evaluates rnm [1,2,3,4]" $ do
    results <- runStdoutColoredLoggingWarnT . S.toList $ seval . xtoCxt . toDeepRepr' $ rnm [1,2,3,4]
    length results `shouldBe` 8
