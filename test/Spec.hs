import Data.DPHS.Examples.Fuzzi
import Data.DPHS.Fuzzi
import Data.DPHS.Name

import Data.Either
import Control.Monad.State.Strict

import Test.Hspec
import Test.QuickCheck

preprocessTests :: SpecWith (Arg Expectation)
preprocessTests = describe "Data.DPHS.Fuzzi.preprocess" $ do
  it "successfully processes ex1" $ do
    let namedEx1' = flip evalStateT empty (namedEx1 >>= preprocess)
    print namedEx1'
    namedEx1' `shouldSatisfy` isRight

  it "successfully processes ex2" $ do
    let namedEx2' = flip evalStateT empty (namedEx2 >>= preprocess)
    print namedEx2'
    namedEx2' `shouldSatisfy` isRight

sensitivityTests :: SpecWith (Arg Expectation)
sensitivityTests = describe "Sensitivity Properties" $ do
  return () 
    
main :: IO ()
main = hspec $ do
  preprocessTests
  sensitivityTests
