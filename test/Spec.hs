{-# OPTIONS -Wno-incomplete-uni-patterns #-}

import Data.DPHS.Examples.Fuzzi
import qualified Data.DPHS.Examples.LogisticRegression as LR
import Data.DPHS.Fuzzi
import Data.DPHS.Name
import Data.DPHS.Typecheck.Fuzzi

import Data.Either
import qualified Data.Map.Strict as M 
import Control.Monad.State.Strict

import Test.Hspec

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

simpleTypeCheckingTests :: SpecWith (Arg Expectation)
simpleTypeCheckingTests = describe "Data.DPHS.Typecheck.Fuzzi" $ do
  it "successfully checks ex1" $ do
    let ~(Right code) = flip evalStateT empty (namedEx1 >>= preprocess)
    case typecheck code (M.fromList [("x", 1.0)]) of
      Left err -> expectationFailure (show err)
      Right result -> result `shouldBe` (M.fromList [("x", Sens 0)], P, T, 1.0, 0.0)
    case typecheck code (M.fromList [("x", 2.0)]) of
      Left err -> expectationFailure (show err)
      Right result -> result `shouldBe` (M.fromList [("x", Sens 0)], P, T, 2.0, 0.0)
    case typecheck code (M.fromList [("x", 10.0)]) of
      Left err -> expectationFailure (show err)
      Right result -> result `shouldBe` (M.fromList [("x", Sens 0)], P, T, 10.0, 0.0)
  it "successfully checks ex2" $ do
    let ~(Right code) = flip evalStateT empty (namedEx2 >>= preprocess)
    let cxt = [("x", 0), ("y", 0), ("w", 0), ("i", 0)]
    case typecheck code (M.fromList cxt) of
      Left err -> expectationFailure (show err)
      Right result -> result `shouldBe` (fmap Sens $ M.fromList cxt, D, C, 0, 0)
  it "successfully checks ex3" $ do
    let ~(Right code) = flip evalStateT empty (namedEx3 >>= preprocess)
    case typecheck code (M.fromList [("xs", 1.0)]) of
      Left err -> expectationFailure (show err)
      Right result -> result `shouldBe` (M.fromList [("xs", Sens 2.0)], D, T, 0, 0)
  it "successfully checks ex4" $ do
    let ~(Right code) = flip evalStateT empty (namedEx4 >>= preprocess)
    case typecheck code (M.fromList [("ys", 1.0)]) of
      Left err -> expectationFailure (show err)
      Right result -> result `shouldBe` (M.fromList [("ys", Sens 1.0)], D, T, 0, 0)
  it "successfully checks ex5" $ do
    let ~(Right code) = flip evalStateT empty (namedEx5 >>= preprocess)
    case typecheck code (M.fromList [("x", 0), ("ys", 5.0)]) of
      Left err -> expectationFailure (show err)
      Right result -> result
        `shouldBe` (M.fromList [("x", Sens 5.0), ("ys", Sens 5.0)], D, T, 0, 0)
  it "successfully checks ex6" $ do
    let ~(Right code) = flip evalStateT empty (toNamed ex6 >>= preprocess)
    case typecheck code (M.fromList [("row", 1.0), ("x", 0), ("y", 0)]) of
      Left err -> expectationFailure (show err)
      Right result -> result
        `shouldBe` (M.fromList [("row", Sens 1.0), ("x", Sens 0), ("y", Sens 0)], P, T, 1, 0)
  it "successfully checks logistic regression" $ do
    let ~(Right code) = flip evalStateT LR.names (toNamed (LR.acIters 1000) >>= preprocess)
    case typecheck code LR.context of
      Left err -> expectationFailure (show err)
      Right result@(cxt, p, t, eps, dlt) -> do
        print result
        cxt `shouldBe` (M.map Sens LR.context)
        p `shouldBe` P
        t `shouldBe` C
        eps `shouldSatisfy` (<= 17)
        dlt `shouldBe` (1e-6)
    
main :: IO ()
main = hspec $ do
  preprocessTests
  sensitivityTests
  simpleTypeCheckingTests
