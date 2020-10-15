{-# OPTIONS_GHC -Wno-unused-do-bind #-}
module Data.DPHS.Examples.Fuzzi where

import Data.Functor.Compose
import Type.Reflection

import Data.Comp.Multi.Term

import Data.DPHS.HXFunctor
import Data.DPHS.Name
import Data.DPHS.Fuzzi
import Data.DPHS.Syntax
import Data.DPHS.Syntactic

x :: Typeable a => Variable a
x = V "x"

xx :: Fuzzi f (FuzziM Double)
xx = iDeref x

ex1 :: EmMon (Fuzzi f) FuzziM ()
ex1 = do
  xx .= laplace 1.0 0.0
  xx .= laplace xx 0.0
  xx .= laplace xx xx

deepEx1 :: forall f. Fuzzi f (FuzziM ())
deepEx1 = toDeepRepr (ex1 @f)

namedEx1 :: forall m. FreshM m => m (Term NFuzziF (FuzziM ()))
namedEx1 =
  -- the type annotation for ex1 here is important...
  -- otherwise the typechecker cannot infer the type of "holes" in the term
  getCompose $ hxcata (hoasToNamedAlg @FuzziF) (toDeepRepr (ex1 @(Compose m (Term NFuzziF))))

ex2 :: EmMon (Fuzzi f) FuzziM ()
ex2 = do
  if_ (xx .> 5)
      ex1
      (do xx .= 2.0 * laplace 1.0 0.0)

ex3 :: EmMon (Fuzzi f) FuzziM ()
ex3 = do
  while (xx ./= 0.0) $ do
    xx .= laplace 1.0 0.0

ex4 :: EmMon (Fuzzi f) FuzziM ()
ex4 = do
  y .= 0
  ac (V "y") 100 $ do
    if_ (xx .> 100)
      (xx .= laplace 1.0 0.0)
      (xx .= laplace 2.0 0.0)
  where y = v @Int (V "y")
