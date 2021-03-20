{-# OPTIONS_GHC -Wno-unused-do-bind #-}
module Data.DPHS.Examples.Fuzzi where

import Data.Functor.Compose
import Type.Reflection

import Data.Comp.Multi.Term
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Annotation

import Data.DPHS.SrcLoc
import Data.DPHS.HXFunctor
import Data.DPHS.Name
import Data.DPHS.Fuzzi
import Data.DPHS.Syntax
import Data.DPHS.Syntactic

x :: Typeable a => Variable a
x = V "x"

xx :: Term (WithPos FuzziF) (FuzziM Double)
xx = v x

ex1 :: EmMon (Term (WithPos FuzziF)) FuzziM ()
ex1 = do
  V "x" .= laplace xx 1.0 
  V "x" .= laplace xx 0.0

deepEx1 :: Term (WithPos FuzziF) (FuzziM ())
deepEx1 = toDeepRepr' ex1

namedEx1 :: FreshM m => m (Term (WithPos NFuzziF) (FuzziM ()))
namedEx1 = getCompose $ hxcata (hoasToNamedAlg @(WithPos FuzziF)) (xtoCxt deepEx1)

{-
ex2 :: EmMon (Term FuzziF) FuzziM ()
ex2 = do
  if_ (xx .> 5)
      ex1
      (do xx .= 2.0 * laplace 1.0 0.0)

ex3 :: EmMon (Term FuzziF) FuzziM ()
ex3 = do
  while (xx ./= 0.0) $ do
    xx .= laplace 1.0 0.0

ex4 :: EmMon (Term FuzziF) FuzziM ()
ex4 = do
  y .= 0
  ac (V "y") 100 $ do
    if_ (xx .> 100)
      (xx .= laplace 1.0 0.0)
      (xx .= laplace 2.0 0.0)
  where y = v @Int (V "y")
-}
