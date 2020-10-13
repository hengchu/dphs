{-# OPTIONS_GHC -Wno-unused-do-bind #-}
module Data.DPHS.Examples.Fuzzi where

import Type.Reflection

import Data.DPHS.Fuzzi
import Data.DPHS.Syntax
import Data.DPHS.Syntactic

x :: Typeable a => Variable a
x = Variable ()

xx :: Fuzzi f (FuzziM Double)
xx = iDeref x

y :: Typeable a => Variable a
y = Variable ()

yy :: Fuzzi f (FuzziM Int)
yy = iDeref y

ex1 :: EmMon (Fuzzi f) FuzziM ()
ex1 = do
  xx .= laplace 1.0 0.0
  xx .= laplace xx 0.0
  xx .= laplace xx xx

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
ex4 =
  ac y 100 $ do
    if_ (xx .> 100)
      (xx .= laplace 1.0 0.0)
      (xx .= laplace 2.0 0.0)
