{-# OPTIONS_GHC -Wno-unused-do-bind #-}
module Data.DPHS.Examples.Fuzzi where

import Data.Functor.Compose
import Type.Reflection

import Data.Comp.Multi.Term

import Data.DPHS.Types
import Data.DPHS.SrcLoc
import Data.DPHS.HXFunctor
import Data.DPHS.Name
import Data.DPHS.Fuzzi
import Data.DPHS.Syntax
import Data.DPHS.Syntactic

vw, vx, vy, vz :: Typeable a => Variable a
vw = V "w"
vx = V "x"
vy = V "y"
vz = V "z"

vxs, vys :: Typeable a => Variable a
vxs = V "xs"
vys = V "ys"

vi :: Typeable a => Variable a
vi = V "i"

w, x, y, z :: Term (WithPos FuzziF) (FuzziM Double)
w = v vw
x = v vx
y = v vy
z = v vz

xs :: Term (WithPos FuzziF) (FuzziM (Array Double))
xs = v vxs

ys :: Term (WithPos FuzziF) (FuzziM (Bag Double))
ys = v vys

i :: Term (WithPos FuzziF) (FuzziM Int)
i = v vi

ex1 :: EmMon (Term (WithPos FuzziF)) FuzziM ()
ex1 = do
  vx .= laplace x 1.0
  vx .= laplace x 2.0

namedEx1 :: FreshM m => m (Term (WithPos NFuzziF) (FuzziM ()))
namedEx1 = toNamed ex1

ex2 :: EmMon (Term (WithPos FuzziF)) FuzziM ()
ex2 = do
  vi .= (0 :: Term (WithPos FuzziF) (FuzziM Int))
  vx .= (1.0 :: Term (WithPos FuzziF) (FuzziM Double))
  vy .= (1.0 :: Term (WithPos FuzziF) (FuzziM Double))
  while (i .< 100) $ do
    vw .= y
    vy .= x + y
    vx .= w
    vi .= i + 1

namedEx2 :: FreshM m => m (Term (WithPos NFuzziF) (FuzziM ()))
namedEx2 = toNamed ex2

ex3 :: EmMon (Term (WithPos FuzziF)) FuzziM ()
ex3 = do
  vxs .= amap xs (\x -> 2 * x)

namedEx3 :: FreshM m => m (Term (WithPos NFuzziF) (FuzziM ()))
namedEx3 = toNamed ex3

ex4 :: EmMon (Term (WithPos FuzziF)) FuzziM ()
ex4 = do
  vys .= bmap ys classify

classify :: Term (WithPos FuzziF) (FuzziM Double) -> Term (WithPos FuzziF) (FuzziM Double)
classify x = toDeepRepr' $ if_ (x .> 100) (fromDeepRepr' $ 1.0) (fromDeepRepr' $ -1.0)

namedEx4 :: FreshM m => m (Term (WithPos NFuzziF) (FuzziM ()))
namedEx4 = toNamed ex4

ex5 :: EmMon (Term (WithPos FuzziF)) FuzziM ()
ex5 = do
  ex4
  vx .= bsum 1.0 ys

namedEx5 :: FreshM m => m (Term (WithPos NFuzziF) (FuzziM ()))
namedEx5 = toNamed ex5

toNamed :: (Typeable a, FreshM m) => EmMon (Term (WithPos FuzziF)) FuzziM a -> m (Term (WithPos NFuzziF) (FuzziM a))
toNamed = getCompose . hxcata (hoasToNamedAlg @(WithPos FuzziF)) . xtoCxt . toDeepRepr'

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
