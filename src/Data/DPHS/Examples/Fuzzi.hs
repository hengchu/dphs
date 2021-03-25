{-# OPTIONS_GHC -Wno-unused-do-bind #-}
module Data.DPHS.Examples.Fuzzi where

import Data.Functor.Compose
import Type.Reflection

import Data.Comp.Multi.Term
import Data.Comp.Multi.Annotation
import Data.Comp.Multi

import Data.DPHS.Types
import Data.DPHS.SrcLoc
import Data.DPHS.HXFunctor
import Data.DPHS.Name
import Data.DPHS.Fuzzi
import Data.DPHS.Syntax
import Data.DPHS.Syntactic

vw, vx, vy, vz :: Variable Double
vw = V "w"
vx = V "x"
vy = V "y"
vz = V "z"

vxs, vys :: Typeable a => Variable a
vxs = V "xs"
vys = V "ys"

vi :: Typeable a => Variable a
vi = V "i"

vrow :: Typeable a => Variable a
vrow = V "row"

w, x, y, z :: Term (WithPos FuzziF) Double
w = v vw
x = v vx
y = v vy
z = v vz

xs :: Term (WithPos FuzziF) (Array Double)
xs = v vxs

ys :: Term (WithPos FuzziF) (Bag Double)
ys = v vys

i :: Term (WithPos FuzziF) Int
i = v vi

row :: Term (WithPos FuzziF) (Vec N5 Double)
row = Term $ injectA noPos (inj $ XVar vrow)

ex1 :: EmMon (Term (WithPos FuzziF)) FuzziM ()
ex1 = do
  vx .$= laplace x 1.0
  vx .$= laplace x 2.0

namedEx1 :: FreshM m => m (Term (WithPos NFuzziF) (FuzziM ()))
namedEx1 = toNamed ex1

ex2 :: EmMon (Term (WithPos FuzziF)) FuzziM ()
ex2 = do
  vi .= (0 :: Term (WithPos FuzziF) Int)
  vx .= (1.0 :: Term (WithPos FuzziF) Double)
  vy .= (1.0 :: Term (WithPos FuzziF) Double)
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

classify :: Term (WithPos FuzziF) Double -> Term (WithPos FuzziF) Double
classify x = if_ (x .> 100) (fromDeepRepr' $ 1.0) (fromDeepRepr' $ -1.0)

namedEx4 :: FreshM m => m (Term (WithPos NFuzziF) (FuzziM ()))
namedEx4 = toNamed ex4

ex5 :: EmMon (Term (WithPos FuzziF)) FuzziM ()
ex5 = do
  ex4
  vx .= bsum 1.0 ys

namedEx5 :: FreshM m => m (Term (WithPos NFuzziF) (FuzziM ()))
namedEx5 = toNamed ex5

noiseSum :: Term (WithPos FuzziF) Double -> EmMon (Term (WithPos FuzziF)) FuzziM ()
noiseSum entry = do
  vx .= (0 :: _ Double)
  vx .$= laplace entry 5.0
  vy .= (x + y)

ex6 :: EmMon (Term (WithPos FuzziF)) FuzziM ()
ex6 = do
  let entries = toList (fromDeepRepr' row)
  forMon_ entries noiseSum

toNamed :: (Typeable a, FreshM m) => EmMon (Term (WithPos FuzziF)) FuzziM a -> m (Term (WithPos NFuzziF) (FuzziM a))
toNamed = getCompose . hxcata (hoasToNamedAlg @(WithPos FuzziF)) . xtoCxt . toDeepRepr'

toNamed' :: (Typeable a, FreshM m) => (Term (WithPos FuzziF)) a -> m (Term (WithPos NFuzziF) a)
toNamed' = getCompose . hxcata (hoasToNamedAlg @(WithPos FuzziF)) . xtoCxt
