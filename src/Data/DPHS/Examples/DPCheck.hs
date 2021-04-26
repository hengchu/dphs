module Data.DPHS.Examples.DPCheck where

import Data.DList (DList)
import Type.Reflection

import Data.Comp.Multi

import Data.DPHS.SrcLoc
import Data.DPHS.DPCheck
import Data.DPHS.TEval
import Data.DPHS.Syntax
import Data.DPHS.Syntactic
import Data.DPHS.Generator

type DPCheck m num = ( num ~ Noise m
                     , CheckBool (Cmp num)
                     , Typeable (Cmp num)
                     , NoiseM m
                     , Typeable m
                     , Typeable num
                     , SynOrd num
                     )

trivial :: forall m num.
  DPCheck m num => EmMon (Term (WithPos DPCheckF)) m num
trivial = do
  x <- laplace 0 1.0
  if_ (x .>= 0)
      (laplace 0 1.0)
      (laplace 1 1.0)

rnmTester :: Similar [Double]
          -> ( Term (WithPos DPCheckF) (InstrDist Int)
             , Term (WithPos DPCheckF) (SymM      Int)
             )
rnmTester similar =
  ( toDeepRepr' $ rnm (map realToFrac $ left similar)
  , toDeepRepr' $ rnm (map realToFrac $ right similar)
  )

rnm :: forall m num. DPCheck m num =>
  [Term (WithPos DPCheckF) num] -> EmMon (Term (WithPos DPCheckF)) m Int
rnm []     = error "rnm: received empty input"
rnm (x:xs) = do
  xNoised <- laplace x 1.0
  rnmAux xs xNoised 0 1

rnmAux :: forall m num.
  DPCheck m num
  => [Term (WithPos DPCheckF) num]
  -> Term (WithPos DPCheckF) num
  -> Term (WithPos DPCheckF) Int
  -> Term (WithPos DPCheckF) Int
  -> EmMon (Term (WithPos DPCheckF)) m Int
rnmAux []     _       maxIdx _       = return maxIdx
rnmAux (x:xs) currMax maxIdx thisIdx = do
  noised <- laplace x 1.0
  if_ (noised .> currMax)
      (rnmAux xs noised  thisIdx (thisIdx+1))
      (rnmAux xs currMax maxIdx  (thisIdx+1))

svBooleanTester ::
  Double
  -> Int
  -> Similar [Double]
  -> ( Term (WithPos DPCheckF) (InstrDist (DList Bool))
     , Term (WithPos DPCheckF) (SymM      (DList Bool))
     )
svBooleanTester threshold count similar =
  ( toDeepRepr' $ svBoolean (fmap realToFrac $ left similar)  (realToFrac threshold) count
  , toDeepRepr' $ svBoolean (fmap realToFrac $ right similar) (realToFrac threshold) count
  )

svBoolean :: forall m num.
  DPCheck m num
  => [Term (WithPos DPCheckF) num]
  -> Term (WithPos DPCheckF) num
  -> Int
  -> EmMon (Term (WithPos DPCheckF)) m (DList Bool)
svBoolean xs thresh count = do
  thresh' <- laplace thresh 2.0
  svBooleanAux xs (4.0 * realToFrac count) thresh' count nil

svBooleanAux :: forall m num.
  DPCheck m num
  => [Term (WithPos DPCheckF) num]
  -> Double
  -> Term (WithPos DPCheckF) num
  -> Int
  -> Term (WithPos DPCheckF) (DList Bool)
  -> EmMon (Term (WithPos DPCheckF)) m (DList Bool)
svBooleanAux []     _width _ _ acc = return acc
svBooleanAux _      _width _ 0 acc = return acc
svBooleanAux (x:xs) width  t c acc = do
  xNoised <- laplace x width
  if_ (xNoised .> t)
      (svBooleanAux xs width t (c-1) (acc `snoc` ctrue))
      (svBooleanAux xs width t c     (acc `snoc` cfalse))
