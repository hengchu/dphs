module Data.DPHS.Examples.DPCheck where

import Type.Reflection

import Data.Comp.Multi

import Data.DPHS.SrcLoc
import Data.DPHS.DPCheck
import Data.DPHS.Syntax
import Data.DPHS.Syntactic

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
