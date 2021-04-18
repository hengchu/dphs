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
