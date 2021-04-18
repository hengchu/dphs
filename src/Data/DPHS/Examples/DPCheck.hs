module Data.DPHS.Examples.DPCheck where

import Type.Reflection

import Data.Comp.Multi

import Data.DPHS.SrcLoc
import Data.DPHS.DPCheck
import Data.DPHS.Syntax
import Data.DPHS.Syntactic

trivial :: forall m num.
           ( num ~ Noise m
           , CheckBool (Cmp num)
           , Typeable (Cmp num)
           , NoiseM m
           , Typeable m
           , Typeable num
           , SynOrd num
           ) => EmMon (Term (WithPos DPCheckF)) m num
trivial = do
  (x :: Term (WithPos DPCheckF) num) <- laplace 0 1.0
  if_ (x .>= 0)
      (laplace 0 1.0)
      (laplace 1 1.0)
