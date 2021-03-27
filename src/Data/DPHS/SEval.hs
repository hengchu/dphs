module Data.DPHS.SEval where

import Data.DPHS.SrcLoc
import Data.DPHS.DPCheck
import Data.DPHS.Syntax
import Data.DPHS.Symbolic

import Data.Comp.Multi
import Data.Comp.Multi.Term
import Data.Comp.Multi.Algebra

data Step a i where
  Stepped :: a i -> Step a i
  PendingBranch :: SBool -> (Bool -> a i) -> Step a i
  PendingNoise  :: (SReal -> a i) -> Step a i
  Normal :: Step a i

type Carrier = WithPos DPCheckF

class SymbolicStep h where
  stepAlg :: Alg h (Step (Term Carrier))

instance
  ( SymbolicStep f,
    SymbolicStep g
  ) => SymbolicStep ((:+:) f g) where
  stepAlg term = ((caseH stepAlg) stepAlg) term

stepArithFAlg :: ArithF (Step (Term Carrier)) a -> Step (Term Carrier) a
stepArithFAlg = undefined
