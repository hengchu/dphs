{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
module Data.DPHS.Typecheck.Fuzzi where

import Control.Monad
import Control.Monad.Catch
import qualified Data.Map.Strict as M

import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Annotation
import Data.Comp.Multi.Derive
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.Term hiding (Cxt)
import Optics

import Data.DPHS.Name

-- |Annotation for whether a program fragment is deterministic or probabilistic.
data ProbAnn = D | P deriving (Show, Eq, Ord)

-- |Annotation for whether a program fragment co-terminates or terminates.
data TermAnn = C | T deriving (Show, Eq, Ord)

data Sensitivity =
  Constant Double
  | Sensitive Double
  deriving (Show, Eq, Ord)

type TyContext = M.Map Name Sensitivity

data TypeInfo =
  ExprInfo {
    tiSensitivity :: Sensitivity,
    tiProbAnnn :: ProbAnn,
    tiTermAnn :: TermAnn
  }
  | CmdInfo {
    tiPostContext :: TyContext,
    tiProbAnn :: ProbAnn,
    tiTermAnn :: TermAnn,
    tiEpsilon :: Double,
    tiDelta   :: Double
  } deriving (Show, Eq, Ord)

makeFieldLabelsWith abbreviatedFieldLabels ''TypeInfo
makePrisms ''TypeInfo

data MacroTypeInfo m =
  Atomic {
    -- |The type info of a grounded term.
    mtiTypeInfo :: TypeInfo
  }
  | Macro {
    -- |Delayed typechecker for a macro that is not yet instantiated.
    mtiFunctionInfo :: MacroTypeInfo m -> MacroTypeInfo m
  }

makeFieldLabelsWith abbreviatedFieldLabels ''MacroTypeInfo
makePrisms ''MacroTypeInfo

type TypeChecker m = TyContext -> MacroTypeInfo m

class TyAlg (h :: (* -> *) -> * -> *) where
  tyAlg :: MonadThrow m => Alg h (K (TypeChecker m))

liftSum ''TyAlg
