module Data.DPHS.Typecheck.Fuzzi where

import Type.Reflection
import qualified Data.Map.Strict as M

import Optics
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Derive
import Data.Comp.Multi.HFunctor
import Control.Monad.Catch

import Data.DPHS.Syntax
import Data.DPHS.Fuzzi
import Data.DPHS.Name

type Sens  = Double
type Eps   = Double
type Delta = Double

data AnyVariable :: * where
  AnyVariable :: Typeable a => Variable a -> AnyVariable

instance Show AnyVariable where
  -- TODO

instance Eq AnyVariable where
  -- TODO

instance Ord AnyVariable where
  -- TODO

type Cxt = M.Map AnyVariable Sens

data Ty =
    ExprTy {
      tySensitivity :: Sens
    }
  | StmtTy {
      tyCxt :: Cxt
    }
  deriving (Show, Eq, Ord)

makeFieldLabels ''Ty

data CoTerm =
    ExprCoTerm {
      coTermTermination :: Bool
      }
  | StmtCoTerm {
      coTermTermination :: Bool
      }
  deriving (Show, Eq, Ord)

makeFieldLabels ''CoTerm

class SensCheck (h :: (* -> *) -> * -> *) where
  -- |Sensitivity checking algebra builds a function that maps from the typing
  -- context to either an expression sensitivity, or a post-condition typing
  -- context.
  sensCheckAlg :: MonadThrow m => AlgM m h (K (Cxt -> m Ty))

liftSum ''SensCheck
