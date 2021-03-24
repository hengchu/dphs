module Data.DPHS.Examples.LogisticRegression where

import Control.Monad
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
import Data.DPHS.Examples.Fuzzi (toNamed', toNamed)

-- |Modify this type to generalize to arbitrary dimensions.
type Dim_ = N5
type Dim  = 'S Dim_

vdb :: Variable (Bag (Vec Dim Double))
vdb = V "db"

-- | Assuming 0th position is the 1/0 label.
db :: Term (WithPos FuzziF) (Bag (Vec Dim Double))
db = v vdb

vparam :: Variable (Vec Dim Double)
vparam = V "param"

-- | Assuming 0th position is the bias term.
param :: Term (WithPos FuzziF) (Vec Dim Double)
param = v vparam

sigmoid :: Term (WithPos FuzziF) Double -> Term (WithPos FuzziF) Double
sigmoid x = 1 / (1 + expf (-x))

-- | Given a row of data, compute the gradient on param.
gradient :: Term (WithPos FuzziF) (Vec Dim Double) -> Term (WithPos FuzziF) (Vec Dim Double)
gradient row =
  let deepRow@(Cons y (rowEntries :: Vec Dim_ (Term (WithPos FuzziF) Double))) = fromDeepRepr' row
      extendedRow = Cons 1 rowEntries
      factor = sigmoid (dot extendedRow (fromDeepRepr' param)) - y
  in toDeepRepr' $ scale factor deepRow

-- |Goal: implement a single iteration of clippped gradient descent using a
-- private database db, and a public initial parameter param.
iter :: EmMon (Term (WithPos FuzziF)) FuzziM ()
iter = undefined
