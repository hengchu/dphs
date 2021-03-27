{-# OPTIONS -Wno-unused-do-bind #-}

module Data.DPHS.Examples.Fuzzi.LogisticRegression where

import qualified Data.Map.Strict as M
import Control.Monad.State.Strict

import Data.Comp.Multi.Term

import Data.DPHS.Types
import Data.DPHS.SrcLoc
import Data.DPHS.Name
import Data.DPHS.Fuzzi
import Data.DPHS.Syntax
import Data.DPHS.Syntactic

-- |Modify this type to generalize to arbitrary dimensions.
type Dim_ = N5
type Dim  = 'S Dim_

-- | Assuming 0th position is the 1/0 label.
vdb :: FreshM m => m (Variable (Bag (Vec Dim Double)))
vdb = V <$> gfresh "db"

vdbsize :: FreshM m => m (Variable Double)
vdbsize = V <$> gfresh "dbsize"

-- |The variable that stores intermediate bag of gradients.
vgrads :: FreshM m => m (Variable (Bag (Vec Dim Double)))
vgrads = V <$> gfresh "grads"

vaggGradFields ::
  forall (n :: Nat) m.
  ( SingNat n
  , FreshM m
  ) => m (Vec n (Variable Double))
vaggGradFields = do
  case singNat @n of
    SO -> return Nil
    SS n' -> withSingNat n' $ do
      x <- gfresh "gradField"
      xs <- vaggGradFields
      return (Cons (V x) xs)

-- | Assuming 0th position is the bias term.
vparam :: FreshM m => m (Variable (Vec Dim Double))
vparam = V <$> gfresh "param"

sigmoid :: Term (WithPos FuzziF) Double -> Term (WithPos FuzziF) Double
sigmoid x = if_ (x .> 0) x 0 -- ReLU

-- | Given a row of data, compute the gradient on param.
gradient :: Variable (Vec Dim Double)
         -> Term (WithPos FuzziF) (Vec Dim Double)
         -> Term (WithPos FuzziF) (Vec Dim Double)
gradient paramVar row =
  let deepRow@(Cons y (rowEntries :: Vec Dim_ (Term (WithPos FuzziF) Double))) = fromDeepRepr' row
      extendedRow = Cons 1 rowEntries
      factor = sigmoid (dot extendedRow (fromDeepRepr' (v paramVar))) - y
  in toDeepRepr' $ scale factor deepRow

computeDbSize :: Variable Double
              -> Variable (Bag (Vec Dim Double))
              -> EmMon (Term (WithPos FuzziF)) FuzziM ()
computeDbSize vdbsize vdb = do
  vdbsize .= bsum 1.0 (bmap (v vdb) (const 1.0))
  vdbsize .$= laplace (v vdbsize) 100.0

releaseAggGradientAt ::
  Vec Dim (Variable Double)
  -> Variable (Bag (Vec Dim Double))
  -> Variable Double
  -> Fin Dim
  -> EmMon (Term (WithPos FuzziF)) FuzziM ()
releaseAggGradientAt fields vgrads dbSizeVar idx =
  let fld = fields `index` idx
      prj = \row -> (fromDeepRepr' @_ @(Vec Dim _) row) `index` idx
  in do
    fld .= bsum 1.0 (bmap (v vgrads) prj)
    fld .$= laplace (v fld) 100.0
    fld .= (v fld) / (v dbSizeVar)

releaseAggGradient :: FreshM m => m (M.Map Name Double, EmMon (Term (WithPos FuzziF)) FuzziM ())
releaseAggGradient = do
  -- declare program variables
  dbvar@(V dbname) <- vdb
  dbSizeVar@(V dbsizeName) <- vdbsize
  gradsVar@(V gradsName) <- vgrads
  paramVar@(V paramName) <- vparam
  fieldVars <- vaggGradFields
  let cxt = M.fromList $
        [(dbname, 1.0), (gradsName, 1.0), (paramName, 0.0), (dbsizeName, 0.0)]
        ++ map (\(V nm) -> (nm, 0.0)) (toList fieldVars)
  let indices = [minBound .. maxBound] :: [Fin Dim]
  return $ (cxt, do
    computeDbSize dbSizeVar dbvar
    gradsVar .= bmap (v dbvar) (gradient paramVar)
    forMon_ indices (releaseAggGradientAt fieldVars gradsVar dbSizeVar)
    paramVar .= (toDeepRepr' $ fmap v fieldVars))
  
iter' :: ((M.Map Name Double, EmMon (Term (WithPos FuzziF)) FuzziM ()), NameState)
iter' = flip runState empty releaseAggGradient

-- |Goal: implement a single iteration of clippped gradient descent using a
-- private database db, and a public initial parameter param.
iter :: EmMon (Term (WithPos FuzziF)) FuzziM ()
iter = snd (fst iter')

acIters :: Int -> EmMon (Term (WithPos FuzziF)) FuzziM ()
acIters niters = ac niters 1e-6 iter

names :: NameState
names = snd iter'

context :: M.Map Name Double
context = fst (fst iter')
