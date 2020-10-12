{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Data.DPHS.Fuzzi where

import Control.Monad
import Type.Reflection

import Data.DPHS.Syntax
import Data.DPHS.Syntactic

import Data.Comp.Multi
import Data.Comp.Multi.Show ()
import Data.Comp.Multi.Equality ()
import Data.Comp.Multi.Ordering (KOrd(..))
import Data.Comp.Multi.Derive

import Data.Functor.Identity

newtype FuzziM a = FuzziM { runFuzziM :: Identity a }
  deriving (Functor, Applicative, Monad)

type Array a = [a]
type Bag   a = [a]

class (Show a, Eq a, Ord a, Typeable a) => FuzziLit a where

data ExprF :: (* -> *) -> * -> * where
  -- |Dereference a variable.
  Deref :: Typeable a
        => Variable a
        -> ExprF r (FuzziM a)

  -- |Index into a term.
  Index :: r (FuzziM (Array a))
        -> r (FuzziM Int)
        -> ExprF r (FuzziM a)

  -- |Literal structure values.
  Lit   :: FuzziLit a
        => a
        -> ExprF r (FuzziM a)

data PrivMechF :: (* -> *) -> * -> * where
  Laplace :: r (FuzziM Double)
          -> r (FuzziM Double)
          -> PrivMechF r (FuzziM Double)

$(derive [makeHFunctor, makeHFoldable, makeHTraversable,
          makeShowHF, makeEqHF, makeOrdHF,
          smartConstructors, smartAConstructors]
         [''PrivMechF])

instance EqHF ExprF where
  eqHF (Deref (v1 :: Variable a1)) (Deref (v2 :: Variable a2)) =
    case eqTypeRep (typeRep @a1) (typeRep @a2) of
      Just HRefl -> v1 == v2
      Nothing -> False
  eqHF (Deref _) _ = False

  eqHF (Index a1 idx1) (Index a2 idx2) = keq a1 a2 && keq idx1 idx2
  eqHF (Index _ _) _ = False

  eqHF (Lit (a1 :: a1)) (Lit (a2 :: a2)) =
    case eqTypeRep (typeRep @a1) (typeRep @a2) of
      Just HRefl -> a1 == a2
      Nothing -> False
  eqHF (Lit _) _ = False

instance OrdHF ExprF where
  compareHF (Deref (v1 :: Variable a1)) (Deref (v2 :: Variable a2)) =
    case eqTypeRep tr1 tr2 of
      Just HRefl -> compare v1 v2
      Nothing -> compare (SomeTypeRep tr1) (SomeTypeRep tr2)
    where tr1 = typeRep @a1
          tr2 = typeRep @a2
  compareHF (Deref _) _ = LT

  compareHF (Index _ _) (Deref _) = GT
  compareHF (Index a1 idx1) (Index a2 idx2) = kcompare a1 a2 <> kcompare idx1 idx2
  compareHF (Index _ _) _ = LT

  compareHF (Lit (v1 :: a1)) (Lit (v2 :: a2)) =
    case eqTypeRep tr1 tr2 of
      Just HRefl -> compare v1 v2
      Nothing -> compare (SomeTypeRep tr1) (SomeTypeRep tr2)
    where tr1 = typeRep @a1
          tr2 = typeRep @a2
  compareHF (Lit _) _ = GT

$(derive [makeHFunctor, makeHFoldable, makeHTraversable,
          makeShowHF, --makeEqHF, makeOrdHF,
          smartConstructors, smartAConstructors]
         [''ExprF])

data EffF :: (* -> *) -> * -> * where
  Assign :: r (FuzziM a)            -- ^ the lhs expression to be assigned
         -> r (FuzziM a)            -- ^ the rhs expression to assign to the lhs
         -> EffF r (FuzziM ())
  Branch :: r (FuzziM Bool)         -- ^ branch condition
         -> r (FuzziM ())           -- ^ true branch statements
         -> r (FuzziM ())           -- ^ false branch statements
         -> EffF r (FuzziM ())
  While  :: r (FuzziM Bool) ->      -- ^ loop condition
            r (FuzziM ()) ->        -- ^ loop body
            EffF r (FuzziM ())

$(derive [makeHFunctor, makeHFoldable, makeHTraversable,
          makeShowHF, makeEqHF, makeOrdHF,
          smartConstructors, smartAConstructors]
         [''EffF])

type FuzziF  = ArithF :+: ExprF :+: PrivMechF :+: EffF :+: XLambdaF :+: XMonadF
type Fuzzi f = Context FuzziF f

assign :: forall f a.
          Fuzzi f (FuzziM a)
       -> Fuzzi f (FuzziM a)
       -> EmMon (Fuzzi f) FuzziM ()
assign lhs rhs = fromDeepRepr $ iAssign lhs rhs

laplace :: forall f.
           Fuzzi f (FuzziM Double)
        -> Fuzzi f (FuzziM Double)
        -> Fuzzi f (FuzziM Double)
laplace width center = iLaplace width center

{-
x :: Variable Double
x = Variable ()

xx :: forall f. Fuzzi f (FuzziM Double)
xx = iDeref x

ex1 :: forall f. Mon (Fuzzi f) FuzziM (Fuzzi f ())
ex1 = assign (xx @f) (xx @f)

ex2 :: forall f. EmMon (Fuzzi f) FuzziM ()
ex2 = do
  assign xx (laplace 1.0 0.0)
  assign xx (xx + 1.0)
-}

instance Num a => Num (FuzziM a) where
  (+) = liftM2 (+)
  (*) = liftM2 (*)
  abs = fmap abs
  signum = fmap signum
  fromInteger = return . fromInteger
  negate = fmap negate

instance Integralite a => Integralite (FuzziM a) where
  idiv = liftM2 idiv
  imod = liftM2 imod

instance Fractional a => Fractional (FuzziM a) where
  (/) = liftM2 (/)
  fromRational = return . fromRational

instance Floating a => Floating (FuzziM a) where
  pi = return pi
  exp = fmap exp
  log = fmap log
  sqrt = fmap sqrt
  (**) = liftM2 (**)
  logBase = liftM2 logBase
  sin = fmap sin
  cos = fmap cos
  tan = fmap tan
  asin = fmap asin
  acos = fmap acos
  atan = fmap atan
  sinh = fmap sinh
  cosh = fmap cosh
  tanh = fmap tanh
  asinh = fmap asinh
  acosh = fmap acosh
  atanh = fmap atanh
