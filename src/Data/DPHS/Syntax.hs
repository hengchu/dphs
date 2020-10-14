{-# OPTIONS_GHC -Wno-missing-signatures -Wno-orphans #-}

module Data.DPHS.Syntax where

import Type.Reflection hiding (App)
import Data.Functor.Compose

import Data.DPHS.Name
import Data.DPHS.HXFunctor
import Data.DPHS.Syntactic

import Data.Comp.Multi
import Data.Comp.Multi.Show ()
import Data.Comp.Multi.Equality ()
import Data.Comp.Multi.Ordering (KOrd(..))
import Data.Comp.Multi.Derive

newtype Variable a = V Name
  deriving (Show, Eq, Ord)

heq :: forall a b. (Typeable a, Typeable b) => Variable a -> Variable b -> Bool
heq va vb =
  case eqTypeRep (typeRep @a) (typeRep @b) of
    Just HRefl -> va == vb
    Nothing -> False

hcompare :: forall a b. (Typeable a, Typeable b) => Variable a -> Variable b -> Ordering
hcompare va vb =
  case eqTypeRep tr1 tr2 of
    Just HRefl -> compare va vb
    Nothing -> compare (SomeTypeRep tr1) (SomeTypeRep tr2)
  where tr1 = typeRep @a
        tr2 = typeRep @b

class Integralite a where
  idiv :: a -> a -> a
  imod :: a -> a -> a

infixr 2 .||
infixr 3 .&&
infix  4 .==, ./=, .<, .<=, .>, .>=
class SynBool a where
  neg   :: a -> a
  (.&&) :: a -> a -> a
  (.||) :: a -> a -> a

class SynBool (Cmp a) => SynOrd a where
  type Cmp a :: *

  (.==) :: a -> a -> Cmp a
  (./=) :: a -> a -> Cmp a
  (.<)  :: a -> a -> Cmp a
  (.<=) :: a -> a -> Cmp a
  (.>)  :: a -> a -> Cmp a
  (.>=) :: a -> a -> Cmp a

-- |Basic arithmetic operations.
data ArithF :: (* -> *) -> * -> * where
  IntLit  :: Num a => Integer -> ArithF r a
  FracLit :: Fractional a => Rational -> ArithF r a

  Add    :: Num a => r a -> r a -> ArithF r a
  Sub    :: Num a => r a -> r a -> ArithF r a
  Abs    :: Num a => r a -> ArithF r a
  Signum :: Num a => r a -> ArithF r a

  Mult :: Num a => r a -> r a -> ArithF r a
  Div  :: Fractional a => r a -> r a -> ArithF r a

  IDiv :: Integralite a => r a -> r a -> ArithF r a
  IMod :: Integralite a => r a -> r a -> ArithF r a

  Exp  :: Floating a => r a -> ArithF r a
  Log  :: Floating a => r a -> ArithF r a
  Sqrt :: Floating a => r a -> ArithF r a

$(derive [makeHFunctor, makeHFoldable, makeHTraversable,
          makeShowHF, makeEqHF, makeOrdHF,
          smartConstructors, smartAConstructors]
         [''ArithF])

instance ArithF :<: tgt => HOASToNamed ArithF tgt where
  hoasToNamedAlg (IntLit v) = Compose . return $ iIntLit v
  hoasToNamedAlg (FracLit v) = Compose . return $ iFracLit v
  hoasToNamedAlg (Add v1 v2) = Compose $ iAdd <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (Sub v1 v2) = Compose $ iSub <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (Abs v) = Compose $ iAbs <$> getCompose v
  hoasToNamedAlg (Signum v) = Compose $ iSignum <$> getCompose v
  hoasToNamedAlg (Mult v1 v2) = Compose $ iMult <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (Div v1 v2) = Compose $ iDiv <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (IDiv v1 v2) = Compose $ iIDiv <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (IMod v1 v2) = Compose $ iIMod <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (Exp v) = Compose $ iExp <$> getCompose v
  hoasToNamedAlg (Log v) = Compose $ iLog <$> getCompose v
  hoasToNamedAlg (Sqrt v) = Compose $ iSqrt <$> getCompose v

-- |Basic comparison and boolean operations.
data CompareF :: (* -> *) -> * -> * where
  IsEq  :: SynOrd a => r a -> r a -> CompareF r (Cmp a)
  IsNeq :: SynOrd a => r a -> r a -> CompareF r (Cmp a)
  IsLt  :: SynOrd a => r a -> r a -> CompareF r (Cmp a)
  IsLe  :: SynOrd a => r a -> r a -> CompareF r (Cmp a)
  IsGt  :: SynOrd a => r a -> r a -> CompareF r (Cmp a)
  IsGe  :: SynOrd a => r a -> r a -> CompareF r (Cmp a)

  Neg   :: SynBool bool => r bool           -> CompareF r bool
  And   :: SynBool bool => r bool -> r bool -> CompareF r bool
  Or    :: SynBool bool => r bool -> r bool -> CompareF r bool

$(derive [makeHFunctor, makeHFoldable, makeHTraversable,
          makeShowHF, makeEqHF, makeOrdHF,
          smartConstructors, smartAConstructors]
         [''CompareF])

instance CompareF :<: tgt => HOASToNamed CompareF tgt where
  hoasToNamedAlg (IsEq v1 v2) = Compose $ iIsEq <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (IsNeq v1 v2) = Compose $ iIsNeq <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (IsLt v1 v2) = Compose $ iIsLt <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (IsLe v1 v2) = Compose $ iIsLe <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (IsGt v1 v2) = Compose $ iIsGt <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (IsGe v1 v2) = Compose $ iIsGe <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (Neg v) = Compose $ iNeg <$> getCompose v
  hoasToNamedAlg (And v1 v2) = Compose $ iAnd <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (Or v1 v2) = Compose $ iOr <$> getCompose v1 <*> getCompose v2

-- |Embedded monadic syntax.
data MonadF :: (* -> *) -> * -> * where
  Bind :: (Monad m, Typeable a) => r (m a) -> r (a -> m b) -> MonadF r (m b)
  Ret  :: Monad m => r a -> MonadF r (m a)

$(derive [makeHFunctor, makeHFoldable, makeHTraversable,
          makeShowHF, makeEqHF, makeOrdHF,
          smartConstructors, smartAConstructors]
         [''MonadF])

instance MonadF :<: tgt => HOASToNamed MonadF tgt where
  hoasToNamedAlg (Bind ma kont) = Compose $ iBind <$> getCompose ma <*> getCompose kont
  hoasToNamedAlg (Ret a) = Compose $ iRet <$> getCompose a

instance Syntactic (Cxt hole lang f) (Cxt hole lang f a) where
  type DeepRepr (Cxt hole lang f a) = a
  toDeepRepr = id
  fromDeepRepr = id

-- |Shallow monadic expressions are embedded through this catch-all instance.
instance ( Syntactic (Cxt hole lang f) a,
           Typeable (DeepRepr a),
           MonadF :<: lang,
           XLambdaF :<: lang,
           Monad m,
           Typeable m
         ) => Syntactic (Cxt hole lang f) (Mon (Cxt hole lang f) m a) where
  type DeepRepr (Mon (Cxt hole lang f) m a) = m (DeepRepr a)
  toDeepRepr (Mon m) = m (Term . inj . Ret . toDeepRepr)
  fromDeepRepr m = Mon $ \k -> Term . inj $ Bind m (toDeepRepr k)

-- |Embedded lambda calculus.
data XLambdaF :: (* -> *) -> * -> * where
  XLam :: Typeable a => (r a -> r b) -> XLambdaF r (a -> b)
  XApp :: Typeable a => r (a -> b) -> r a -> XLambdaF r b
  XVar :: Typeable a => Variable a -> XLambdaF r a

instance HXFunctor XLambdaF where
  hxmap f g (XLam lam) = XLam (f . lam . g)
  hxmap f _ (XApp lam arg) = XApp (f lam) (f arg)
  hxmap _ _ (XVar var) = XVar var

-- |Shallow functions and applications are embedded through this catch-all
-- instance.
instance ( Typeable (DeepRepr a),
           Typeable (DeepRepr b),
           Syntactic (Cxt hole lang f) a,
           Syntactic (Cxt hole lang f) b,
           XLambdaF :<: lang
         ) => Syntactic (Cxt hole lang f) (a -> b) where
  type DeepRepr (a -> b) = DeepRepr a -> DeepRepr b
  toDeepRepr f = Term . inj . XLam $ toDeepRepr . f . fromDeepRepr
  fromDeepRepr f = fromDeepRepr . (Term . inj . XApp f) . toDeepRepr

-- |Named lambda calculus representation.
data LambdaF :: (* -> *) -> * -> * where
  Lam :: Typeable a => Variable a -> r b -> LambdaF r (a -> b)
  App :: Typeable a => r (a -> b) -> r a -> LambdaF r b
  Var :: Typeable a => Variable a -> LambdaF r a

instance EqHF LambdaF where
  eqHF (Lam x1 body1) (Lam x2 body2) = heq x1 x2 && keq body1 body2
  eqHF (App f1 arg1) (App f2 arg2) = keq f1 f2 && keq arg1 arg2
  eqHF (Var v1) (Var v2) = heq v1 v2
  eqHF _ _ = False

instance OrdHF LambdaF where
  compareHF (Lam x1 body1) (Lam x2 body2) =
    hcompare x1 x2 <> kcompare body1 body2
  compareHF (Lam _ _) _ = LT

  compareHF (App _ _) (Lam _ _) = GT
  compareHF (App f1 arg1) (App f2 arg2) =
    kcompare f1 f2 <> kcompare arg1 arg2
  compareHF (App _ _) (Var _) = LT

  compareHF (Var _) (Lam _ _) = GT
  compareHF (Var _) (App _ _) = GT
  compareHF (Var v1) (Var v2) = hcompare v1 v2

$(derive [makeHFunctor, makeHFoldable, makeHTraversable,
          makeShowHF,
          smartConstructors, smartAConstructors]
         [''LambdaF])

instance LambdaF :<: tgt => HOASToNamed XLambdaF tgt where
  hoasToNamedAlg (XLam f) = Compose $ do
    x <- V <$> gfresh "x"
    body <- getCompose $ f (Compose . return . iVar $ x)
    return (iLam x body)
  hoasToNamedAlg (XApp f arg) = Compose $ iApp <$> getCompose f <*> getCompose arg
  hoasToNamedAlg (XVar fv) = Compose . return $ iVar fv

instance (Num a, ArithF :<: lang) => Num (Cxt hole lang f a) where
  (+) = iAdd
  (*) = iMult
  (-) = iSub
  abs = iAbs
  signum = iSignum
  fromInteger = iIntLit

instance (Fractional a, ArithF :<: lang) => Fractional (Cxt hole lang f a) where
  (/) = iDiv
  fromRational = iFracLit

instance (Integralite a, ArithF :<: lang) => Integralite (Cxt hole lang f a) where
  idiv = iIDiv
  imod = iIMod

instance (SynBool a, CompareF :<: lang) => SynBool (Cxt hole lang f a) where
  neg = iNeg
  (.&&) = iAnd
  (.||) = iOr

instance (SynOrd a, CompareF :<: lang) => SynOrd (Cxt hole lang f a) where
  type Cmp (Cxt hole lang f a) = Cxt hole lang f (Cmp a)
  (.==) = iIsEq
  (./=) = iIsNeq
  (.<) = iIsLt
  (.<=) = iIsLe
  (.>) = iIsGt
  (.>=) = iIsGe

instance SynBool Bool where
  neg = not
  (.&&) = (&&)
  (.||) = (||)

instance SynOrd Double where
  type Cmp Double = Bool

  (.==) = (==)
  (./=) = (/=)
  (.<)  = (<)
  (.<=) = (<=)
  (.>)  = (>)
  (.>=) = (>=)

instance SynOrd Int where
  type Cmp Int = Bool

  (.==) = (==)
  (./=) = (/=)
  (.<)  = (<)
  (.<=) = (<=)
  (.>)  = (>)
  (.>=) = (>=)

instance SynOrd Integer where
  type Cmp Integer = Bool

  (.==) = (==)
  (./=) = (/=)
  (.<)  = (<)
  (.<=) = (<=)
  (.>)  = (>)
  (.>=) = (>=)
