{-# OPTIONS_GHC -Wno-missing-signatures -Wno-orphans #-}

module Data.DPHS.Syntax where

import Type.Reflection

import Data.DPHS.Name
import Data.DPHS.HXFunctor
import Data.DPHS.Syntactic

import Data.Comp.Multi
import Data.Comp.Multi.Show ()
import Data.Comp.Multi.Equality ()
import Data.Comp.Multi.Ordering ()
import Data.Comp.Multi.Derive

newtype Variable a = Variable Name
  deriving (Show, Eq, Ord)

class Integralite a where
  idiv :: a -> a -> a
  imod :: a -> a -> a

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
          makeShowHF, --makeEqHF, makeOrdHF,
          smartConstructors, smartAConstructors]
         [''ArithF])

-- |Embedded monadic syntax.
data XMonadF :: (* -> *) -> * -> * where
  XBind :: Monad m => r (m a) -> (r a -> r (m b)) -> XMonadF r (m b)
  XRet  :: Monad m => r a -> XMonadF r (m a)

instance HXFunctor XMonadF where
  hxmap f g (XBind ma k) = XBind (f ma) (f . k . g)
  hxmap f _ (XRet a)     = XRet (f a)

instance Syntactic (Cxt hole lang f) (Cxt hole lang f a) where
  type DeepRepr (Cxt hole lang f a) = a
  toDeepRepr = id
  fromDeepRepr = id

-- |Shallow monadic expressions are embedded through this catch-all instance.
instance ( Syntactic (Cxt hole lang f) a,
           Typeable (DeepRepr a),
           XMonadF :<: lang,
           Monad m
         ) => Syntactic (Cxt hole lang f) (Mon (Cxt hole lang f) m a) where
  type DeepRepr (Mon (Cxt hole lang f) m a) = m (DeepRepr a)
  toDeepRepr (Mon m) = m (Term . inj . XRet . toDeepRepr)
  fromDeepRepr m = Mon $ \k -> Term . inj $ XBind m (k . fromDeepRepr)

-- |Embedded lambda calculus.
data XLambdaF :: (* -> *) -> * -> * where
  XLam :: (r a -> r b) -> XLambdaF r (a -> b)
  XApp :: r (a -> b) -> r a -> XLambdaF r b
  XVar :: Variable a -> XLambdaF r a

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

-- |Named monadic expression representation.
data MonadF :: (* -> *) -> * -> * where
  Bind :: Monad m => r (m a) -> Variable a -> r (m b) -> MonadF r (m b)
  Ret  :: Monad m => r a -> MonadF r (m a)

$(derive [makeHFunctor, makeHFoldable, makeHTraversable,
          makeShowHF, --makeEqHF, makeOrdHF,
          smartConstructors, smartAConstructors]
         [''MonadF])

-- |Named lambda calculus representation.
data LambdaF :: (* -> *) -> * -> * where
  Lam :: Variable a -> r b -> LambdaF r (a -> b)
  App :: r (a -> b) -> r a -> LambdaF r b
  Var :: Variable a -> LambdaF r a

$(derive [makeHFunctor, makeHFoldable, makeHTraversable,
          makeShowHF, --makeEqHF, makeOrdHF,
          smartConstructors, smartAConstructors]
         [''LambdaF])

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
