{-# OPTIONS_GHC -Wno-missing-signatures -Wno-orphans #-}
{-# LANGUAGE InstanceSigs #-}

module Data.DPHS.Syntax where

import Type.Reflection hiding (App)
import Data.Functor.Compose
import GHC.Stack
import qualified Data.Foldable as Foldable

import Data.DPHS.Name
import Data.DPHS.Types
import Data.DPHS.HXFunctor
import Data.DPHS.Syntactic
import Data.DPHS.SrcLoc

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
  idiv :: HasCallStack => a -> a -> a
  imod :: HasCallStack => a -> a -> a

infixr 2 .||
infixr 3 .&&
infix  4 .==, ./=, .<, .<=, .>, .>=
class SynBool a where
  neg   :: HasCallStack => a -> a
  (.&&) :: HasCallStack => a -> a -> a
  (.||) :: HasCallStack => a -> a -> a

  true  :: a
  false :: a

class SynBool (Cmp a) => SynOrd a where
  type Cmp a :: *

  (.==) :: HasCallStack => a -> a -> Cmp a
  (./=) :: HasCallStack => a -> a -> Cmp a
  (.<)  :: HasCallStack => a -> a -> Cmp a
  (.<=) :: HasCallStack => a -> a -> Cmp a
  (.>)  :: HasCallStack => a -> a -> Cmp a
  (.>=) :: HasCallStack => a -> a -> Cmp a

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

expf :: ( ArithF :<: s
        , DistAnn s Pos f
        , Floating a
        , HasCallStack
        ) => Cxt h f x a -> Cxt h f x a
expf x = iAExp (fromCallStack callStack) x

sqrtf :: ( ArithF :<: s
         , DistAnn s Pos f
         , Floating a
         , HasCallStack
         ) => Cxt h f x a -> Cxt h f x a
sqrtf x = iASqrt (fromCallStack callStack) x

logf :: ( ArithF :<: s
        , DistAnn s Pos f
        , Floating a
        , HasCallStack
        ) => Cxt h f x a -> Cxt h f x a
logf x = iALog (fromCallStack callStack) x

-- |Container types and operations.
data ContainerF :: (* -> *) -> * -> * where
  VNil   :: ContainerF r (Vec 'O a)
  VCons  :: r a -> r (Vec n a) -> ContainerF r (Vec ('S n) a)
  VIndex :: r (Vec n a) -> Fin n -> ContainerF r a

data TupleF :: (* -> *) -> * -> * where
  Fst :: r (a, b) -> TupleF r a
  Snd :: r (a, b) -> TupleF r b
  Pair :: r a -> r b -> TupleF r (a, b)

iVNil :: ContainerF :<: f => Cxt h f x (Vec 'O a)
iVNil = inject VNil

iAVNil :: (ContainerF :<: s,
           DistAnn s p f) => p -> Cxt h f x (Vec 'O a)
iAVNil p = Term (injectA p (inj VNil))

iVCons :: ContainerF :<: f => Cxt h f x a -> Cxt h f x (Vec n a) -> Cxt h f x (Vec ('S n) a)
iVCons hd tl = inject (VCons hd tl)

iAVCons :: ( ContainerF :<: s
           , DistAnn s p f)
        => p -> Cxt h f x a -> Cxt h f x (Vec n a) -> Cxt h f x (Vec ('S n) a)
iAVCons p hd tl = Term (injectA p (inj (VCons hd tl)))

iVIndex :: ContainerF :<: f => Cxt h f x (Vec n a) -> Fin n -> Cxt h f x a
iVIndex v i = inject (VIndex v i)

iAVIndex :: ( ContainerF :<: s
            , DistAnn s p f
            ) => p -> Cxt h f x (Vec n a) -> Fin n -> Cxt h f x a
iAVIndex p v i = Term (injectA p (inj (VIndex v i)))

$(derive [makeHFunctor, makeHFoldable, makeHTraversable,
          makeShowHF
          --makeEqHF, makeOrdHF
          --smartConstructors, smartAConstructors
         ]
         [''ContainerF])

$(derive [makeHFunctor, makeHFoldable, makeHTraversable,
          makeShowHF,
          makeEqHF, makeOrdHF,
          smartConstructors, smartAConstructors
         ]
         [''TupleF])

instance
  ( SyntacticPos lang a
  , Typeable (DeepRepr' a)
  , ContainerF :<: lang
  , langPos ~ Annotate lang Pos
  , ContainerF :&: Pos :<: Annotate lang Pos
  , DistAnn lang Pos langPos
  , SingNat n
  ) => SyntacticPos lang (Vec n a) where
  type DeepRepr' (Vec n a) = Vec n (DeepRepr' a)
  toDeepRepr' Nil = iAVNil noPos
  toDeepRepr' (Cons x xs) =
    case singNat @n of
      SS n' ->
        withSingNat n' $
        withBounded (singNat @n) $
        iAVCons noPos (toDeepRepr' x) (toDeepRepr' xs)

  --fromDeepRepr' :: Term (Annotate h Pos) (DeepRepr' (Vec n a)) -> Vec n a
  fromDeepRepr' term =
    case singNat @n of
      SO -> Nil
      SS n' ->
        withSingNat n' $
        withBounded (singNat @n) $
        let idxs = [minBound .. maxBound] :: [Fin n]
        in case fromList @n $
                  map (\idx -> iAVIndex noPos term idx) idxs of
             Nothing -> error "impossible"
             Just v -> fmap fromDeepRepr' v

instance {-# OVERLAPPING #-}
  ( ContainerF :<: tgt
  , ContainerF :&: Pos :<: WithPos tgt
  , tgtPos ~ WithPos tgt
  , DistAnn tgt Pos tgtPos
  ) => HOASToNamed (ContainerF :&: Pos) tgtPos where
  hoasToNamedAlg (VNil :&: pos) = Compose . return $ iAVNil pos
  hoasToNamedAlg (VCons hd tl :&: pos) =
    Compose $ iAVCons pos <$> getCompose hd <*> getCompose tl
  hoasToNamedAlg (VIndex v i :&: pos) =
    Compose $ iAVIndex pos <$> getCompose v <*> pure i

{-
instance {-# OVERLAPPABLE #-}
  ArithF :<: tgt => HOASToNamed ArithF tgt where
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
-}

instance {-# OVERLAPPING #-}
  ( ArithF :<: tgt
  , ArithF :&: Pos :<: WithPos tgt
  , tgtPos ~ WithPos tgt
  , DistAnn tgt Pos tgtPos
  ) => HOASToNamed (ArithF :&: Pos) tgtPos where
  hoasToNamedAlg (IntLit v :&: pos) =
    Compose . return $ iAIntLit pos v
  hoasToNamedAlg (FracLit v :&: pos) =
    Compose . return $ iAFracLit pos v
  hoasToNamedAlg (Add v1 v2 :&: pos) =
    Compose $ iAAdd pos <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (Sub v1 v2 :&: pos) =
    Compose $ iASub pos <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (Abs v :&: pos) =
    Compose $ iAAbs pos <$> getCompose v
  hoasToNamedAlg (Signum v :&: pos) =
    Compose $ iASignum pos <$> getCompose v
  hoasToNamedAlg (Mult v1 v2 :&: pos) =
    Compose $ iAMult pos <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (Div v1 v2 :&: pos) =
    Compose $ iADiv pos <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (IDiv v1 v2 :&: pos) =
    Compose $ iAIDiv pos <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (IMod v1 v2 :&: pos) =
    Compose $ iAIMod pos <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (Exp v :&: pos) =
    Compose $ iAExp pos <$> getCompose v
  hoasToNamedAlg (Log v :&: pos) =
    Compose $ iALog pos <$> getCompose v
  hoasToNamedAlg (Sqrt v :&: pos) =
    Compose $ iASqrt pos <$> getCompose v

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

  CTrue  :: SynBool bool => CompareF r bool
  CFalse :: SynBool bool => CompareF r bool

iAIsEq :: (SynOrd a, CompareF :<: s, DistAnn s p f) => p -> Cxt h f x a -> Cxt h f x a -> Cxt h f x (Cmp a)
iAIsEq p a b = Term (injectA p (inj (IsEq a b)))

iAIsNeq :: (SynOrd a, CompareF :<: s, DistAnn s p f) => p -> Cxt h f x a -> Cxt h f x a -> Cxt h f x (Cmp a)
iAIsNeq p a b = Term (injectA p (inj (IsNeq a b)))

iAIsLt :: (SynOrd a, CompareF :<: s, DistAnn s p f) => p -> Cxt h f x a -> Cxt h f x a -> Cxt h f x (Cmp a)
iAIsLt p a b = Term (injectA p (inj (IsLt a b)))

iAIsLe :: (SynOrd a, CompareF :<: s, DistAnn s p f) => p -> Cxt h f x a -> Cxt h f x a -> Cxt h f x (Cmp a)
iAIsLe p a b = Term (injectA p (inj (IsLe a b)))

iAIsGt :: (SynOrd a, CompareF :<: s, DistAnn s p f) => p -> Cxt h f x a -> Cxt h f x a -> Cxt h f x (Cmp a)
iAIsGt p a b = Term (injectA p (inj (IsGt a b)))

iAIsGe :: (SynOrd a, CompareF :<: s, DistAnn s p f) => p -> Cxt h f x a -> Cxt h f x a -> Cxt h f x (Cmp a)
iAIsGe p a b = Term (injectA p (inj (IsGe a b)))

iANeg :: (SynBool a, CompareF :<: s, DistAnn s p f) => p -> Cxt h f x a -> Cxt h f x a
iANeg p a = Term (injectA p (inj (Neg a)))

iAAnd :: (SynBool a, CompareF :<: s, DistAnn s p f) => p -> Cxt h f x a -> Cxt h f x a -> Cxt h f x a
iAAnd p a b = Term (injectA p (inj (And a b)))

iAOr :: (SynBool a, CompareF :<: s, DistAnn s p f) => p -> Cxt h f x a -> Cxt h f x a -> Cxt h f x a
iAOr p a b = Term (injectA p (inj (Or a b)))

iACTrue :: (SynBool a, CompareF :<: s, DistAnn s p f) => p -> Cxt h f x a
iACTrue p = Term (injectA p (inj CTrue))

iACFalse :: (SynBool a, CompareF :<: s, DistAnn s p f) => p -> Cxt h f x a
iACFalse p = Term (injectA p (inj CFalse))

ctrue :: ( CompareF :<: h
         , CompareF :&: Pos :<: (WithPos h)
         , DistAnn h Pos (WithPos h)
         , SynBool a
         , HasCallStack
         ) => Cxt hole (WithPos h) x a
ctrue = iACTrue (fromCallStack callStack)

cfalse :: ( CompareF :<: h
         , CompareF :&: Pos :<: (WithPos h)
         , DistAnn h Pos (WithPos h)
         , SynBool a
         , HasCallStack
         ) => Cxt hole (WithPos h) x a
cfalse = iACFalse (fromCallStack callStack)

$(derive [makeHFunctor, makeHFoldable, makeHTraversable,
          makeShowHF, makeEqHF, makeOrdHF]
         [''CompareF])

instance {-# OVERLAPPING #-}
  ( CompareF :<: tgt
  , CompareF :&: Pos :<: WithPos tgt
  , tgtPos ~ WithPos tgt
  , DistAnn tgt Pos tgtPos
  ) => HOASToNamed (CompareF :&: Pos) tgtPos where
  hoasToNamedAlg (IsEq v1 v2 :&: pos) =
    Compose $ iAIsEq pos <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (IsNeq v1 v2 :&: pos) =
    Compose $ iAIsNeq pos <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (IsLt v1 v2 :&: pos) =
    Compose $ iAIsLt pos <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (IsLe v1 v2 :&: pos) =
    Compose $ iAIsLe pos <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (IsGt v1 v2 :&: pos) =
    Compose $ iAIsGt pos <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (IsGe v1 v2 :&: pos) =
    Compose $ iAIsGe pos <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (Neg v :&: pos) =
    Compose $ iANeg pos <$> getCompose v
  hoasToNamedAlg (And v1 v2 :&: pos) =
    Compose $ iAAnd pos <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (Or v1 v2 :&: pos) =
    Compose $ iAOr pos <$> getCompose v1 <*> getCompose v2
  hoasToNamedAlg (CTrue :&: pos) =
    Compose $ return $ iACTrue pos
  hoasToNamedAlg (CFalse :&: pos) =
    Compose $ return $ iACFalse pos

-- |Embedded monadic syntax.
data MonadF :: (* -> *) -> * -> * where
  Bind :: (Monad m, Typeable m, Typeable a, Typeable b) => r (m a) -> r (a -> m b) -> MonadF r (m b)
  Ret  :: (Monad m, Typeable m) => r a -> MonadF r (m a)

$(derive [makeHFunctor, makeHFoldable, makeHTraversable,
          makeShowHF, makeEqHF, makeOrdHF,
          smartConstructors, smartAConstructors]
         [''MonadF])

{-
instance MonadF :<: tgt => HOASToNamed MonadF tgt where
  hoasToNamedAlg (Bind ma kont) =
    Compose $ iBind <$> getCompose ma <*> getCompose kont
  hoasToNamedAlg (Ret a) =
    Compose $ iRet <$> getCompose a
-}

instance
  ( MonadF :<: tgt
  , MonadF :&: Pos :<: tgtPos
  , tgtPos ~ WithPos tgt
  , DistAnn tgt Pos tgtPos
  ) => HOASToNamed (MonadF :&: Pos) tgtPos where
  hoasToNamedAlg (Bind ma kont :&: pos) =
    Compose $ iABind pos <$> getCompose ma <*> getCompose kont
  hoasToNamedAlg (Ret a :&: pos) =
    Compose $ iARet pos <$> getCompose a

instance Syntactic (Cxt hole lang f) (Cxt hole lang f a) where
  type DeepRepr (Cxt hole lang f a) = a
  toDeepRepr = id
  fromDeepRepr = id

instance
  langPos ~ Annotate lang Pos => SyntacticPos lang (Term langPos a) where
  type DeepRepr' (Term langPos a) = a
  toDeepRepr' = id
  fromDeepRepr' = id

-- |Shallow monadic expressions are embedded through this catch-all instance.
instance
  ( Syntactic (Cxt hole lang f) a,
    Typeable (DeepRepr a),
    MonadF :<: lang,
    XLambdaF :<: lang,
    Monad m,
    Typeable m
  ) => Syntactic (Cxt hole lang f) (Mon (Cxt hole lang f) m a) where
  type DeepRepr (Mon (Cxt hole lang f) m a) = m (DeepRepr a)
  toDeepRepr (Mon m) = m (iRet . toDeepRepr)
  fromDeepRepr m = Mon $ iBind m . toDeepRepr

instance
  ( SyntacticPos lang a,
    Typeable (DeepRepr' a),
    MonadF :<: lang,
    XLambdaF :<: lang,
    MonadF :&: Pos :<: Annotate lang Pos,
    XLambdaF :&: Pos :<: Annotate lang Pos,
    Monad m,
    Typeable m,
    langPos ~ Annotate lang Pos,
    DistAnn lang Pos langPos
  ) => SyntacticPos lang (Mon (Term langPos) m a) where
  type DeepRepr' (Mon (Term langPos) m a) = m (DeepRepr' a)
  toDeepRepr' (Mon m) = m (iARet noPos . toDeepRepr')
  fromDeepRepr' m = Mon $ iABind noPos m . toDeepRepr'

-- |Embedded lambda calculus.
data XLambdaF :: (* -> *) -> * -> * where
  XLam :: (Typeable a, Typeable b) => (r a -> r b) -> XLambdaF r (a -> b)
  XApp :: (Typeable a, Typeable b) => r (a -> b) -> r a -> XLambdaF r b
  XVar :: Typeable a => Variable a -> XLambdaF r a

instance HXFunctor XLambdaF where
  hxmap f g (XLam lam) = XLam (f . lam . g)
  hxmap f _ (XApp lam arg) = XApp (f lam) (f arg)
  hxmap _ _ (XVar var) = XVar var

-- |Shallow functions and applications are embedded through this catch-all
-- instance.
instance
  ( Typeable (DeepRepr a),
    Typeable (DeepRepr b),
    Syntactic (Cxt hole lang f) a,
    Syntactic (Cxt hole lang f) b,
    XLambdaF :<: lang
  ) => Syntactic (Cxt hole lang f) (a -> b) where
  type DeepRepr (a -> b) = DeepRepr a -> DeepRepr b
  toDeepRepr f = Term . inj . XLam $ toDeepRepr . f . fromDeepRepr
  fromDeepRepr f = fromDeepRepr . (Term . inj . XApp f) . toDeepRepr

instance
  ( Typeable (DeepRepr' a),
    Typeable (DeepRepr' b),
    SyntacticPos lang a,
    SyntacticPos lang b,
    XLambdaF :&: Pos :<: Annotate lang Pos
  ) => SyntacticPos lang (a -> b) where
  type DeepRepr' (a -> b) = DeepRepr' a -> DeepRepr' b
  toDeepRepr' f = Term . inj $ (XLam (toDeepRepr' . f . fromDeepRepr') :&: noPos)
  fromDeepRepr' f = fromDeepRepr' . (Term . inj . \x -> XApp f x :&: noPos) . toDeepRepr'

-- |Named lambda calculus representation.
data LambdaF :: (* -> *) -> * -> * where
  Lam :: (Typeable a, Typeable b) => Variable a -> r b -> LambdaF r (a -> b)
  App :: (Typeable a, Typeable b) => r (a -> b) -> r a -> LambdaF r b
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

{-
instance {-# OVERLAPPABLE #-}
  LambdaF :<: tgt => HOASToNamed XLambdaF tgt where
  hoasToNamedAlg (XLam f) = Compose $ do
    x <- V <$> gfresh "x"
    body <- getCompose $ f (Compose . return . iVar $ x)
    return (iLam x body)
  hoasToNamedAlg (XApp f arg) = Compose $ iApp <$> getCompose f <*> getCompose arg
  hoasToNamedAlg (XVar fv) = Compose . return $ iVar fv
-}

instance {-# OVERLAPPING #-}
  ( LambdaF :<: tgt
  , LambdaF :&: Pos :<: tgtPos
  , tgtPos ~ WithPos tgt
  , DistAnn tgt Pos tgtPos
  ) => HOASToNamed (XLambdaF :&: Pos) tgtPos where
  hoasToNamedAlg (XLam f :&: pos) = Compose $ do
    x <- V <$> gfresh "x"
    body <- getCompose $ f (Compose . return . iAVar pos $ x)
    return (iALam pos x body)
  hoasToNamedAlg (XApp f arg :&: pos) = Compose $ iAApp pos <$> getCompose f <*> getCompose arg
  hoasToNamedAlg (XVar fv :&: pos) = Compose . return $ iAVar pos fv

{-
instance {-# OVERLAPPABLE #-}
  (Num a, ArithF :<: lang) => Num (Cxt hole lang f a) where
  (+) = iAdd
  (*) = iMult
  (-) = iSub
  abs = iAbs
  signum = iSignum
  fromInteger = iIntLit
-}

instance {-# OVERLAPPING #-}
  ( Num a
  , ArithF :<: lang
  , ArithF :&: Pos :<: Annotate lang Pos
  , langPos ~ Annotate lang Pos
  , DistAnn lang Pos langPos
  ) => Num (Cxt hole langPos f a) where
  (+) = iAAdd noPos
  (*) = iAMult noPos
  (-) = iASub noPos
  abs = iAAbs noPos
  signum = iASignum noPos
  fromInteger = iAIntLit noPos

{-
instance {-# OVERLAPPABLE #-}
  (Fractional a, ArithF :<: lang) => Fractional (Cxt hole lang f a) where
  (/) = iDiv
  fromRational = iFracLit
-}

instance {-# OVERLAPPING #-}
  ( Fractional a
  , ArithF :<: lang
  , ArithF :&: Pos :<: langPos
  , langPos ~ Annotate lang Pos
  , DistAnn lang Pos langPos
  ) => Fractional (Cxt hole langPos f a) where
  (/) = iADiv noPos
  fromRational = iAFracLit noPos

{-
instance {-# OVERLAPPABLE #-}
  (Integralite a, ArithF :<: lang) => Integralite (Cxt hole lang f a) where
  idiv = iIDiv
  imod = iIMod
-}

instance {-# OVERLAPPING #-}
  ( Integralite a
  , ArithF :<: lang
  , ArithF :&: Pos :<: langPos
  , langPos ~ Annotate lang Pos
  , DistAnn lang Pos langPos
  ) => Integralite (Cxt hole langPos f a) where
  idiv = iAIDiv (fromCallStack callStack)
  imod = iAIMod (fromCallStack callStack)

{-
instance {-# OVERLAPPABLE #-}
  (SynBool a, CompareF :<: lang) => SynBool (Cxt hole lang f a) where
  neg = iNeg
  (.&&) = iAnd
  (.||) = iOr
-}

instance {-# OVERLAPPING #-}
  ( SynBool a
  , CompareF :<: lang
  , CompareF :&: Pos :<: langPos
  , langPos ~ Annotate lang Pos
  , DistAnn lang Pos langPos
  ) => SynBool (Cxt hole langPos f a) where
  neg = iANeg (fromCallStack callStack)
  (.&&) = iAAnd (fromCallStack callStack)
  (.||) = iAOr (fromCallStack callStack)

  true = ctrue
  false = cfalse

{-
instance {-# OVERLAPPABLE #-}
  (SynOrd a, CompareF :<: lang) => SynOrd (Cxt hole lang f a) where
  type Cmp (Cxt hole lang f a) = Cxt hole lang f (Cmp a)
  (.==) = iIsEq
  (./=) = iIsNeq
  (.<) = iIsLt
  (.<=) = iIsLe
  (.>) = iIsGt
  (.>=) = iIsGe
-}

instance {-# OVERLAPPING #-}
  ( SynOrd a
  , CompareF :<: lang
  , CompareF :&: Pos :<: langPos
  , langPos ~ Annotate lang Pos
  , DistAnn lang Pos langPos
  ) => SynOrd (Cxt hole langPos f a) where
  type Cmp (Cxt hole langPos f a) = Cxt hole langPos f (Cmp a)
  (.==) = iAIsEq (fromCallStack callStack)
  (./=) = iAIsNeq (fromCallStack callStack)
  (.<) = iAIsLt (fromCallStack callStack)
  (.<=) = iAIsLe (fromCallStack callStack)
  (.>) = iAIsGt (fromCallStack callStack)
  (.>=) = iAIsGe (fromCallStack callStack)

instance SynBool Bool where
  neg = not
  (.&&) = (&&)
  (.||) = (||)
  true = True
  false = False

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

data Progress a = Done a | Worked a

unprogress :: Progress a -> a
unprogress (Done a) = a
unprogress (Worked a) = a

removeBindRetImpl ::
  forall h a.
  ( MonadF :&: Pos :<: h
  , LambdaF :&: Pos :<: h
  ) =>
  h (Term h) a -> Progress (h (Term h) a)
removeBindRetImpl term@(proj @(MonadF :&: Pos) -> Just (Bind m (f :: _ (x -> my)) :&: _)) =
  case proj @(LambdaF :&: Pos) (unTerm f) of
    Just (Lam ((V x) :: _ xx) body :&: _) ->
      case proj @(MonadF :&: Pos) (unTerm body) of
        Just (Ret r :&: _) ->
          case proj @(LambdaF :&: Pos) (unTerm r) of
            Just (Var ((V x') :: _ xx') :&: _) ->
              case eqTypeRep (typeRep @xx) (typeRep @xx') of
                Just HRefl -> if x == x' then Worked (unTerm m) else Done term
                _ -> Done term
            _ -> Done term
        _ -> Done term
    _ -> Done term
removeBindRetImpl term = Done term

removeBindRet :: forall h a.
  ( HFunctor h
  , MonadF :&: Pos :<: h
  , LambdaF :&: Pos :<: h
  ) => h (Compose Progress (Term h)) a -> Compose Progress (Term h) a
removeBindRet term =
  case removeBindRetImpl . hfmap (unprogress . getCompose) $ term of
    Worked t -> Compose . Worked . Term $ t
    Done t -> Compose . Done . Term $ t

removeBindRetStep :: forall h a.
  ( HFunctor h
  , MonadF :&: Pos :<: h
  , LambdaF :&: Pos :<: h
  ) => Term h a -> Progress (Term h a)
removeBindRetStep = getCompose . cata removeBindRet

removeAllBindRet :: forall h a.
  ( HFunctor h
  , MonadF :&: Pos :<: h
  , LambdaF :&: Pos :<: h
  ) => Term h a -> Term h a
removeAllBindRet = untilConvergence removeBindRetStep

untilConvergence :: (a -> Progress a) -> (a -> a)
untilConvergence f a =
  case f a of
    Worked a -> untilConvergence f a
    Done a -> a

forMon_ :: Foldable t => t a -> (a -> EmMon lang m ()) -> EmMon lang m ()
forMon_ container f =
  case Foldable.toList container of
    -- TODO: a better way to handle this is to create a term that has
    -- the unit type in the language.
    [] -> error "forMon_: empty container"
    [x] -> f x
    (x:xs) -> f x >> forMon_ xs f
