{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Data.DPHS.Fuzzi where

import Data.Functor.Compose
import Control.Monad
import Type.Reflection
import Data.List

import Data.DPHS.Name
import Data.DPHS.HXFunctor
import Data.DPHS.Syntax
import Data.DPHS.Syntactic
import Data.DPHS.Types

import Text.Printf
import Data.Comp.Multi
import Data.Comp.Multi.Show ()
import Data.Comp.Multi.Equality ()
import Data.Comp.Multi.Ordering (KOrd(..))
import Data.Comp.Multi.Derive

import Data.Functor.Identity

newtype FuzziM a = FuzziM { runFuzziM :: Identity a }
  deriving (Functor, Applicative, Monad)

data ExprF :: (* -> *) -> * -> * where
  -- |Dereference a variable.
  Deref :: Typeable a
        => Variable a
        -> ExprF r (FuzziM a)

  -- |Index into an array.
  Index :: r (FuzziM (Array a))
        -> r (FuzziM Int)
        -> ExprF r (FuzziM a)

  -- |Literal array value.
  ArrLit :: [r (FuzziM a)]
         -> ExprF r (FuzziM (Array a))

$(derive [makeHFunctor, makeHFoldable, makeHTraversable,
          smartConstructors, smartAConstructors]
         [''ExprF])

instance ShowHF ExprF where
  showHF (Deref (V v)) = K (show v)
  showHF (Index e idx) = K (printf "%s[%s]" (unK e) (unK idx))
  showHF (ArrLit es) = K (printf "[%s]" contents)
    where contents = (concat . intersperse ", " . map unK) es

instance EqHF ExprF where
  eqHF (Deref (v1 :: Variable a1)) (Deref (v2 :: Variable a2)) =
    case eqTypeRep (typeRep @a1) (typeRep @a2) of
      Just HRefl -> v1 == v2
      Nothing -> False

  eqHF (Index a1 idx1) (Index a2 idx2) = keq a1 a2 && keq idx1 idx2

  eqHF (ArrLit vs1) (ArrLit vs2) =
    length vs1 == length vs2 && all (uncurry keq) (zip vs1 vs2)

  eqHF _ _ = False

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

  compareHF (ArrLit _) (Deref _) = GT
  compareHF (ArrLit _) (Index _ _) = GT
  compareHF (ArrLit vs1) (ArrLit vs2) = compareList vs1 vs2

compareList :: KOrd r => [r a] -> [r b] -> Ordering
compareList []     []     = EQ
compareList (_:_)  []     = GT
compareList []     (_:_)  = LT
compareList (x:xs) (y:ys) = kcompare x y <> compareList xs ys

data ExtensionF :: (* -> *) -> * -> * where
  BMap :: r (FuzziM (Bag a))
       -> r (FuzziM a -> FuzziM b)
       -> ExtensionF r (FuzziM (Bag b))
  BSum :: Double
       -> r (FuzziM (Bag Double))
       -> ExtensionF r (FuzziM Double)
  AMap :: r (FuzziM (Array a))
       -> r (FuzziM a -> FuzziM b)
       -> ExtensionF r (FuzziM (Array b))
  Part :: Int
       -> r (FuzziM (Bag a))
       -> r (FuzziM a -> FuzziM Int)
       -> ExtensionF r (FuzziM (Array (Bag a)))

  AdvComp :: Variable Int  -- ^ iteration variable
          -> Int           -- ^ total number of iterations
          -> r (FuzziM ()) -- ^ loop body
          -> ExtensionF r (FuzziM ())

$(derive [makeHFunctor, makeHFoldable, makeHTraversable,
          makeShowHF, makeEqHF, makeOrdHF,
          smartConstructors, smartAConstructors]
         [''ExtensionF])

data PrivMechF :: (* -> *) -> * -> * where
  Laplace :: r (FuzziM Double)
          -> r (FuzziM Double)
          -> PrivMechF r (FuzziM Double)

$(derive [makeHFunctor, makeHFoldable, makeHTraversable,
          makeShowHF, makeEqHF, makeOrdHF,
          smartConstructors, smartAConstructors]
         [''PrivMechF])

data EffF :: (* -> *) -> * -> * where
  Assign :: r (FuzziM a)            -- ^ the lhs expression to be assigned
         -> r (FuzziM a)            -- ^ the rhs expression to assign to the lhs
         -> EffF r (FuzziM ())
  Branch :: r (FuzziM Bool)         -- ^ branch condition
         -> r (FuzziM ())           -- ^ true branch statements
         -> r (FuzziM ())           -- ^ false branch statements
         -> EffF r (FuzziM ())
  While  :: r (FuzziM Bool)         -- ^ loop condition
         -> r (FuzziM ())           -- ^ loop body
         -> EffF r (FuzziM ())

$(derive [makeHFunctor, makeHFoldable, makeHTraversable,
          makeShowHF, makeEqHF, makeOrdHF,
          smartConstructors, smartAConstructors]
         [''EffF])

type FuzziF = ArithF :+: CompareF :+: ExprF
              :+: PrivMechF :+: EffF :+: XLambdaF
              :+: MonadF
              :+: ExtensionF
type Fuzzi f = Context FuzziF f

type NFuzziF = ArithF :+: CompareF :+: ExprF
              :+: PrivMechF :+: EffF :+: LambdaF
              :+: MonadF
              :+: ExtensionF
type NFuzzi f = Context NFuzziF f

assign :: forall f a.
          Fuzzi f (FuzziM a)
       -> Fuzzi f (FuzziM a)
       -> EmMon (Fuzzi f) FuzziM ()
assign lhs rhs =
  fromDeepRepr $ iAssign lhs rhs

while :: forall f.
         Fuzzi f (FuzziM Bool)
      -> EmMon (Fuzzi f) FuzziM ()
      -> EmMon (Fuzzi f) FuzziM ()
while cond body =
  fromDeepRepr $ iWhile cond (toDeepRepr body)

if_ :: forall f.
       Fuzzi f (FuzziM Bool)
    -> EmMon (Fuzzi f) FuzziM ()
    -> EmMon (Fuzzi f) FuzziM ()
    -> EmMon (Fuzzi f) FuzziM ()
if_ cond ct cf =
  fromDeepRepr $ iBranch cond (toDeepRepr ct) (toDeepRepr cf)

v :: Typeable a => Variable a -> Fuzzi f (FuzziM a)
v = iDeref

vn :: Typeable a => Name -> Fuzzi f (FuzziM a)
vn = v . V

infixl 9 .!!
(.!!) :: forall f a.
         Fuzzi f (FuzziM (Array a))
      -> Fuzzi f (FuzziM Int)
      -> Fuzzi f (FuzziM a)
(.!!) = iIndex

infix 4 .=
(.=) :: forall f a.
        Fuzzi f (FuzziM a)
     -> Fuzzi f (FuzziM a)
     -> EmMon (Fuzzi f) FuzziM ()
(.=) = assign

laplace :: forall f.
           Fuzzi f (FuzziM Double)
        -> Fuzzi f (FuzziM Double)
        -> Fuzzi f (FuzziM Double)
laplace width center = iLaplace width center

bmap :: forall f a b.
        (Typeable a, Typeable b)
     => Fuzzi f (FuzziM (Bag a))
     -> (Fuzzi f (FuzziM a) -> Fuzzi f (FuzziM b))
     -> Fuzzi f (FuzziM (Bag b))
bmap input f = iBMap input (toDeepRepr f)

amap :: forall f a b.
        (Typeable a, Typeable b)
     => Fuzzi f (FuzziM (Array a))
     -> (Fuzzi f (FuzziM a) -> Fuzzi f (FuzziM b))
     -> Fuzzi f (FuzziM (Array b))
amap input f = iAMap input (toDeepRepr f)

ac :: forall f.
      Variable Int
   -> Int
   -> EmMon (Fuzzi f) FuzziM ()
   -> EmMon (Fuzzi f) FuzziM ()
ac i n iter =
  fromDeepRepr @(Fuzzi f) $ iAdvComp i n (toDeepRepr iter)

instance Num a => Num (FuzziM a) where
  (+) = liftM2 (+)
  (*) = liftM2 (*)
  abs = fmap abs
  signum = fmap signum
  fromInteger = return . fromInteger
  negate = fmap negate

instance SynBool a => SynBool (FuzziM a) where
  neg = fmap neg
  (.&&) = liftM2 (.&&)
  (.||) = liftM2 (.||)

instance SynOrd a => SynOrd (FuzziM a) where
  type Cmp (FuzziM a) = FuzziM (Cmp a)

  (.==) = liftM2 (.==)
  (./=) = liftM2 (./=)
  (.<)  = liftM2 (.<)
  (.<=) = liftM2 (.<=)
  (.>)  = liftM2 (.>)
  (.>=) = liftM2 (.>=)

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

instance HOASToNamed ExprF NFuzziF where
  hoasToNamedAlg (Deref var) = Compose . return $ iDeref var
  hoasToNamedAlg (Index e idx) = Compose $ iIndex <$> getCompose e <*> getCompose idx
  hoasToNamedAlg (ArrLit es) = Compose $ iArrLit <$> traverse getCompose es

instance HOASToNamed ExtensionF NFuzziF where
  hoasToNamedAlg (BMap input f) = Compose $ iBMap <$> getCompose input <*> getCompose f
  hoasToNamedAlg (BSum clip input) = Compose $ iBSum clip <$> getCompose input
  hoasToNamedAlg (AMap input f) = Compose $ iAMap <$> getCompose input <*> getCompose f
  hoasToNamedAlg (Part nparts input partfun) = Compose $ iPart nparts <$> getCompose input <*> getCompose partfun
  hoasToNamedAlg (AdvComp i niter body) = Compose $ iAdvComp i niter <$> getCompose body

instance HOASToNamed PrivMechF NFuzziF where
  hoasToNamedAlg (Laplace width center) = Compose $ iLaplace <$> getCompose width <*> getCompose center

instance HOASToNamed EffF NFuzziF where
  hoasToNamedAlg (Assign lhs rhs) = Compose $ iAssign <$> getCompose lhs <*> getCompose rhs
  hoasToNamedAlg (Branch cond t f) = Compose $ iBranch <$> getCompose cond <*> getCompose t <*> getCompose f
  hoasToNamedAlg (While cond body) = Compose $ iWhile <$> getCompose cond <*> getCompose body
