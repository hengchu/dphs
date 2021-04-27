module Data.DPHS.Examples.DPCheck where

import Data.DList (DList)
import Type.Reflection

import Data.Comp.Multi

import Data.DPHS.DPCheck
import Data.DPHS.Generator
import Data.DPHS.SrcLoc
import Data.DPHS.Symbolic
import Data.DPHS.Syntactic
import Data.DPHS.Syntax
import Data.DPHS.TEval

type DPCheck m num = ( num ~ Noise m
                     , CheckBool (Cmp num)
                     , Typeable (Cmp num)
                     , NoiseM m
                     , Typeable m
                     , Typeable num
                     , SynOrd num
                     )

trivial :: forall m num.
  DPCheck m num => EmMon (Term (WithPos DPCheckF)) m num
trivial = do
  x <- laplace 0 1.0
  if_ (x .>= 0)
      (laplace 0 1.0)
      (laplace 1 1.0)

rnmTester :: Similar [Double]
          -> ( Term (WithPos DPCheckF) (InstrDist Int)
             , Term (WithPos DPCheckF) (SymM      Int)
             )
rnmTester similar =
  ( toDeepRepr' $ rnm (map realToFrac $ left similar)
  , toDeepRepr' $ rnm (map realToFrac $ right similar)
  )

rnm :: forall m num. DPCheck m num =>
  [Term (WithPos DPCheckF) num] -> EmMon (Term (WithPos DPCheckF)) m Int
rnm []     = error "rnm: received empty input"
rnm (x:xs) = do
  xNoised <- laplace x 1.0
  rnmAux xs xNoised 0 1

rnmAux :: forall m num.
  DPCheck m num
  => [Term (WithPos DPCheckF) num]
  -> Term (WithPos DPCheckF) num
  -> Term (WithPos DPCheckF) Int
  -> Term (WithPos DPCheckF) Int
  -> EmMon (Term (WithPos DPCheckF)) m Int
rnmAux []     _       maxIdx _       = return maxIdx
rnmAux (x:xs) currMax maxIdx thisIdx = do
  noised <- laplace x 1.0
  if_ (noised .> currMax)
      (rnmAux xs noised  thisIdx (thisIdx+1))
      (rnmAux xs currMax maxIdx  (thisIdx+1))

svBooleanTester ::
  Double
  -> Int
  -> Similar [Double]
  -> ( Term (WithPos DPCheckF) (InstrDist (DList Bool))
     , Term (WithPos DPCheckF) (SymM      (DList Bool))
     )
svBooleanTester threshold count similar =
  ( toDeepRepr' $ svBoolean (fmap realToFrac $ left similar)  (realToFrac threshold) count
  , toDeepRepr' $ svBoolean (fmap realToFrac $ right similar) (realToFrac threshold) count
  )

svBoolean :: forall m num.
  DPCheck m num
  => [Term (WithPos DPCheckF) num]
  -> Term (WithPos DPCheckF) num
  -> Int
  -> EmMon (Term (WithPos DPCheckF)) m (DList Bool)
svBoolean xs thresh count = do
  thresh' <- laplace thresh 2.0
  svBooleanAux xs (4.0 * realToFrac count) thresh' count nil

svBooleanAux :: forall m num.
  DPCheck m num
  => [Term (WithPos DPCheckF) num]
  -> Double
  -> Term (WithPos DPCheckF) num
  -> Int
  -> Term (WithPos DPCheckF) (DList Bool)
  -> EmMon (Term (WithPos DPCheckF)) m (DList Bool)
svBooleanAux []     _width _ _ acc = return acc
svBooleanAux _      _width _ 0 acc = return acc
svBooleanAux (x:xs) width  t c acc = do
  xNoised <- laplace x width
  if_ (xNoised .> t)
      (svBooleanAux xs width t (c-1) (acc `snoc` ctrue))
      (svBooleanAux xs width t c     (acc `snoc` cfalse))

svBooleanUnboundedTester ::
  Double
  -> Similar [Double]
  -> ( Term (WithPos DPCheckF) (InstrDist (DList Bool))
     , Term (WithPos DPCheckF) (SymM      (DList Bool))
     )
svBooleanUnboundedTester threshold similar =
  ( toDeepRepr' $ svBooleanUnbounded (fmap realToFrac $ left similar)  (realToFrac threshold)
  , toDeepRepr' $ svBooleanUnbounded (fmap realToFrac $ right similar) (realToFrac threshold)
  )

svBooleanUnbounded :: forall m num.
  DPCheck m num
  => [Term (WithPos DPCheckF) num]
  -> Term (WithPos DPCheckF) num
  -> EmMon (Term (WithPos DPCheckF)) m (DList Bool)
svBooleanUnbounded xs thresh = do
  thresh' <- laplace thresh 1.0
  svBooleanUnboundedAux xs 1.0 thresh' nil

svBooleanUnboundedAux :: forall m num.
  DPCheck m num
  => [Term (WithPos DPCheckF) num]
  -> Double
  -> Term (WithPos DPCheckF) num
  -> Term (WithPos DPCheckF) (DList Bool)
  -> EmMon (Term (WithPos DPCheckF)) m (DList Bool)
svBooleanUnboundedAux []     _width _ acc = return acc
svBooleanUnboundedAux (x:xs) width  t acc = do
  xNoised <- laplace x width
  if_ (xNoised .> t)
      (svBooleanUnboundedAux xs width t (acc `snoc` ctrue))
      (svBooleanUnboundedAux xs width t (acc `snoc` cfalse))

svNumericTester ::
  Double
  -> Int
  -> Similar [Double]
  -> ( Term (WithPos DPCheckF) (InstrDist (DList (Maybe (InstrValue Double))))
     , Term (WithPos DPCheckF) (SymM      (DList (Maybe SReal)))
     )
svNumericTester threshold count similar =
  ( toDeepRepr' $ svNumeric (fmap realToFrac $ left similar)  (realToFrac threshold) count
  , toDeepRepr' $ svNumeric (fmap realToFrac $ right similar) (realToFrac threshold) count
  )

svNumeric :: forall m num.
  DPCheck m num
  => [Term (WithPos DPCheckF) num]
  -> Term (WithPos DPCheckF) num
  -> Int
  -> EmMon (Term (WithPos DPCheckF)) m (DList (Maybe num))
svNumeric xs thresh count = do
  thresh' <- laplace thresh 2.0
  svNumericAux xs (4.0 * realToFrac count) thresh' count nil

svNumericAux :: forall m num.
  DPCheck m num
  => [Term (WithPos DPCheckF) num]
  -> Double
  -> Term (WithPos DPCheckF) num
  -> Int
  -> Term (WithPos DPCheckF) (DList (Maybe num))
  -> EmMon (Term (WithPos DPCheckF)) m (DList (Maybe num))
svNumericAux []     _width _ _ acc = return acc
svNumericAux _      _width _ 0 acc = return acc
svNumericAux (x:xs) width  t c acc = do
  xNoised <- laplace x width
  if_ (xNoised .> t)
      (laplace x width >>= \xFreshNoised -> svNumericAux xs width t (c-1) (acc `snoc` just xFreshNoised))
      (svNumericAux xs width t c     (acc `snoc` nothing))

svNumericBugTester ::
  Double
  -> Int
  -> Similar [Double]
  -> ( Term (WithPos DPCheckF) (InstrDist (DList (Maybe (InstrValue Double))))
     , Term (WithPos DPCheckF) (SymM      (DList (Maybe SReal)))
     )
svNumericBugTester threshold count similar =
  ( toDeepRepr' $ svNumericBug (fmap realToFrac $ left similar)  (realToFrac threshold) count
  , toDeepRepr' $ svNumericBug (fmap realToFrac $ right similar) (realToFrac threshold) count
  )

svNumericBug :: forall m num.
  DPCheck m num
  => [Term (WithPos DPCheckF) num]
  -> Term (WithPos DPCheckF) num
  -> Int
  -> EmMon (Term (WithPos DPCheckF)) m (DList (Maybe num))
svNumericBug xs thresh count = do
  thresh' <- laplace thresh 2.0
  svNumericBugAux xs (4.0 * realToFrac count) thresh' count nil

svNumericBugAux :: forall m num.
  DPCheck m num
  => [Term (WithPos DPCheckF) num]
  -> Double
  -> Term (WithPos DPCheckF) num
  -> Int
  -> Term (WithPos DPCheckF) (DList (Maybe num))
  -> EmMon (Term (WithPos DPCheckF)) m (DList (Maybe num))
svNumericBugAux []     _width _ _ acc = return acc
svNumericBugAux _      _width _ 0 acc = return acc
svNumericBugAux (x:xs) width  t c acc = do
  xNoised <- laplace x width
  if_ (xNoised .> t)
      (svNumericBugAux xs width t (c-1) (acc `snoc` just xNoised))
      (svNumericBugAux xs width t c     (acc `snoc` nothing))
