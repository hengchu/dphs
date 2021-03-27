{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.DPHS.Precedence where

import qualified GHC.TypeLits as GHC

data Prec = P Int Int
  deriving (Show, Eq, Ord)

precInt :: Int -> Prec
precInt p = P p 0

data Assoc = L | R | NA
  deriving (Show, Eq, Ord)

pBinOpR :: Prec -> Assoc -> Prec
pBinOpR (P p l) L  = P p (l+1)
pBinOpR p R  = p
pBinOpR p NA = p

pBinOpL :: Prec -> Assoc -> Prec
pBinOpL p L = p
pBinOpL (P p l) R = P p (l+1)
pBinOpL p NA = p

class KnownOperator (op :: GHC.Symbol) where
  prec   :: Prec
  fixity :: Assoc

instance KnownOperator "+" where
  prec = precInt 600
  fixity = L

instance KnownOperator "-" where
  prec = precInt 600
  fixity = L

instance KnownOperator "*" where
  prec = precInt 700
  fixity = L

instance KnownOperator "/" where
  prec = precInt 700
  fixity = L

instance KnownOperator "app" where
  prec = precInt 1200
  fixity = NA

instance KnownOperator "<" where
  prec = precInt 400
  fixity = NA

instance KnownOperator "<=" where
  prec = precInt 400
  fixity = NA

instance KnownOperator ">" where
  prec = precInt 400
  fixity = NA

instance KnownOperator ">=" where
  prec = precInt 400
  fixity = NA

instance KnownOperator "!=" where
  prec = precInt 400
  fixity = NA

instance KnownOperator "==" where
  prec = precInt 400
  fixity = NA

instance KnownOperator "not" where
  prec = precInt 300
  fixity = NA

instance KnownOperator "&&" where
  prec = precInt 200
  fixity = L

instance KnownOperator "||" where
  prec = precInt 100
  fixity = L

type family UnknownOp s where
  UnknownOp s = ('GHC.Text "Unknown operator: ") 'GHC.:<>: ('GHC.Text s)

instance {-# OVERLAPPABLE #-}
  GHC.TypeError (UnknownOp s) =>
  KnownOperator s where
  prec = error "not implemented"
  fixity = error "not implemented"
