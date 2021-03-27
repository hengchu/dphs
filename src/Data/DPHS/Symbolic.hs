{-# LANGUAGE CPP #-}

module Data.DPHS.Symbolic where

import Data.DPHS.Syntax
import Data.DPHS.Name
import Data.DPHS.Precedence

import Text.PrettyPrint.ANSI.Leijen

data SExp :: * where
  SI      :: Integer  -> SExp
  SR      :: Rational -> SExp
  -- |A placeholder for the ith laplace sample from concrete execution.
  SLap    :: Int -> Double -> SExp
  SVar    :: Name -> SExp
  SAdd    :: SExp -> SExp -> SExp
  SSub    :: SExp -> SExp -> SExp
  SDiv    :: SExp -> SExp -> SExp
  SMult   :: SExp -> SExp -> SExp
  SAbs    :: SExp -> SExp
  SSignum :: SExp -> SExp
  SEq     :: SExp -> SExp -> SExp
  SNeq    :: SExp -> SExp -> SExp
  SLt     :: SExp -> SExp -> SExp
  SLe     :: SExp -> SExp -> SExp
  SGt     :: SExp -> SExp -> SExp
  SGe     :: SExp -> SExp -> SExp
  SNeg    :: SExp -> SExp
  SAnd    :: SExp -> SExp -> SExp
  SOr     :: SExp -> SExp -> SExp
  deriving (Eq)

newtype SInt = SInt SExp
  deriving (Show, SynOrd, Num) via SExp
  deriving (Eq)

newtype SReal = SReal SExp
  deriving (Show, SynOrd, Num, Fractional) via SExp
  deriving (Eq)

newtype SBool = SBool SExp
  deriving (Show, SynBool) via SExp
  deriving (Eq)

instance Show SExp where
  showsPrec _ t = showSExp t

instance Num SExp where
  (+) = SAdd
  (-) = SSub
  (*) = SMult
  abs = SAbs
  signum = SSignum
  fromInteger = SI . fromInteger

instance Fractional SExp where
  (/) = SDiv
  fromRational = SR

instance SynBool SExp where
  neg = SNeg
  (.&&) = SAnd
  (.||) = SOr

instance SynOrd SExp where
  type Cmp SExp = SBool

  a .== b = SBool (SEq a b)
  a ./= b = SBool (SNeq a b)
  a .<= b = SBool (SLe a b)
  a .< b  = SBool (SLt a b)
  a .>= b = SBool (SGe a b)
  a .> b  = SBool (SGt a b)

parensPrec :: Prec -> Prec -> Doc -> Doc
parensPrec cxt op doc =
  if cxt > op then parens doc else doc

#define IMPL_PRETTY_SEXP(op) \
  parensPrec cxt (prec @op) $ \
  prettySExp lhs (prec @op) <+> text op <+> \
  prettySExp rhs (pBinOpR (prec @op) (fixity @op))

prettySExp :: SExp -> Prec -> Doc
prettySExp (SI v) _ = integer v
prettySExp (SR v) _ = double (realToFrac v)
prettySExp (SLap i width) _ = text "lap_" <> int i <> text "@" <> double width
prettySExp (SVar x) _ = string (show x)
prettySExp (SAdd lhs rhs) cxt = IMPL_PRETTY_SEXP("+")
prettySExp (SSub lhs rhs) cxt = IMPL_PRETTY_SEXP("-")
prettySExp (SDiv lhs rhs) cxt = IMPL_PRETTY_SEXP("/")
prettySExp (SMult lhs rhs) cxt = IMPL_PRETTY_SEXP("*")
prettySExp (SAbs t) _ =
  text "abs" <> (parens $ prettySExp t (precInt 0))
prettySExp (SSignum t) _ =
  text "signum" <> (parens $ prettySExp t (precInt 0))
prettySExp (SEq lhs rhs) cxt = IMPL_PRETTY_SEXP("==")
prettySExp (SNeq lhs rhs) cxt = IMPL_PRETTY_SEXP("!=")
prettySExp (SLt lhs rhs) cxt = IMPL_PRETTY_SEXP("<")
prettySExp (SLe lhs rhs) cxt = IMPL_PRETTY_SEXP("<=")
prettySExp (SGt lhs rhs) cxt = IMPL_PRETTY_SEXP(">")
prettySExp (SGe lhs rhs) cxt = IMPL_PRETTY_SEXP(">=")
prettySExp (SNeg t) cxt = text "-" <> prettySExp t cxt
prettySExp (SAnd lhs rhs) cxt = IMPL_PRETTY_SEXP("&&")
prettySExp (SOr lhs rhs) cxt = IMPL_PRETTY_SEXP("||")

showSExp :: SExp -> ShowS
showSExp t = displayS . renderPretty 1.0 80 $ yellow (prettySExp t (precInt 0)) 

#undef IMPL_PRETTY_SEXP
