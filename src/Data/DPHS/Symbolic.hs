{-# LANGUAGE CPP #-}

module Data.DPHS.Symbolic where

import qualified Data.DList as DL

import Data.DPHS.Syntax
import Data.DPHS.Name
import Data.DPHS.Precedence

import Text.PrettyPrint.ANSI.Leijen

data SExp :: * where
  SI      :: !Integer  -> SExp
  SR      :: !Rational -> SExp
  -- |A placeholder for the ith laplace sample from concrete execution.
  SLap    :: Int -> SExp -> Double -> SExp
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
  STrue   :: SExp
  SFalse  :: SExp
  deriving (Eq, Ord)

strue :: SBool
strue = SBool STrue

sfalse :: SBool
sfalse = SBool SFalse

conjunct :: Foldable t => t SBool -> SBool
conjunct = foldr (.&&) strue

disjunct :: Foldable t => t SBool -> SBool
disjunct = foldr (.||) sfalse

newtype SInt = SInt SExp
  deriving (Show, SynOrd, Num) via SExp
  deriving (Eq, Ord)

newtype SReal = SReal SExp
  deriving (Show, SynOrd, Num, Fractional) via SExp
  deriving (Eq, Ord)

newtype SBool = SBool SExp
  deriving (Show, SynBool) via SExp
  deriving (Eq, Ord)

instance Show SExp where
  showsPrec _ t = showSExp t

instance Num SExp where
  (SI 0) + other  = other
  other  + (SI 0) = other

  (SR 0) + other  = other
  other  + (SR 0) = other

  a + b           = SAdd a b

  (-) = SSub
  (*) = SMult
  abs = SAbs
  signum = SSignum
  fromInteger = SI . fromInteger

instance Fractional SExp where
  (/) = SDiv
  fromRational = SR

instance SynBool SExp where
  neg STrue  = SFalse
  neg SFalse = STrue
  neg other  = SNeg other

  STrue .&& other = other
  other .&& STrue = other
  a     .&& b     = SAnd a b

  SFalse .|| other  = other
  other  .|| SFalse = other
  a      .|| b      = SOr a b

  true  = STrue
  false = SFalse

instance SynOrd SExp where
  type Cmp SExp = SBool

  a .== b = SBool (SEq a b)
  a ./= b = SBool (SNeq a b)
  a .<= b = SBool (SLe a b)
  a .< b  = SBool (SLt a b)
  a .>= b = SBool (SGe a b)
  a .> b  = SBool (SGt a b)

data MatchResult =
  Static Bool | Symbolic SBool
  deriving (Show, Eq)

-- |'Match' is instantiated for types 'a' and 'b' that can be tested for
-- equality, either statically, or by the SMT solver.
class Match a b where
  match :: a -> b -> MatchResult

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
prettySExp (SLap i center width) _ =
  text "lap" <> parens (int i <> comma <+> prettySExp center (precInt 0) <> comma <+> double width)
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
prettySExp (SNeg t) cxt =
  text "!" <> (parensPrec cxt (prec @"!") $ prettySExp t (prec @"!"))
prettySExp (SAnd lhs rhs) cxt = IMPL_PRETTY_SEXP("&&")
prettySExp (SOr lhs rhs) cxt = IMPL_PRETTY_SEXP("||")
prettySExp STrue _ = text "True"
prettySExp SFalse _ = text "False"

showSExp :: SExp -> ShowS
showSExp t = displayS . renderPretty 1.0 80 $ yellow (prettySExp t (precInt 0))

#undef IMPL_PRETTY_SEXP

-- |The 'Semigroup' instance on 'MatchResult' takes the conjunction of two match
-- results.
instance Semigroup MatchResult where
  Static True <> a = a
  a <> Static True = a
  Static False <> _ = Static False
  _ <> Static False = Static False
  Symbolic a <> Symbolic b = Symbolic (a .&& b)

instance Match Int Int where
  match a b = Static (a == b)

instance Match Bool Bool where
  match a b = Static (a == b)

instance Match Double Double where
  match a b = Static (a == b)

instance Match Double SReal where
  match v sv = Symbolic (realToFrac v .== sv)

instance Match Int SInt where
  match v sv = Symbolic (fromIntegral v .== sv)

instance Match a b => Match (Maybe a) (Maybe b) where
  match (Just a) (Just b) = match a b
  match Nothing  Nothing  = Static True
  match _        _        = Static False

instance (Match a sa, Match b sb) => Match (a, b) (sa, sb) where
  match (va, vb) (sva, svb) =
    match va sva <> match vb svb

instance Match a b => Match [a] [b] where
  match []      []      = Static True
  match (a1:b1) (a2:b2) = match a1 a2 <> match b1 b2
  match _       _       = Static False

instance Match a b => Match (DL.DList a) (DL.DList b) where
  match (DL.Cons a1 b1) (DL.Cons a2 b2) =
    match a1 a2 <> match b1 b2
  match DL.Nil DL.Nil = Static True
  match _      _      = Static False
