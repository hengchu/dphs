{-# language TypeFamilyDependencies #-}

module Data.DPHS.SrcLoc where

import GHC.Stack
import Data.Comp.Multi.Annotation
import Data.Comp.Multi.Sum

newtype Pos = Pos {
  posSrcLoc :: Maybe SrcLoc
  }
  deriving (Eq)

instance Show Pos where
  show (Pos (Just srcloc)) = prettySrcLoc srcloc
  show (Pos Nothing) = "<unknown location>"

noPos :: Pos
noPos = Pos Nothing

fromCallStack :: CallStack -> Pos
fromCallStack stk =
  case getCallStack stk of
    (_, loc):_ -> Pos (Just loc)
    _ -> Pos Nothing

type family Annotate h p = result | result -> h p where
  Annotate (f :+: g) p = Annotate f p :+: Annotate g p
  Annotate a p = a :&: p

type WithPos f = Annotate f Pos
