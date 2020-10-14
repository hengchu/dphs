module Data.DPHS.Name where

import Data.String
import Data.Text
import Optics
import Text.Printf
import qualified Data.Map.Strict as M
import Data.Semigroup

data Name = N Text (Maybe Int)
  deriving (Eq, Ord)

type NameMap = M.Map Text Int

data NameState
  = NameState
      { -- | the currently in-scope global names
        nameStateGlobals :: NameMap,
        -- | the currently in-scope local names
        nameStateLocals :: [NameMap]
      }
  deriving (Show, Eq, Ord)

makeFieldLabels ''NameState

empty :: NameState
empty = NameState M.empty []

gfreshAppend :: FreshM m => Name -> Text -> m Name
gfreshAppend (N b _) postfix =
  gfresh $ b <> postfix

class Monad m => FreshM m where
  getNameState :: m NameState
  modifyNameState :: (NameState -> NameState) -> m ()

  -- | Get a globally fresh name.
  gfresh :: Text -> m Name
  gfresh hint = do
    ns <- getNameState
    let gnames = ns ^. #globals
    let lcxts = ns ^. #locals
    let allCxts = gnames : lcxts
    let nextNameId = foldMap ((fmap Max) . M.lookup hint) allCxts
    case fmap getMax nextNameId of
      Nothing -> do
        modifyNameState (\st -> st & #globals %~ M.insert hint 1)
        modifyNameState (\st -> st & #locals %~ Prelude.map (M.insert hint 1))
        return $ N hint (Just 0)
      Just nextIdx -> do
        modifyNameState (\st -> st & #globals %~ M.insert hint (nextIdx + 1))
        modifyNameState (\st -> st & #locals %~ Prelude.map (M.insert hint (nextIdx + 1)))
        return $ N hint (Just nextIdx)

  -- | Enter a new locally fresh context.
  lpush :: m ()
  lpush = do
    ns <- getNameState
    let gnames = ns ^. #globals
    let lcxts = ns ^. #locals
    case lcxts of
      [] -> modifyNameState (\st -> st & #locals %~ (gnames :))
      (c : _) -> modifyNameState (\st -> st & #locals %~ (c :))

  -- | Exit the last locally fresh context.
  lpop :: m ()
  lpop = do
    ns <- getNameState
    let lcxts = ns ^. #locals
    case lcxts of
      [] -> error "lpop: no pushed contexts!"
      (_ : cs) -> modifyNameState (\st -> st & #locals %~ (const cs))

  -- | Get a locally fresh name.
  lfresh :: Text -> m Name
  lfresh hint = do
    ns <- getNameState
    let lcxts = ns ^. #locals
    case lcxts of
      [] -> error "lfresh: no pushed contexts!"
      (c : cs) -> case M.lookup hint c of
        Nothing -> do
          let c' = M.insert hint 1 c
          modifyNameState (\st -> st & #locals %~ (const $ c' : cs))
          return $ N hint (Just 0)
        Just nextIdx -> do
          let c' = M.insert hint (nextIdx + 1) c
          modifyNameState (\st -> st & #locals %~ (const $ c' : cs))
          return $ N hint (Just nextIdx)

instance Show Name where
  show (N prefix (Just num)) = printf "%s_%d" prefix num
  show (N prefix Nothing) = printf "%s" prefix

instance Read Name where
  readsPrec prec str =
    let (prefix, remainder) = Prelude.span (/= '_') str
    in case remainder of
         []           -> [(N (pack prefix) Nothing, [])]
         ('_':numStr) ->
           case readsPrec @Int prec numStr of
             [] -> []
             xs -> [(N (pack prefix) (Just d), r) | (d, r) <- xs]
         _            -> []

instance IsString Name where
  fromString = read
