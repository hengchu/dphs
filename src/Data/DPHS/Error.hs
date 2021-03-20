module Data.DPHS.Error where

import Data.DPHS.SrcLoc
import Control.Monad.Catch

data PositionAndError e = PE Pos e
  deriving (Show, Eq)

instance Exception e => Exception (PositionAndError e)

-- Wrap an exception with a source code location.
throwPos :: (Exception e, MonadThrow m) => Pos -> e -> m a
throwPos pos exc = throwM (PE pos exc)
