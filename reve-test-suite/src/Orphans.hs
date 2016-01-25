{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Orphans where

import Control.Monad.Trans.Class
import Control.Monad.Logger
import Pipes.Safe

instance MonadSafe m => MonadSafe (LoggingT m) where
  type Base (LoggingT m) = Base m
  liftBase = lift . liftBase
  register = lift . register
  release = lift . release
