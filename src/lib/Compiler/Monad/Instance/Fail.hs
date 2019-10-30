{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module defines an instance of @MonadFail@ for every instance
--   of @MonadReporter@ such that internal errors (e.g. pattern matching
--   failuress) are reported properly.

module Compiler.Monad.Instance.Fail where

import           Control.Monad.Fail

import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Reporter

-- | Internal errors (e.g. pattern matching failures in @do@-blocks) are
--   cause fatal error messages to be reported.
instance (Monad r, MonadReporter r) => MonadFail r where
  fail = reportFatal . Message NoSrcSpan Internal
