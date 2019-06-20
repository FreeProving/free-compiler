module Compiler.Types where

data ConversionMonad
  = Option
  | Identity
  deriving (Eq, Show, Read)
