module Compiler.Converter.Types where

data ConversionMonad
  = Option
  | Identity
  deriving (Eq, Show, Read)
