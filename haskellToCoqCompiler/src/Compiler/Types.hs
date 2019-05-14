module Compiler.Types where

data ConversionMode
  = HelperFunction
  | FueledFunction
  deriving (Eq, Show, Read)

data ConversionMonad
  = Option
  | Identity
  deriving (Eq, Show, Read)
