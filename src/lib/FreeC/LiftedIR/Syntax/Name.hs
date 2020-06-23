-- | This module reexports the data types for names from "FreeC.IR.Syntax.Name".

module FreeC.LiftedIR.Syntax.Name
  ( IR.Name(..)
  , IR.QName(..)
    -- * Value Level Names
  , IR.ConName
  , IR.VarName
    -- * Type Level Names
  , IR.TypeVarIdent
  , IR.TypeConName
  )
where

import qualified FreeC.IR.Syntax               as IR
