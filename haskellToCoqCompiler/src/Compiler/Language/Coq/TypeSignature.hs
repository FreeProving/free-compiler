-- TODO REMOVE ME

module Compiler.Language.Coq.TypeSignature where

import qualified Language.Coq.Gallina          as G

data TypeSignature = TypeSignature G.Name [G.Term]
