
-- | This module contains smart constructors for nodes of the Agda AST.
--   For convenience the original Agda AST is exported as well.

module FreeC.Backend.Agda.ConcreteSyntax
    ( module Agda.Syntax.Concrete
    , concretePrettyExample
    )
where

import           Agda.Syntax.Literal            ( Literal(LitNat) )

import qualified Agda.Syntax.Concrete          as Agda
import           Agda.Syntax.Concrete
import           Agda.Syntax.Concrete.Pretty    ( )
import           Agda.Syntax.Concrete.Name      ( Name(Name)
                                                , NamePart(Id)
                                                )

import           Agda.Syntax.Position           ( Range'(NoRange) )
import           Agda.Syntax.Common             ( defaultNamedArg )

import           Agda.Utils.Pretty              ( pretty )


concretePrettyExample :: String
concretePrettyExample = show . pretty $ Agda.Lam
    NoRange
    [DomainFree $ defaultNamedArg $ mkBinder_ $ Name NoRange InScope [Id "foo"]]
    (Lit $ LitNat NoRange 3)
