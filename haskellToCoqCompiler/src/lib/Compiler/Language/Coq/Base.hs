-- | This module contains the Coq identifiers of types, constructors and
--   functions defined in the Base library that accompanies the compiler.

module Compiler.Language.Coq.Base where

import           Compiler.Converter.State
import qualified Compiler.Language.Coq.AST     as G
import qualified Compiler.Language.Haskell.SimpleAST
                                               as HS

-------------------------------------------------------------------------------
-- Base library import                                                       --
-------------------------------------------------------------------------------

-- | Import sentence for the @Free@ and @Prelude@ modules from the Base
--   Coq library.
imports :: G.Sentence
imports =
  G.requireImportFrom (G.ident "Base") [G.ident "Free", G.ident "Prelude"]

-------------------------------------------------------------------------------
-- Free monad                                                                --
-------------------------------------------------------------------------------

-- | The Coq identifier for the @Free@ monad.
free :: G.Qualid
free = G.bare "Free"

-- | The Coq identifier for the @pure@ constructor of the @Free@ monad.
freePureCon :: G.Qualid
freePureCon = G.bare "pure"

-- | The Coq identifier for the @impure@ constructor of the @Free@ monad.
freeImpureCon :: G.Qualid
freeImpureCon = G.bare "impure"

-- | The Coq identifier for the @>>=@ operator of the @Free@ monad.
--
--   TODO does the pretty printer handle this right (e.g. w.r.t. precedence)?
freeBind :: G.Qualid
freeBind = G.bare "op_>>=__"

-- | The names and types of the parameters that must be passed to the @Free@
--   monad. These parameters are added automatically to every defined type and
--   function.
freeArgs :: [(G.Qualid, G.Term)]
freeArgs =
  [ (G.bare "Shape", G.Sort G.Type)
  , (G.bare "Pos", G.Arrow (G.Qualid (G.bare "Shape")) (G.Sort G.Type))
  ]

-------------------------------------------------------------------------------
-- Partiality                                                                --
-------------------------------------------------------------------------------

-- | The identifier for the error term @undefined@.
partialUndefined :: G.Qualid
partialUndefined = G.bare "undefined"

-- | The identifier for the error term @error@.
partialError :: G.Qualid
partialError = G.bare "error"

-------------------------------------------------------------------------------
-- Reserved identifiers                                                      --
-------------------------------------------------------------------------------

-- | All Coq identifiers that are reserved for the Base library.
--
--   This does only include identifiers without corresponding Haskell name.
reservedIdents :: [G.Qualid]
reservedIdents =
  [ -- Free monad
    free
    , freePureCon
    , freeImpureCon
    -- Partiality
    , partialUndefined
    , partialError
    ]
    ++ map fst freeArgs

-------------------------------------------------------------------------------
-- Predefined data types                                                     --
-------------------------------------------------------------------------------

-- | Populates the given environment with the predefined data types from
--   the @Prelude@ module in the Base Coq library.
predefine :: Environment -> Environment
predefine =
  predefineBool . predefineInt . predefineList . predefinePair . predefineUnit

-- | Populates the given environment with the predefined @Bool@ data type,
--   its (smart) constructors and predefined operations.
predefineBool :: Environment -> Environment
predefineBool =
  defineTypeCon (HS.Ident "Bool") 0 (G.bare "Bool")
    . defineCon (HS.Ident "True")  0 (G.bare "true")  (G.bare "True_")
    . defineCon (HS.Ident "False") 0 (G.bare "false") (G.bare "False_")
    . defineFunc (HS.Symbol "&&") 2 (G.bare "andBool")
    . defineFunc (HS.Symbol "||") 2 (G.bare "orBool")

-- | Populates the given environment with the predefined @Int@ data type and
--   its operations.
predefineInt :: Environment -> Environment
predefineInt =
  defineTypeCon (HS.Ident "Int") 0 (G.bare "Int")
    . defineFunc (HS.Symbol "+")     2 (G.bare "addInt")
    . defineFunc (HS.Symbol "-")     2 (G.bare "subInt")
    . defineFunc (HS.Symbol "*")     2 (G.bare "mulInt")
    . defineFunc (HS.Symbol "^")     2 (G.bare "powInt")
    . defineFunc (HS.Symbol "<=")    2 (G.bare "leInt")
    . defineFunc (HS.Symbol "<")     2 (G.bare "ltInt")
    . defineFunc (HS.Symbol "==")    2 (G.bare "eqInt")
    . defineFunc (HS.Symbol "/=")    2 (G.bare "neqInt")
    . defineFunc (HS.Symbol ">=")    2 (G.bare "geInt")
    . defineFunc (HS.Symbol ">")     2 (G.bare "gtInt")
    . defineFunc (HS.Ident "negate") 1 negateOp

-- | The Coq identifier for the predefined negation operation.
--
--   'predefineInt' associates the Haskell identifier @negate@ with this Coq
--   identifier already, but we still need this identifier to refer to @negate@
--   when translating the prefix negation operator. This is because we do not
--   support qualified identifiers but the user may shadow @negate@ with a
--   local variable or custom function.
negateOp :: G.Qualid
negateOp = G.bare "negate"

-- | Populates the given environment with the predefined list data type and
--   its (smart) constructors.
predefineList :: Environment -> Environment
predefineList =
  defineTypeCon HS.listTypeConName 1 (G.bare "List")
    . defineCon HS.nilConName  0 (G.bare "nil")  (G.bare "Nil")
    . defineCon HS.consConName 2 (G.bare "cons") (G.bare "Cons")

-- | Populates the given environment with the predefined pair data type and
--   its (smart) constructor.
predefinePair :: Environment -> Environment
predefinePair = defineTypeCon HS.pairTypeConName 2 (G.bare "Pair")
  . defineCon HS.pairConName 2 (G.bare "pair_") (G.bare "Pair_")

-- | Populate sthe given environment with the predefined unit data type and
--   its (smart) constructor.
predefineUnit :: Environment -> Environment
predefineUnit = defineTypeCon HS.unitTypeConName 0 (G.bare "Unit")
  . defineCon HS.unitConName 0 (G.bare "tt") (G.bare "Tt")
