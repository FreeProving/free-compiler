-- | This module contains the Coq identifiers of types, constructors and
--   functions defined in the Base library that accompanies the compiler.

module Compiler.Language.Coq.Base where

import           Compiler.Converter.State
import           Compiler.Language.Coq.AST     as G
import           Compiler.Language.Haskell.SimpleAST
                                               as HS

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

-- | The names and types of the parameters that must be passed to the @Free@
--   monad. These parameters are added automatically to every defined type and
--   function.
freeArgs :: [(G.Qualid, G.Term)]
freeArgs =
  [ (G.bare "Shape", G.Sort G.Type)
  , (G.bare "Pos", G.Arrow (G.Qualid (G.bare "Shape")) (G.Sort G.Type))
  ]

-- | All Coq identifiers that are reserved for the Base library.
--
--   This does only include identifiers without corresponding Haskell name.
reservedIdents :: [G.Qualid]
reservedIdents = [free, freePureCon, freeImpureCon] ++ map fst freeArgs

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
  defineTypeCon (HS.Ident "Bool") (bare "Bool")
    . defineCon (HS.Ident "True")  (bare "true")  (bare "True_")
    . defineCon (HS.Ident "False") (bare "false") (bare "False_")
    . defineVar (HS.Symbol "&&") (bare "andBool")
    . defineVar (HS.Symbol "||") (bare "orBool")

-- | Populates the given environment with the predefined @Int@ data type and
--   its operations.
predefineInt :: Environment -> Environment
predefineInt =
  defineTypeCon (HS.Ident "Int") (bare "Int")
    . defineVar (HS.Symbol "+")      (bare "addInt")
    . defineVar (HS.Symbol "-")      (bare "subInt")
    . defineVar (HS.Symbol "*")      (bare "mulInt")
    . defineVar (HS.Symbol "^")      (bare "powInt")
    . defineVar (HS.Symbol "<=")     (bare "leInt")
    . defineVar (HS.Symbol "<")      (bare "ltInt")
    . defineVar (HS.Symbol "==")     (bare "eqInt")
    . defineVar (HS.Symbol "/=")     (bare "neqInt")
    . defineVar (HS.Symbol ">=")     (bare "geInt")
    . defineVar (HS.Symbol ">")      (bare "gtInt")
    . defineVar (HS.Symbol "negate") (bare "negate")

-- | Populates the given environment with the predefined list data type and
--   its (smart) constructors.
predefineList :: Environment -> Environment
predefineList =
  defineTypeCon HS.listTypeConName (bare "List")
    . defineCon HS.nilConName  (bare "nil")  (bare "Nil")
    . defineCon HS.consConName (bare "cons") (bare "Cons")

-- | Populates the given environment with the predefined pair data type and
--   its (smart) constructor.
predefinePair :: Environment -> Environment
predefinePair = defineTypeCon HS.pairTypeConName (bare "Pair")
  . defineCon HS.pairConName (bare "pair_") (bare "Pair_")

-- | Populate sthe given environment with the predefined unit data type and
--   its (smart) constructor.
predefineUnit :: Environment -> Environment
predefineUnit = defineTypeCon HS.unitTypeConName (bare "Unit")
  . defineCon HS.unitConName (bare "tt") (bare "Tt")
