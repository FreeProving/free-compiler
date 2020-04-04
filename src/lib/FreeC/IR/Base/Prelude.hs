-- | This module contains the names of build-in data types and operations
--   from the @Prelude@ module that are needed for code generation.
--
--   For example, to infer the type of integer literals, we have to know
--   the name of the @Integer@ data type and to desugar list literals
--   we have to know the names of the list constructors.
--
--   However, this module contains only names, the actual environment
--   entries are defined in the module interface file of the @Prelude@.
--   This way, the @Prelude@ and the compiler are decoupled from each
--   other. Even though the names listed in this module are not allowed
--   to be changed, additional functions can be added to the @Prelude@
--   without rebuilding the compiler.

module FreeC.IR.Base.Prelude where

import qualified FreeC.IR.Syntax.Name          as HS

-------------------------------------------------------------------------------
-- Names of predefined modules                                               --
-------------------------------------------------------------------------------

-- | The name of the @Prelude@ module.
--
--   TODO once @import ... as ...@ is supported, the @Prelude@ could be
--        renamed by the user.
modName :: HS.ModName
modName = "Prelude"

-------------------------------------------------------------------------------
-- Names of predefined type constructors                                     --
-------------------------------------------------------------------------------

-- | The name of the unit type constructor.
unitTypeConName :: HS.TypeConName
unitTypeConName = HS.Qual modName (HS.Symbol "")

-- | The name of the @n@-ary tuple type constructor.
tupleTypeConName :: Int -> HS.TypeConName
tupleTypeConName n = HS.Qual modName (HS.Symbol (replicate (n - 1) ','))

-- | The name of the list type constructor.
listTypeConName :: HS.TypeConName
listTypeConName = HS.Qual modName (HS.Symbol "[]")

-------------------------------------------------------------------------------
-- Names of predefined data constructors                                     --
-------------------------------------------------------------------------------

-- | Name of the unit data constructor.
unitConName :: HS.ConName
unitConName = HS.Qual modName (HS.Symbol "")

-- | The name of the empty list data constructor.
nilConName :: HS.ConName
nilConName = HS.Qual modName (HS.Symbol "[]")

-- | The name of the non empty list data constructor.
consConName :: HS.ConName
consConName = HS.Qual modName (HS.Symbol ":")

-- | The name of the @n@-ary tuple data constructor.
tupleConName :: Int -> HS.ConName
tupleConName n = HS.Qual modName (HS.Symbol (replicate (n - 1) ','))

-------------------------------------------------------------------------------
-- Names of special predefined types and operators                           --
-------------------------------------------------------------------------------

-- | When inferring the type of integer literals this is the type to infer.
integerTypeConName :: HS.TypeConName
integerTypeConName = HS.Qual modName (HS.Ident "Integer")

-- | When inferring the type of @if@ expressions this is the type to infer
--   for the condition.
boolTypeConName :: HS.TypeConName
boolTypeConName = HS.Qual modName (HS.Ident "Bool")

-- | The unary prefix operator @-@ is translated to the application of the
--   @negate@ function.
negateOpName :: HS.VarName
negateOpName = HS.Qual modName (HS.Ident "negate")

-------------------------------------------------------------------------------
-- Names of error terms                                                      --
-------------------------------------------------------------------------------

-- | The name of the @error@ function.
errorFuncName :: HS.VarName
errorFuncName = HS.Qual modName (HS.Ident "error")

-- | The name of the @undefined@ function.
undefinedFuncName :: HS.VarName
undefinedFuncName = HS.Qual modName (HS.Ident "undefined")
