-- | This module contains the names of built-in data types and operations
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

import qualified FreeC.IR.Syntax.Name          as IR

-------------------------------------------------------------------------------
-- Names of predefined modules                                               --
-------------------------------------------------------------------------------

-- | The name of the @Prelude@ module.
--
--   TODO once @import ... as ...@ is supported, the @Prelude@ could be
--        renamed by the user.
modName :: IR.ModName
modName = "Prelude"

-------------------------------------------------------------------------------
-- Names of predefined type constructors                                     --
-------------------------------------------------------------------------------

-- | The name of the unit type constructor.
unitTypeConName :: IR.TypeConName
unitTypeConName = IR.Qual modName (IR.Symbol "")

-- | The name of the @n@-ary tuple type constructor.
tupleTypeConName :: Int -> IR.TypeConName
tupleTypeConName n = IR.Qual modName (IR.Symbol (replicate (n - 1) ','))

-- | The name of the list type constructor.
listTypeConName :: IR.TypeConName
listTypeConName = IR.Qual modName (IR.Symbol "[]")

-------------------------------------------------------------------------------
-- Names of predefined data constructors                                     --
-------------------------------------------------------------------------------

-- | Name of the unit data constructor.
unitConName :: IR.ConName
unitConName = IR.Qual modName (IR.Symbol "")

-- | The name of the empty list data constructor.
nilConName :: IR.ConName
nilConName = IR.Qual modName (IR.Symbol "[]")

-- | The name of the non-empty list data constructor.
consConName :: IR.ConName
consConName = IR.Qual modName (IR.Symbol ":")

-- | The name of the @n@-ary tuple data constructor.
tupleConName :: Int -> IR.ConName
tupleConName n = IR.Qual modName (IR.Symbol (replicate (n - 1) ','))

-------------------------------------------------------------------------------
-- Names of special predefined types and operators                           --
-------------------------------------------------------------------------------

-- | When inferring the type of integer literals this is the type to infer.
integerTypeConName :: IR.TypeConName
integerTypeConName = IR.Qual modName (IR.Ident "Integer")

-- | When inferring the type of @if@ expressions this is the type to infer
--   for the condition.
boolTypeConName :: IR.TypeConName
boolTypeConName = IR.Qual modName (IR.Ident "Bool")

-- | The unary prefix operator @-@ is translated to the application of the
--   @negate@ function.
negateOpName :: IR.VarName
negateOpName = IR.Qual modName (IR.Ident "negate")

-------------------------------------------------------------------------------
-- Names of error terms                                                      --
-------------------------------------------------------------------------------

-- | The name of the @error@ function.
errorFuncName :: IR.VarName
errorFuncName = IR.Qual modName (IR.Ident "error")

-- | The name of the @undefined@ function.
undefinedFuncName :: IR.VarName
undefinedFuncName = IR.Qual modName (IR.Ident "undefined")
