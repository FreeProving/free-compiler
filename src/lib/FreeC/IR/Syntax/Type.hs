-- | This module contains the definition of type expressions of our
--   intermediate language.
module FreeC.IR.Syntax.Type where

import           FreeC.IR.SrcSpan
import           FreeC.IR.Syntax.Name
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Type Expressions                                                          --
-------------------------------------------------------------------------------
-- | A type expression.
--
--   Built-in types are represented by applications of their type constructors.
--   E.g. the type @[a]@ is represented as
--   @'TypeApp' ('TypeCon' "[]") ('TypeVar' "a")@.
--   The only exception to this rule is the function type @a -> b@. It is
--   represented directly as @'FuncType' ('TypeVar' "a") ('TypeVar' "b")@.
--   The syntax @(->) a b@ is not supported at the moment. This is due to the
--   special role of functions during the lifting.
data Type
  = -- | A type variable.
    TypeVar { typeSrcSpan :: SrcSpan, typeVarIdent :: TypeVarIdent }
    -- | A type constructor.
  | TypeCon { typeSrcSpan :: SrcSpan, typeConName :: TypeConName }
    -- | A type constructor application.
  | TypeApp { typeSrcSpan :: SrcSpan, typeAppLhs :: Type, typeAppRhs :: Type }
    -- | A function type.
  | FuncType { typeSrcSpan :: SrcSpan
             , funcTypeArg :: Type
             , funcTypeRes :: Type
             }
 deriving ( Eq, Show )

-- | Creates a type constructor application type.
--
--   The given source span is inserted into the generated type constructor
--   and every generated type constructor application.
typeApp :: SrcSpan -- ^ The source span to insert into generated nodes.
        -> Type    -- ^ The partially applied type constructor.
        -> [Type]  -- ^ The type arguments to pass to the type constructor.
        -> Type
typeApp srcSpan = foldl (TypeApp srcSpan)

-- | Creates a type constructor application type for the constructor with
--   the given name.
--
--   The given source span is inserted into the generated type constructor
--   and every generated type constructor application.
typeConApp
  :: SrcSpan     -- ^ The source span to insert into generated nodes.
  -> TypeConName -- ^ The name of the type constructor to apply.
  -> [Type]      -- ^ The type arguments to pass to the type constructor.
  -> Type
typeConApp srcSpan = typeApp srcSpan . TypeCon srcSpan

-- | Creates a function type with the given argument and return types.
funcType :: SrcSpan -> [Type] -> Type -> Type
funcType srcSpan = flip (foldr (FuncType srcSpan))

-- | Splits the type of a function or constructor with the given arity
--   into the argument and return types.
--
--   This is basically the inverse of 'funcType'.
splitFuncType :: Type -> Int -> ([Type], Type)
splitFuncType (FuncType _ t1 t2) arity
  | arity > 0 = let (argTypes, returnType) = splitFuncType t2 (arity - 1)
                in (t1 : argTypes, returnType)
splitFuncType returnType _             = ([], returnType)

-- | Pretty instance for type expressions.
instance Pretty Type where
  pretty = prettyTypePred 0

-- | Pretty prints a type and adds parentheses if necessary.
--
--   The first argument indicates the precedence of the surrounding
--   context.
--    * @0@ - Top level. No parentheses are necessary.
--    * @1@ - Parentheses are needed around function types.
--    * @2@ - Parentheses are also needed around type constructor
--            applications.
prettyTypePred :: Int -> Type -> Doc

-- There are never parentheses around type variables or constructors.
prettyTypePred _ (TypeVar _ ident)  = prettyString ident
prettyTypePred _ (TypeCon _ name)   = pretty name
-- There may be parentheses around type applications and function types.
prettyTypePred n (TypeApp _ t1 t2)
  | n <= 1 = prettyTypePred 1 t1 <+> prettyTypePred 2 t2
prettyTypePred 0 (FuncType _ t1 t2)
  = prettyTypePred 1 t1 <+> prettyString "->" <+> pretty t2
prettyTypePred _ t                  = parens (pretty t)
