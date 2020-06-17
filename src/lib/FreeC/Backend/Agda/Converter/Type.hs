-- | Implements the IR to Agda translation, which applies the monadic lifting as
--   described by Abel et al. in "Verifying Haskell Programs Using Constructive
--   Type Theory".

module FreeC.Backend.Agda.Converter.Type
  ( convertType
  , convertFunctionType
  , convertConstructorType
  )
where

import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.Backend.Agda.Converter.Free
                                                ( free
                                                , applyFreeArgs
                                                )
import           FreeC.Environment.LookupOrFail ( lookupAgdaIdentOrFail )
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter          ( Converter )

-- | Lifts a single type.
convertType :: IR.Type -> Converter Agda.Expr
convertType = dagger

-- | Functions not defined in terms lambdas (@f x = …@ not @f = \x -> …@) aren't
--   evaluated until fully applied, i.e. cannot be bottom. Therefore interleaving
--   monadic layers isn't needed.
--
--   > τ₁ -> … -> τₙ -> ρ ↦ τ₁' → … → τₙ' → ρ'
convertFunctionType :: [IR.Type] -> IR.Type -> Converter Agda.Expr
convertFunctionType argTypes returnType =
  foldr Agda.fun <$> dagger returnType <*> mapM dagger argTypes

-- | Constructors aren't evaluated until fully applied. Furthermore the return
--   type of a constructor for a data type D has to be D and therefore cannot be
--   lifted.
--
--   > τ₁ -> … -> τₙ -> ρ ↦ τ₁' → … → τₙ' → ρ*
convertConstructorType :: [IR.Type] -> IR.Type -> Converter Agda.Expr
convertConstructorType argTypes returnType =
  -- We can use the @star@ translation for the data type, because only the name
  -- and the application of type and @Size@ variables have to be translated.
  foldr Agda.fun <$> star returnType <*> mapM dagger argTypes

-------------------------------------------------------------------------------
-- Translations                                                              --
-------------------------------------------------------------------------------

-- | Converts a type from IR to Agda by lifting it into the @Free@ monad.
--
--   This corresponds to the dagger translation for monotypes as described by
--   Abel et al.
--
--   > τ' = Free τ*
dagger :: IR.Type -> Converter Agda.Expr
dagger = fmap free . star

-- | Lifts a type from IR to Agda by renaming type variables and constructors,
--   adding the free arguments to constructors and lifting function types in
--   the @Free@ monad.
--
--   This corresponds to the star translation for monotypes as described by
--   Abel et al.
--
--   > (τ₁ τ₂)* = τ₁* τ₂*
--   > (τ₁ → τ₂)* = τ₁' → τ₂'
--   > C* = Ĉ Shape Position
--   > α* = α̂
star :: IR.Type -> Converter Agda.Expr
star (IR.TypeVar s name) = Agda.Ident
  <$> lookupAgdaIdentOrFail s IR.TypeScope (IR.UnQual (IR.Ident name))
star (IR.TypeCon s name) =
  applyFreeArgs <$> lookupAgdaIdentOrFail s IR.TypeScope name
star (IR.TypeApp  _ l r) = Agda.app <$> star l <*> star r
star (IR.FuncType _ l r) = Agda.fun <$> dagger l <*> dagger r
