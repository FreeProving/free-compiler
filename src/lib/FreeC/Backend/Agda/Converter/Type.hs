module FreeC.Backend.Agda.Converter.Type
  ( convertType
  , convertFunctionType
  , convertConstructorType
  , renameAgdaTypeVar
  )
where

-- | Implements the IR to Agda translation, which applies the monadic lifting as
--   described by Abel et al. in "Verifying Haskell Programs Using Constructive
--   Type Theory".

import           Control.Monad                  ( mapM )

import qualified FreeC.Backend.Agda.Base       as Agda.Base
import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.Environment.LookupOrFail ( lookupAgdaIdentOrFail )
import           FreeC.Environment.Renamer      ( renameAndDefineAgdaTypeVar )
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter          ( Converter )

-- | Lifts a single type.
convertType :: IR.Type -> Converter Agda.Expr
convertType = dagger

-- | Functions not defined in terms lambdas (@f x = …@ not @f = \x -> …@) aren't
--   evaluated until fully applied, i.e. cannot be bottom. Therefore interleaving
--   monadic layers isn't needed.
--
--   > (τ₁ → τ₂ → … → τₙ)' = τ₁' → Free τ₂' → … → Free τₙ'
convertFunctionType :: [IR.Type] -> Converter Agda.Expr
convertFunctionType types = foldr1 Agda.fun <$> mapM dagger types

-- | Constructors aren't evaluated until fully applied. Furthermore the return
--   type of a constructor for a data type D has to be D and therefore cannot be
--   lifted.
--
--   > (τ₁ → τ₂ → … → τₙ → D)' = τ₁' → Free τ₂' → … → τₙ' → D
convertConstructorType :: [IR.Type] -> Converter Agda.Expr
convertConstructorType types =
  -- We can use the @star@ translation for the data type, because only the name
  -- and the application of type and @Size@ variables have to be translated.
  Agda.fun <$> convertFunctionType (init types) <*> star (last types)

-- | Utility function for introducing a new Agda type variable to the current
--   scope.
renameAgdaTypeVar :: IR.TypeVarDecl -> Converter Agda.Name
renameAgdaTypeVar (IR.TypeVarDecl srcSpan name) =
  Agda.unqualify <$> renameAndDefineAgdaTypeVar srcSpan name
-------------------------------------------------------------------------------
-- Translations                                                              --
-------------------------------------------------------------------------------

-- | The dagger translation as describer by Abel et al.
--   Normally the dagger translations separates mono and poly types, but the
--   polytype cases are not applicable for our IR.
--   Note: If polytypes are added in the future (e.g. for type classes) add
--   their type translation here.
--
--   > -- not applicable (polytypes)
--   > (∀α:κ.σ)’ = (α : κ’) → σ’ -- RankNTypes translate to pi types
--   > (σ ↦ τ)’ = σ’ → τ’        -- functions handling polytypes e.g.
--   >                           -- result from type class dictionary translation
--   > -- all other cases (monotypes):
--   > τ’ = m τ
dagger :: IR.Type -> Converter Agda.Expr
dagger = fmap Agda.Base.free' . star

-- | The star translation for monotypes as described by Abel et al.
--
-- > (σ τ)* = σ* τ*
-- > (σ → τ)* = σ’ → τ’
-- > C* = Ĉ @S @P
-- > α* = α
star :: IR.Type -> Converter Agda.Expr
star (IR.TypeVar s name) = Agda.Ident
  <$> lookupAgdaIdentOrFail s IR.TypeScope (IR.UnQual (IR.Ident name))
star (IR.TypeCon s name) =
  Agda.Base.freeArgs <$> lookupAgdaIdentOrFail s IR.TypeScope name
star (IR.TypeApp  _ l r) = Agda.app <$> star l <*> star r
-- At the moment this case simplifies to
-- @Agda.func <$> Agda.base.free' (dagger l) <*> Agda.base.free' (dagger r)@.
star (IR.FuncType _ l r) = Agda.fun <$> dagger l <*> dagger r
