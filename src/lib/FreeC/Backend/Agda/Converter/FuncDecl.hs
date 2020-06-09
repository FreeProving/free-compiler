module FreeC.Backend.Agda.Converter.FuncDecl
  ( convertFuncDecl
  )
where

import           Prelude                 hiding ( mod )

import           Data.Function                  ( on )
import           Data.List.Extra                ( snoc )
import           Data.Maybe                     ( fromJust )

import qualified FreeC.Backend.Agda.Syntax     as Agda
import qualified FreeC.Backend.Agda.Base       as Agda.Base
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter          ( Converter
                                                , inEnv
                                                )
import           FreeC.Environment              ( lookupAgdaIdent )
import           FreeC.Environment.LookupOrFail ( lookupAgdaIdentOrFail )


-- | Converts the given function declarations. Returns the declarations for the
--   type signature and the definition (TODO).
convertFuncDecl :: IR.FuncDecl -> Converter [Agda.Declaration]
convertFuncDecl decl = sequence [convertSignature decl]

-- | Converts the type signature of the given function to an Agda type
--   declaration.
convertSignature :: IR.FuncDecl -> Converter Agda.Declaration
convertSignature (IR.FuncDecl _ ident tVars args retType _) =
  Agda.funcSig <$> lookupIdent ident <*> convertFunc_ tVars types
  where types = (IR.varPatType <$> args) `snoc` retType

-- | Looks up the name of a Haskell function in the environment and converts it
--   to an Agda name.
lookupIdent :: IR.DeclIdent -> Converter Agda.Name
lookupIdent ident = do
  let name = IR.declIdentName ident
  Just qualid <- inEnv $ lookupAgdaIdent IR.ValueScope name
  pure $ Agda.unqualify qualid

-------------------------------------------------------------------------------
-- Free Type Lifting                                                         --
-------------------------------------------------------------------------------

-- | Converts a fully applied function.
convertFunc_ :: [IR.TypeVarDecl] -> [Maybe IR.Type] -> Converter Agda.Expr
convertFunc_ tVars ts = Agda.pi tVars' <$> convertFunc (fromJust <$> ts)
  where tVars' = Agda.Base.addTVars (Agda.name . IR.typeVarDeclIdent <$> tVars)

-- | Lifts an n-ary function piece wise. Functions, which take all their
--   arguments aren't evaluated until they are fully applied. Therefore partial
--   application cannot produce @undefined@.
--
--   > (τ₁ → τ₂ → … → τₙ)* = τ₁' → τ₂' → … → τₙ'
convertFunc :: [IR.Type] -> Converter Agda.Expr
convertFunc ts =
  foldr1 Agda.func <$> mapM (fmap Agda.Base.free' . convertType) ts

-- | Implements the dagger translation. Types are lifted recursively in the free
--   monad.
--   The dagger translation is denoted by ' and ^ denoted renamed identifiers.
--
-- > (τ → σ)’ = Free (Free τ’ → Free σ’)
-- > α' = α    (τ σ)’ = τ’ σ’    C' = Ĉ @S @P
convertType :: IR.Type -> Converter Agda.Expr
convertType (IR.TypeVar _ name) = pure $ Agda.ident name -- TODO: lookup
convertType (IR.TypeCon s name) =
  Agda.Base.freeArgs <$> lookupAgdaIdentOrFail s IR.TypeScope name
convertType (IR.TypeApp  _ l r) = Agda.app <$> convertType l <*> convertType r
convertType (IR.FuncType _ l r) = freeFunc <$> convertType l <*> convertType r
  where freeFunc = Agda.func `on` Agda.Base.free'

