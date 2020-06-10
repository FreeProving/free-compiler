module FreeC.Backend.Agda.Converter.FuncDecl
  ( convertFuncDecl
  )
where

import           Data.Function                  ( on )
import           Data.List.Extra                ( snoc )
import           Data.Maybe                     ( fromJust )
import qualified FreeC.Backend.Agda.Base       as Agda.Base
import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.Environment.LookupOrFail ( lookupAgdaIdentOrFail )
import           FreeC.Environment.Renamer      ( renameAndDefineAgdaTypeVar )
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter          ( Converter
                                                , localEnv
                                                )
import           Prelude                 hiding ( mod )

-- | Converts the given function declarations. Returns the declarations for the
--   type signature and the definition (TODO).
convertFuncDecl :: IR.FuncDecl -> Converter [Agda.Declaration]
convertFuncDecl decl = localEnv $ sequence [convertSignature decl]

-- | Converts the type signature of the given function to an Agda type
--   declaration.
convertSignature :: IR.FuncDecl -> Converter Agda.Declaration
convertSignature (IR.FuncDecl _ ident tVars args retType _) =
  Agda.funcSig <$> lookupValueIdent ident <*> convertFunc_ tVars types
  where types = (IR.varPatType <$> args) `snoc` retType

-- | Looks up the name of a Haskell function in the environment and converts it
--   to an Agda name.
lookupValueIdent :: IR.DeclIdent -> Converter Agda.Name
lookupValueIdent (IR.DeclIdent srcSpan name) =
  Agda.unqualify <$> lookupAgdaIdentOrFail srcSpan IR.ValueScope name

-------------------------------------------------------------------------------
-- Free Type Lifting                                                         --
-------------------------------------------------------------------------------

-- | Converts a fully applied function.
convertFunc_ :: [IR.TypeVarDecl] -> [Maybe IR.Type] -> Converter Agda.Expr
convertFunc_ tVars ts = Agda.pi <$> tVars' <*> convertFunc (fromJust <$> ts)
  where tVars' = Agda.Base.addTVars <$> mapM renameAgdaTypeVar tVars

renameAgdaTypeVar :: IR.TypeVarDecl -> Converter Agda.Name
renameAgdaTypeVar (IR.TypeVarDecl srcSpan name) =
  Agda.unqualify <$> renameAndDefineAgdaTypeVar srcSpan name

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
--   The dagger translation is denoted by ' and ^ denotes renamed identifiers.
--
--   > (τ → σ)’ = Free (Free τ’ → Free σ’)
--   > α' = α    (τ σ)’ = τ’ σ’    C' = Ĉ @S @P
convertType :: IR.Type -> Converter Agda.Expr
convertType (IR.TypeVar s name) = Agda.Ident
  <$> lookupAgdaIdentOrFail s IR.TypeScope (IR.UnQual (IR.Ident name))
convertType (IR.TypeCon s name) =
  Agda.Base.freeArgs <$> lookupAgdaIdentOrFail s IR.TypeScope name
convertType (IR.TypeApp  _ l r) = Agda.app <$> convertType l <*> convertType r
convertType (IR.FuncType _ l r) = freeFunc <$> convertType l <*> convertType r
  where freeFunc = Agda.func `on` Agda.Base.free'