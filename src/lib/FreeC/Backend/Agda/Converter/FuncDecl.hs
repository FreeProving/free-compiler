module FreeC.Backend.Agda.Converter.FuncDecl where

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
import           Debug.Trace

convertFuncDecl :: IR.FuncDecl -> Converter [Agda.Declaration]
convertFuncDecl decl = sequence [convertSignature decl]

convertSignature :: IR.FuncDecl -> Converter Agda.Declaration
convertSignature (IR.FuncDecl _ ident tVars args retType _) =
  Agda.funcSig <$> convertIdent ident <*> liftType tVars types
  where types = (IR.varPatType <$> args) `snoc` retType

convertDef :: IR.FuncDecl -> Converter Agda.Declaration
convertDef = undefined

convertIdent :: IR.DeclIdent -> Converter Agda.Name
convertIdent ident = do
  let name = IR.declIdentName ident
  Just qualid <- inEnv $ lookupAgdaIdent IR.ValueScope name
  pure $ Agda.unqualify qualid

-------------------------------------------------------------------------------
-- Free Type Lifting                                                         --
-------------------------------------------------------------------------------

liftType :: [IR.TypeVarDecl] -> [Maybe IR.Type] -> Converter Agda.Expr
liftType tVars ts = Agda.pi tVars' <$> convertFunc (fromJust <$> ts)
  where tVars' = Agda.Base.addTVars (Agda.name . IR.typeVarDeclIdent <$> tVars)

-- | Lifts an n-ary function piece wise. Functions, which take all their
--   arguments aren't evaluated until they are fully applied. Therefore partial
--   application cannot produce @undefined@.
--
--   > (τ₁ → τ₂ → … → τₙ)* = τ₁' → τ₂' → … → τₙ'
convertFunc :: [IR.Type] -> Converter Agda.Expr
convertFunc ts =
  foldr1 Agda.func <$> mapM (fmap Agda.Base.free' . convertType) ts

convertType :: IR.Type -> Converter Agda.Expr
convertType (IR.TypeVar _ name) = pure $ Agda.ident name -- TODO: lookup
convertType (IR.TypeCon _ name) = convertConName name
convertType (IR.TypeApp  _ l r) = Agda.app <$> convertType l <*> convertType r
convertType (IR.FuncType _ l r) = freeFunc <$> convertType l <*> convertType r
  where freeFunc = Agda.func `on` Agda.Base.free'

convertConName :: IR.QName -> Converter Agda.Expr
convertConName (IR.Qual _ n) = pure $ Agda.Ident $ Agda.qname' $ convertName n
convertConName (IR.UnQual n) = pure $ Agda.Ident $ Agda.qname' $ convertName n

convertName :: IR.Name -> Agda.Name
convertName n = Agda.name $ case n of
  IR.Ident  name -> name
  IR.Symbol "[]" -> "List"
  IR.Symbol ","  -> "Pair"
  IR.Symbol name -> trace ("Missing ident: " <> name) undefined

