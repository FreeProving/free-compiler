module FreeC.Backend.Agda.Converter.FuncDecl where

import           Data.List.Extra                ( snoc )

import qualified FreeC.Backend.Agda.Syntax     as Agda
import qualified FreeC.Backend.Agda.Base       as Agda.Base
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter          ( Converter
                                                , inEnv
                                                )
import           FreeC.Environment              ( lookupAgdaIdent )

convertFuncDecl :: IR.FuncDecl -> Converter [Agda.Declaration]
convertFuncDecl decl = sequence [convertSignature decl]

convertSignature :: IR.FuncDecl -> Converter Agda.Declaration
convertSignature (IR.FuncDecl _ ident tVars args retType _) =
  Agda.funcSig <$> convertName ident <*> liftType tVars types
  where types = (IR.varPatType <$> args) `snoc` retType

convertDef :: IR.FuncDecl -> Converter Agda.Declaration
convertDef = undefined

convertName :: IR.DeclIdent -> Converter Agda.Name
convertName ident = do
  let name = IR.declIdentName ident
  Just qualid <- inEnv $ lookupAgdaIdent IR.ValueScope name
  pure $ Agda.unqualify qualid

-------------------------------------------------------------------------------
-- Free Type Lifting                                                         --
-------------------------------------------------------------------------------

liftType :: [IR.TypeVarDecl] -> [Maybe IR.Type] -> Converter Agda.Expr
liftType _ _ =
  pure $ Agda.pi [Agda.Base.shape, Agda.Base.position] $ Agda.intLiteral 42
