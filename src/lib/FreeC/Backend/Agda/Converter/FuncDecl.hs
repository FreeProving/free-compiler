module FreeC.Backend.Agda.Converter.FuncDecl where

import qualified FreeC.Backend.Agda.Syntax     as Agda
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter          ( Converter
                                                , inEnv
                                                )
import           FreeC.Environment              ( lookupAgdaIdent )

convertFuncDecl :: IR.FuncDecl -> Converter [Agda.Declaration]
convertFuncDecl (IR.FuncDecl _ ident typeVar args retType expr) = do
  let name = IR.declIdentName ident
  Just qualid <- inEnv $ lookupAgdaIdent IR.ValueScope name
  pure [Agda.funcSig (Agda.unqualify qualid) (Agda.intLiteral 42)]
