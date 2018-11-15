module Coq.Converter where

import Language.Haskell.Exts.Syntax
import Coq.Gallina

convertToCoq :: Module l -> String
convertToCoq m =
  case m of
    Module _ (Just modHead) _ _ decls -> convertModuleHead modHead ++ convertDeclarations decls
    Module _ Nothing _ _ decls -> convertDeclarations decls


convertModuleHead mh =
  case mh of
    ModuleHead _ (ModuleName _ name) _ _ -> "module " ++ name ++ ". \n \r"

convertDeclarations [] = ""
convertDeclarations (x:xs) = convertDeclaration x ++ convertDeclarations xs

convertDeclaration decl =
  case decl of
    FunBind _ match -> "Definition " ++ convertFunctionBinding match ++". \n \r"

convertFunctionBinding [] = ""
convertFunctionBinding (x:xs) = convertFunctionClause x ++ convertFunctionBinding xs

convertFunctionClause x =
  case x of
    Language.Haskell.Exts.Syntax.Match _ name pat rhs _ -> convertName name ++ convertPatterns pat ++ convertRhs rhs

convertPatterns [] = ""
convertPatterns (x:xs) = convertPattern x ++ convertPatterns xs

convertPattern pat =
  case pat of
    PVar _ name -> convertName name


convertRhs rhs =
  case rhs of
    UnGuardedRhs _ expr ->  ":= " ++ convertExpression expr
    GuardedRhss _ _  -> notI

convertName n =
  case n of
    Language.Haskell.Exts.Syntax.Ident _ n -> n ++ " "
    Symbol _ n -> n ++ " "

convertExpression x =
  case x of
    Var _ qName -> convertQName qName
    InfixApp _ exp1 qop1 exp2 -> convertExpression exp1 ++ convertQOperator qop1 ++ convertExpression exp2

convertQName qName =
  case qName of
    Qual _ _ _ -> notI
    UnQual _ name -> convertName name
    Special _ _ -> notI

convertQOperator qOp =
  case qOp of
    QVarOp _ qName -> convertQName qName
    QConOp _ qName -> convertQName qName

notI = "Not implemented "
