module Coq.Converter where

import Language.Haskell.Exts.Syntax
import qualified Coq.Gallina as G
import Coq.Pretty
import Text.PrettyPrint.Leijen.Text

import qualified Data.Text as T



convertModule :: Module l -> G.LocalModule
convertModule (Module _ (Just modHead) _ _ decls) = G.LocalModule (convertModuleHead modHead) (convertModuleDecls decls)
convertModule (Module _ Nothing _ _ decls)        = G.LocalModule T.empty (convertModuleDecls decls)

convertModuleHead :: ModuleHead l -> G.Ident
convertModuleHead (ModuleHead _ (ModuleName _ modName) _ _) = T.pack modName

convertModuleDecls :: [Decl l] -> [G.Sentence]
convertModuleDecls decls = [convertModuleDecl s | s <- decls]

convertModuleDecl :: Decl l -> G.Sentence
convertModuleDecl (FunBind _ (x : xs)) = G.DefinitionSentence (convertMatchDef x)
convertModuleDecl _ = error "not Inmplemented"

convertMatchDef :: Match l -> G.Definition
convertMatchDef (Match _ (Ident _ name) pattern rhs _) = G.DefinitionDef G.Local (G.Bare (T.pack name)) (convertPatsToBinders pattern) Nothing (convertRhsToTerm rhs)

convertPatsToBinders :: [Pat l] -> [G.Binder]
convertPatsToBinders pats = [convertPatToBinder s | s <- pats]

convertPatToBinder :: Pat l -> G.Binder
convertPatToBinder (PVar _ (Ident _ name)) = G.Inferred G.Explicit (G.Ident (G.Bare (T.pack name)))
convertPatToBinder _ = error "not implemented"

convertRhsToTerm :: Rhs l -> G.Term
convertRhsToTerm (UnGuardedRhs _ (expr)) = convertExprToTerm expr
convertRhsToTerm _ = error "not implemented"

convertExprToTerm :: Exp l -> G.Term
convertExprToTerm (InfixApp _ (Var _ qNameL) (op) (Var _ qNameR)) = error "not implemented"

qNameToText :: QName l -> T.Text
qNameToText (UnQual _ (Ident _ name)) = T.pack name
qNameToText _ = error "not implemented"

qNameToQId :: QName l -> G.Qualid
qNameToQId qName = G.Bare (qNameToText qName)


printCoqAST :: G.LocalModule -> IO ()
printCoqAST x = putDoc (renderGallina x)


{-convertModuleHead mh =
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

notI = "Not implemented "-}
