module Coq.Converter where

import Language.Haskell.Exts.Syntax
import qualified Coq.Gallina as G
import Coq.Pretty
import Text.PrettyPrint.Leijen.Text

import qualified GHC.Base as B

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
convertMatchDef (Match _ name pattern rhs _) = G.DefinitionDef G.Local (nameToQId name) (convertPatsToBinders pattern) Nothing (convertMatchRhsToTerm rhs)

convertPatsToBinders :: [Pat l] -> [G.Binder]
convertPatsToBinders pats = [convertPatToBinder s | s <- pats]

convertPatToBinder :: Pat l -> G.Binder
convertPatToBinder (PVar _ name) = G.Inferred G.Explicit (nameToGName name)
convertPatToBinder _ = error "not implemented"

convertMatchRhsToTerm :: Rhs l -> G.Term
convertMatchRhsToTerm (UnGuardedRhs _ expr) = convertMatchExprToTerm expr
convertMatchRhsToTerm _ = error "not implemented"

convertMatchExprToTerm :: Exp l -> G.Term
convertMatchExprToTerm (InfixApp _ (Var _ qNameL) (qOp) (Var _ qNameR)) = G.Match ((G.MatchItem (G.Qualid (qNameToQId qNameL))  Nothing Nothing) B.:| [] ) Nothing (convertMatchInfixAppToEquation qNameL qOp qNameR)
convertMatchExprToTerm _ = error "not implemented"
-- G.Fun ((convertQNameToBinder qNameL) B.:| (convertQNameToBinder qNameR) : []) (G.App (G.Qualid (qOpToQId op)) ((G.PosArg (G.Qualid (qNameToQId qNameL))) B.:| (G.PosArg (G.Qualid (qNameToQId qNameR))) : []))

convertMatchInfixAppToEquation :: QName l -> QOp l -> QName l -> [G.Equation]
convertMatchInfixAppToEquation qNameL qOp qNameR = [G.Equation ((G.MultPattern ((G.UnderscorePat) B.:| [])) B.:| []) (G.App (G.Qualid (qOpToQId qOp)) ((G.PosArg (G.Qualid (qNameToQId qNameL))) B.:| (G.PosArg (G.Qualid (qNameToQId qNameR))) : []))]

convertQNameToBinder :: QName l -> G.Binder
convertQNameToBinder qName = G.Inferred G.Explicit (qNameToGName qName)

nameToText :: Name l -> T.Text
nameToText (Ident _ str) = T.pack str
nameToText (Symbol _ str) = T.pack str

qNameToText :: QName l -> T.Text
qNameToText (UnQual _ name) = nameToText name
qNameToText _ = error "not implemented"

qNameToQId :: QName l -> G.Qualid
qNameToQId qName = G.Bare (qNameToText qName)

nameToQId :: Name l -> G.Qualid
nameToQId name = G.Bare (nameToText name)

qNameToGName :: QName l -> G.Name
qNameToGName (UnQual _ name) = (nameToGName name)
qNameToGName _ = error "not implemented"

nameToGName :: Name l -> G.Name
nameToGName name = G.Ident (nameToQId name)

qNameToOp :: QName l -> G.Op
qNameToOp qName = qNameToText qName


qOpToQId :: QOp l -> G.Qualid
qOpToQId (QVarOp _ (UnQual _ (Symbol _ name))) = G.Bare (T.pack ("op_"++ name ++"__"))
qOpToQId _ = error "not implemented"

printCoqAST :: G.LocalModule -> IO ()
printCoqAST x = putDoc (renderGallina x)
