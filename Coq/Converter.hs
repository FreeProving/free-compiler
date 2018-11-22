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
convertMatchDef (Match _ name pattern rhs _) = G.DefinitionDef G.Global (nameToQId name) (convertPatsToBinders pattern) Nothing (convertRhsToTerm rhs)

convertPatsToBinders :: [Pat l] -> [G.Binder]
convertPatsToBinders pats = [convertPatToBinder s | s <- pats]

convertPatToBinder :: Pat l -> G.Binder
convertPatToBinder (PVar _ name) = G.Inferred G.Explicit (nameToGName name)
convertPatToBinder _ = error "not implemented"

convertRhsToTerm :: Rhs l -> G.Term
convertRhsToTerm (UnGuardedRhs _ expr) = convertExprToTerm expr
convertRhsToTerm (GuardedRhss _ _ ) = error "not implemented"

convertExprToTerm :: Exp l -> G.Term
convertExprToTerm (Var _ qName) = qNameToTerm qName
convertExprToTerm (Con _ qName) = qNameToTerm qName
convertExprToTerm (InfixApp _ (Var _ qNameL) (qOp) (Var _ qNameR)) = (G.App (G.Qualid (qOpToQId qOp)) ((G.PosArg (G.Qualid (qNameToQId qNameL))) B.:| (G.PosArg (G.Qualid (qNameToQId qNameR))) : []))
convertExprToTerm (Case _ expr altList) = G.Match ((G.MatchItem (convertExprToTerm expr)  Nothing Nothing) B.:| [] ) Nothing (convertAltListToEquationList altList)
convertExprToTerm _ = error "not implemented"
-- G.Fun ((convertQNameToBinder qNameL) B.:| (convertQNameToBinder qNameR) : []) (G.App (G.Qualid (qOpToQId op)) ((G.PosArg (G.Qualid (qNameToQId qNameL))) B.:| (G.PosArg (G.Qualid (qNameToQId qNameR))) : []))

convertAltListToEquationList :: [Alt l] -> [G.Equation]
convertAltListToEquationList altList = [convertAltToEquation s | s <- altList]

convertAltToEquation :: Alt l -> G.Equation
convertAltToEquation (Alt _ pat rhs _) = G.Equation (toNonemptyList (G.MultPattern (toNonemptyList(convertHPatToGPat pat)))) (convertRhsToTerm rhs)

convertHPatListToGPatList :: [Pat l] -> [G.Pattern]
convertHPatListToGPatList patList = [convertHPatToGPat s | s <- patList]

convertHPatToGPat :: Pat l -> G.Pattern
convertHPatToGPat (PVar _ name) = G.QualidPat (nameToQId name)
convertHPatToGPat (PApp _ qName pList) = G.ArgsPat (qNameToQId qName) (convertHPatListToGPatList pList)
convertHPatToGPat _ = error "not implemented"

convertQNameToBinder :: QName l -> G.Binder
convertQNameToBinder qName = G.Inferred G.Explicit (qNameToGName qName)

--helper functions
toNonemptyList :: a -> B.NonEmpty a
toNonemptyList a = a B.:| []

nameToText :: Name l -> T.Text
nameToText (Ident _ str) = T.pack str
nameToText (Symbol _ str) = T.pack str

nameToQId :: Name l -> G.Qualid
nameToQId name = G.Bare (nameToText name)

nameToGName :: Name l -> G.Name
nameToGName name = G.Ident (nameToQId name)

qNameToText :: QName l -> T.Text
qNameToText (UnQual _ name) = nameToText name
qNameToText _ = error "not implemented"

qNameToQId :: QName l -> G.Qualid
qNameToQId qName = G.Bare (qNameToText qName)

qNameToGName :: QName l -> G.Name
qNameToGName (UnQual _ name) = (nameToGName name)
qNameToGName _ = error "not implemented"

qNameToOp :: QName l -> G.Op
qNameToOp qName = qNameToText qName

qNameToTerm :: QName l -> G.Term
qNameToTerm qName = G.Qualid (qNameToQId qName)

--Convert qualifiedOperator from Haskell to Qualid with Operator signature
qOpToQId :: QOp l -> G.Qualid
qOpToQId (QVarOp _ (UnQual _ (Symbol _ name))) = G.Bare (T.pack ("op_"++ name ++"__"))
qOpToQId _ = error "not implemented"

printCoqAST :: G.LocalModule -> IO ()
printCoqAST x = putDoc (renderGallina x)
