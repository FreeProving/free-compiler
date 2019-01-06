module Language.Haskell.Monad where

import Compiler.HelperFunctions
import Language.Coq.Gallina as G
import qualified Data.Text as T


monadDefinitions :: [G.Sentence]
monadDefinitions =
  [ optionReturnSentence, optionBindSentence, bindNotationSentence ]

optionReturnSentence :: G.Sentence
optionReturnSentence =
  G.DefinitionSentence optionReturnDefinition

optionBindSentence :: G.Sentence
optionBindSentence =
  G.DefinitionSentence optionBindDefinition

bindNotationSentence :: G.Sentence
bindNotationSentence =
  G.NotationSentence bindNotation

optionReturnDefinition :: G.Definition
optionReturnDefinition = G.DefinitionDef G.Global (strToQId "return_") binders (Just retTerm) rhs
  where
    retTerm = G.Arrow aTerm (G.App (G.Qualid $ strToQId "option") (singleton $ G.PosArg aTerm))
    binders = [G.Typed G.Ungeneralizable G.Explicit (singleton $ strToGName "A") typeTerm]
    aTerm = G.Qualid (strToQId "A")
    rhs = G.Qualid (strToQId "Some")

optionBindDefinition :: G.Definition
optionBindDefinition = G.DefinitionDef G.Global (strToQId "bind_") binders (Just retTerm) rhs
  where
    binders = [G.Typed G.Ungeneralizable G.Explicit (toNonemptyList [strToGName "A", strToGName "B"] ) typeTerm,
               G.Typed G.Ungeneralizable G.Explicit (singleton (strToGName "m")) optionATerm,
               G.Typed G.Ungeneralizable G.Explicit (singleton (strToGName "f")) (G.Arrow aTerm retTerm)]
    retTerm = G.App (G.Qualid $ strToQId "option") (singleton $ G.PosArg bTerm)
    rhs = G.Match (singleton $ G.MatchItem mTerm Nothing Nothing) Nothing equations
    equations = [G.Equation (singleton (G.MultPattern (singleton (G.QualidPat (strToQId "None"))))) (G.Qualid $ strToQId "None"),
                 G.Equation (singleton (G.MultPattern (singleton (G.ArgsPat (strToQId "Some") [G.QualidPat $ strToQId "A"])))) (G.App fTerm (singleton $ G.PosArg aTerm))]
    aTerm = G.Qualid $ strToQId "A"
    bTerm = G.Qualid $ strToQId "B"
    mTerm = G.Qualid $ strToQId "m"
    fTerm = G.Qualid $ strToQId "f"
    optionATerm = G.App (G.Qualid $ strToQId "option") (singleton $ G.PosArg aTerm)


bindNotation :: G.Notation
bindNotation =
    G.InfixDefinition operator binding (Just G.LeftAssociativity) (G.Level 50) False
    where
      operator = T.pack "m >>= f"
      binding = G.App (G.Qualid (strToQId "bind_")) (toNonemptyList params)
      params = [G.PosArg (G.Qualid (strToQId "m")), G.PosArg (G.Qualid (strToQId "f"))]



bindSig :: (G.Qualid, G.Term)
bindSig =
  (strToQId "bind", G.Forall aBinders firstDecl)
  where
    aBinders = singleton (strToBinder "a")
    bBinders = singleton (strToBinder "b")
    firstDecl = G.Arrow (G.App mTerm (singleton (G.PosArg aTerm))) (G.Forall bBinders secondDecl)
    secondDecl = G.Arrow funSig monadicB
    funSig = G.Parens (G.Arrow aTerm monadicB)
    monadicB = G.App mTerm (singleton (G.PosArg bTerm))
    aTerm = G.Qualid (strToQId "a")
    bTerm = G.Qualid (strToQId "b")
    mTerm = G.Qualid (strToQId "m")
