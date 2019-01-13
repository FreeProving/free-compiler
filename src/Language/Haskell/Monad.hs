module Language.Haskell.Monad where

import Compiler.HelperFunctions
import Compiler.MonadicConverter
import Language.Coq.Gallina as G
import qualified Data.Text as T


monadDefinitions :: [G.Sentence]
monadDefinitions =
  [ optionReturnSentence, optionBindSentence, bindNotationSentence, listSentence, argSentence, singletonSentence ]

optionReturnSentence :: G.Sentence
optionReturnSentence =
  G.DefinitionSentence optionReturnDefinition

optionBindSentence :: G.Sentence
optionBindSentence =
  G.DefinitionSentence optionBindDefinition

bindNotationSentence :: G.Sentence
bindNotationSentence =
  G.NotationSentence bindNotation

singletonSentence :: G.Sentence
singletonSentence =
  G.DefinitionSentence singletonDefinition

listSentence :: G.Sentence
listSentence =
  G.InductiveSentence listType

argSentence :: G.Sentence
argSentence =
  G.ArgumentsSentence arguments

optionReturnDefinition :: G.Definition
optionReturnDefinition = G.DefinitionDef G.Global (strToQId "return_") binders (Just retTerm) rhs
  where
    retTerm = G.Arrow aTerm (G.App (G.Qualid (strToQId "option")) (singleton (G.PosArg aTerm)))
    binders = [G.Typed G.Ungeneralizable G.Explicit (singleton (strToGName "A")) typeTerm]
    aTerm = G.Qualid (strToQId "A")
    rhs = G.Qualid (strToQId "Some")

optionBindDefinition :: G.Definition
optionBindDefinition = G.DefinitionDef G.Global (strToQId "bind_") binders (Just retTerm) rhs
  where
    binders = [G.Typed G.Ungeneralizable G.Explicit (toNonemptyList [strToGName "A", strToGName "B"] ) typeTerm,
               G.Typed G.Ungeneralizable G.Explicit (singleton (strToGName "m")) optionATerm,
               G.Typed G.Ungeneralizable G.Explicit (singleton (strToGName "f")) (G.Arrow aTerm retTerm)]
    retTerm = G.App (G.Qualid (strToQId "option")) (singleton (G.PosArg bTerm))
    rhs = G.Match (singleton (G.MatchItem mTerm Nothing Nothing)) Nothing equations
    equations = [G.Equation (singleton (G.MultPattern (singleton (G.QualidPat (strToQId "None"))))) (G.Qualid (strToQId "None")),
                 G.Equation (singleton (G.MultPattern (singleton (G.ArgsPat (strToQId "Some") [G.QualidPat (strToQId "A")])))) (G.App fTerm (singleton (G.PosArg aTerm)))]
    aTerm = G.Qualid (strToQId "A")
    bTerm = G.Qualid (strToQId "B")
    mTerm = G.Qualid (strToQId "m")
    fTerm = G.Qualid (strToQId "f")
    optionATerm = G.App (G.Qualid (strToQId "option")) (singleton (G.PosArg aTerm))


bindNotation :: G.Notation
bindNotation =
    G.InfixDefinition operator binding (Just G.LeftAssociativity) (G.Level 50) False
    where
      operator = T.pack "m >>= f"
      binding = G.App (G.Qualid (strToQId "bind_")) (toNonemptyList params)
      params = [G.PosArg (G.Qualid (strToQId "m")), G.PosArg (G.Qualid (strToQId "f"))]

singletonDefinition :: G.Definition
singletonDefinition =
  G.DefinitionDef G.Global
    (strToQId "singleton")
      [G.Typed G.Ungeneralizable G.Explicit (singleton (strToGName "a")) typeTerm ,
      G.Typed G.Ungeneralizable G.Explicit (singleton (strToGName "ox")) (toOptionTerm aTerm)]
        Nothing
          (toReturnTerm rhs)
  where
    rhs = G.App (G.Qualid (strToQId "Cons")) (toNonemptyList [G.PosArg (G.Qualid (strToQId "ox")),
            G.PosArg ((toReturnTerm (G.Qualid (strToQId "Nil"))))])
    aTerm = G.Qualid (strToQId "a")

listType :: G.Inductive
listType =
  G.Inductive (singleton (G.IndBody (strToQId "List")
    [G.Typed G.Ungeneralizable G.Explicit (singleton (strToGName "a")) typeTerm ]
      typeTerm
        [(strToQId "Nil", [], Just listTerm),
        (strToQId "Cons", [], Just arrowTerm)])) []
  where
    listTerm = G.App (G.Qualid (strToQId "List")) (singleton (G.PosArg (G.Qualid (strToQId "a"))))
    arrowTerm = G.Arrow aTerm (G.Arrow (toOptionTerm listTerm) listTerm)
    aTerm = toOptionTerm (G.Qualid (strToQId "a"))

arguments :: G.Arguments
arguments =
  G.Arguments Nothing
    (strToQId "Nil")
      [G.ArgumentSpec G.ArgMaximal (strToGName "a") Nothing]

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
