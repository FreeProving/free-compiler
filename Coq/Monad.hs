module Coq.Monad where

import Coq.HelperFunctions
import Coq.Gallina as G
import qualified Data.Text as T


monadDefinitions :: [G.Sentence]
monadDefinitions =
  monadTypeClass : bindNotationSentence : optionMonadImplementationSentance : []

monadTypeClass :: G.Sentence
monadTypeClass =
  G.ClassSentence monadClassDefinition

bindNotationSentence :: G.Sentence
bindNotationSentence =
  G.NotationSentence bindNotation

optionMonadImplementationSentance :: G.Sentence
optionMonadImplementationSentance =
  G.InstanceSentence optionMonadImplementation

optionMonadImplementation :: G.InstanceDefinition
optionMonadImplementation =
  G.InstanceDefinition maybeQId [] ty funs Nothing
  where
    ty = G.App (G.Qualid maybeQId) (singleton (G.PosArg (G.Qualid (strToQId "option"))))
    maybeQId = strToQId "Maybe"
    funs = (strToQId "return_", G.Qualid (strToQId "Some")) : (strToQId "bind", lambda) : []
    lambda = G.Fun (toNonemptyList binders) (G.Match (singleton (G.MatchItem (G.Qualid (strToQId "m")) Nothing Nothing)) Nothing equations)
    binders = strToBinder "a" : strToBinder "m" : strToBinder "b" : strToBinder "f" : []
    equations =
      G.Equation (singleton (G.MultPattern (singleton (G.ArgsPat (strToQId "None") [])))) (G.Qualid (strToQId "None")) :
      G.Equation (singleton (G.MultPattern (singleton (G.ArgsPat (strToQId "Some") [G.QualidPat (strToQId "a")]))))
        (G.App (G.Qualid (strToQId "f")) (singleton (G.PosArg (G.Qualid (strToQId "a"))))) : []

bindNotation :: G.Notation
bindNotation =
    G.InfixDefinition operator binding (Just G.LeftAssociativity) (G.Level 50) False
    where
      operator = T.pack "m >>= f"
      binding = G.App (G.Qualid (strToQId "bind")) (toNonemptyList params)
      params = G.PosArg (G.Qualid (strToQId "m")) : G.PosArg G.Underscore : G.PosArg (G.Qualid (strToQId "f")) : []

monadClassDefinition :: G.ClassDefinition
monadClassDefinition =
  G.ClassDefinition name binder Nothing funs
  where
    name = strToQId "Monad"
    binder = [G.Typed G.Ungeneralizable G.Explicit (singleton (strToGName "m")) ty]
    ty = G.Arrow typeSort typeSort
    funs = returnSig : bindSig : []

returnSig :: (G.Qualid, G.Term)
returnSig =
  (strToQId "return_" , G.Forall binders decl)
  where
    binders = singleton (strToBinder "a")
    decl = G.Arrow aTerm app
    app = G.App  mTerm (singleton (G.PosArg aTerm))
    aTerm = G.Qualid (strToQId "a")
    mTerm = G.Qualid (strToQId "m")

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



typeSort :: G.Term
typeSort =
  G.Sort G.Type
