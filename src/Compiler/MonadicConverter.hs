module Compiler.MonadicConverter where

import Language.Coq.Gallina as G

import Compiler.Types
import Compiler.HelperFunctions

import qualified Data.Text as T
import qualified GHC.Base as B

---------------------- Add Bind Operator
addBindOperators :: [G.Binder] -> G.Term -> G.Term
addBindOperators [] term =
  toReturnTerm term
addBindOperators (x : xs) term =
  G.App bindOperator
    (toNonemptyList [G.PosArg argumentName, G.PosArg lambdaFun])
  where
    argumentName = getBinderName x
    lambdaFun = G.Fun (singleton $ removeMonadFromBinder x) (addBindOperators xs term )

---------------------- transform Data Structures Monadic
transformBindersMonadic :: [G.Binder] -> ConversionMonad -> [G.Binder]
transformBindersMonadic binders m =
  [transformBinderMonadic (addMonadicPrefixToBinder m b) m | b <- binders]

transformBinderMonadic :: G.Binder -> ConversionMonad -> G.Binder
transformBinderMonadic (G.Typed gen expl name term) m =
  G.Typed gen expl name (transformTermMonadic term m)

transformTermMonadic :: G.Term -> ConversionMonad -> G.Term
transformTermMonadic (G.Sort G.Type) m =
  typeTerm
transformTermMonadic term m =
  monad term
  where
    monad = case m of
          Option -> toOptionTerm
          Identity -> toIdentityTerm

-- Convert Terms Monadic
toOptionTerm :: G.Term -> G.Term
toOptionTerm term =
  G.App optionTerm (singleton (G.PosArg term))

toIdentityTerm :: G.Term -> G.Term
toIdentityTerm term =
  G.App identityTerm (singleton (G.PosArg term))

toReturnTerm :: G.Term -> G.Term
toReturnTerm term =
  G.App returnTerm (singleton (G.PosArg (G.Parens term)))

---------------------- Add Monadic Prefixes

addMonadicPrefix :: String -> G.Name -> G.Name
addMonadicPrefix str (G.Ident (G.Bare ident)) =
  G.Ident (strToQId (str ++ name))
  where
    name = T.unpack ident

addMonadicPrefixToBinder ::  ConversionMonad -> G.Binder -> G.Binder
addMonadicPrefixToBinder m (G.Inferred expl name) =
  G.Inferred expl (getPrefixFromMonad m name)
addMonadicPrefixToBinder m (G.Typed gen expl (name B.:| xs) ty) =
  G.Typed gen expl (singleton (getPrefixFromMonad m name)) ty

addMonadicPrefixToQId ::  ConversionMonad -> G.Qualid -> G.Qualid
addMonadicPrefixToQId m qId =
  gNameToQId (getPrefixFromMonad m (G.Ident qId))


getPrefixFromMonad :: ConversionMonad -> (G.Name -> G.Name)
getPrefixFromMonad Option = addOptionPrefix
getPrefixFromMonad Identity = addIdentityPrefix

-- Monadic Prefixes used
addOptionPrefix :: G.Name -> G.Name
addOptionPrefix =
  addMonadicPrefix "o"

addIdentityPrefix :: G.Name -> G.Name
addIdentityPrefix =
  addMonadicPrefix "i"

  ---------------------- Remove Monadic Elements

removeMonadFromBinder :: G.Binder -> G.Binder
removeMonadFromBinder (G.Typed gen expl (n B.:| xs) term) =
  G.Typed gen expl (singleton (removeMonadicPrefix n)) (fromMonadicTerm term)

removeMonadicPrefix :: G.Name -> G.Name
removeMonadicPrefix name =
  strToGName (tail (getStringFromGName name))

fromMonadicTerm :: G.Term -> G.Term
fromMonadicTerm (G.App _ (G.PosArg term B.:| xs)) =
  term
fromMonadicTerm term =
  term

---------------------- Predefined Terms
identityTerm :: G.Term
identityTerm =
  G.Qualid (strToQId "identity")

optionTerm :: G.Term
optionTerm =
  G.Qualid (strToQId "option")

returnTerm :: G.Term
returnTerm =
  G.Qualid (strToQId "return_")

bindOperator :: G.Term
bindOperator =
  G.Qualid (strToQId "op_>>=__")
