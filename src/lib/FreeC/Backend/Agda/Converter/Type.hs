-- | Implements the IR to Agda translation, which applies the monadic lifting as
--   described by Abel et al. in "Verifying Haskell Programs Using Constructive
--   Type Theory".

module FreeC.Backend.Agda.Converter.Type
  ( convertType
  , convertFunctionType
  , convertConType
  , convertRecConType
  )
where


import           Prelude                 hiding ( pi )

import           Data.Composition               ( (.:) )

import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.Backend.Agda.Converter.Free
                                                ( free
                                                , applyFreeArgs
                                                )
import           FreeC.Environment.Fresh        ( freshAgdaVar )
import           FreeC.Environment.LookupOrFail ( lookupAgdaIdentOrFail )
import           FreeC.Backend.Agda.Converter.Size
                                                ( up )
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter          ( Converter
                                                , localEnv
                                                )

-- | Lifts a single type.
convertType :: IR.Type -> Converter Agda.Expr
convertType = dagger'

-- | Functions not defined in terms lambdas (@f x = …@ not @f = \x -> …@) aren't
--   evaluated until fully applied, i.e. cannot be bottom. Therefore interleaving
--   monadic layers isn't needed.
--
--   > τ₁ -> … -> τₙ -> ρ ↦ τ₁' → … → τₙ' → ρ'
convertFunctionType :: [IR.Type] -> IR.Type -> Converter Agda.Expr
convertFunctionType argTypes returnType =
  foldr Agda.fun <$> dagger' returnType <*> mapM dagger' argTypes

-- | Constructors aren't evaluated until fully applied. Furthermore the return
--   type of a constructor for a data type D has to be D and therefore cannot be
--   lifted.
--
--   > τ₁ -> … -> τₙ -> ρ ↦ τ₁' → … → τₙ' → ρ*
convertConType :: [IR.Type] -> IR.Type -> Converter Agda.Expr
convertConType argTypes returnType =
  -- We can use the @star@ translation for the data type, because only the name
  -- and the application of type and @Size@ variables have to be translated.
  foldr Agda.fun <$> star' returnType <*> mapM dagger' argTypes

convertRecConType :: IR.QName -> [IR.Type] -> IR.Type -> Converter Agda.Expr
convertRecConType ident argTypes returnType = pi "i" $ \i -> do
  foldr Agda.fun
    <$> (Agda.app <$> star' returnType <*> pure (Agda.hiddenArg_ $ up i))
    <*> mapM (dagger $ Just (ident, Agda.hiddenArg_ i)) argTypes

-------------------------------------------------------------------------------
-- Translations                                                              --
-------------------------------------------------------------------------------

-- | Converts a type from IR to Agda by lifting it into the @Free@ monad.
--
--   This corresponds to the dagger translation for monotypes as described by
--   Abel et al.
--
--   > τ' = Free τ*
dagger :: Maybe (IR.QName, Agda.Expr) -> IR.Type -> Converter Agda.Expr
dagger = fmap free .: star

-- | Lifts a type from IR to Agda by renaming type variables and constructors,
--   adding the free arguments to constructors and lifting function types in
--   the @Free@ monad.
--
--   This corresponds to the star translation for monotypes as described by
--   Abel et al.
--
--   > (τ₁ τ₂)* = τ₁* τ₂*
--   > (τ₁ → τ₂)* = τ₁' → τ₂'
--   > C* = Ĉ Shape Position
--   > α* = α̂
star :: Maybe (IR.QName, Agda.Expr) -> IR.Type -> Converter Agda.Expr
-- If we apply arguments to the constructor of the data type itself we add a
-- size annotation.
star (Just (ident, i)) t@(IR.TypeApp _ _ _) =
  if t `appliesTo` ident then Agda.app <$> star' t <*> pure i else star' t
star (Just (ident, i)) t@(IR.TypeCon _ name) =
  if ident == name then Agda.app <$> star' t <*> pure i else star' t
-- Otherwise we just apply the normal star transformation.
star _ (IR.TypeVar s name) = Agda.Ident
  <$> lookupAgdaIdentOrFail s IR.TypeScope (IR.UnQual (IR.Ident name))
star _ (IR.TypeCon s name) =
  applyFreeArgs <$> lookupAgdaIdentOrFail s IR.TypeScope name
star _ (IR.TypeApp  _ l r) = Agda.app <$> star' l <*> star' r
star _ (IR.FuncType _ l r) = Agda.fun <$> dagger' l <*> dagger' r

dagger' :: IR.Type -> Converter Agda.Expr
dagger' = dagger Nothing

star' :: IR.Type -> Converter Agda.Expr
star' = star Nothing

-- | Is the given type a type application, which applies arguments to the given
--   constructor?
--
--   > appliesTo (((C x₁) …) xₙ) C ↦ True
appliesTo :: IR.Type -> IR.QName -> Bool
appliesTo (IR.TypeApp _ l _    ) name = l `appliesTo` name
appliesTo (IR.TypeCon _ conName) name = conName == name
appliesTo _                      _    = False

-------------------------------------------------------------------------------
-- specialized syntax                                                        --
-------------------------------------------------------------------------------

pi :: String -> (Agda.Expr -> Converter Agda.Expr) -> Converter Agda.Expr
pi name k = localEnv $ do
  var <- freshAgdaVar name undefined
  Agda.pi [Agda.unqualify var] <$> k (Agda.Ident var)

