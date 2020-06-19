-- | Implements the IR to Agda translation, which applies the monadic lifting as
--   described by Abel et al. in "Verifying Haskell Programs Using Constructive
--   Type Theory".

module FreeC.Backend.Agda.Converter.Type
  ( convertType
  , convertFuncType
  , convertRecFuncType
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

-- | Functions not defined in terms lambdas (@f x = …@ not @f = \x -> …@) aren't
--   evaluated until fully applied, i.e. cannot be bottom. Therefore interleaving
--   monadic layers isn't needed.
--
--   > τ₁ -> … -> τₙ -> ρ ↦ τ₁' → … → τₙ' → ρ'
convertFuncType :: [IR.Type] -> IR.Type -> Converter Agda.Expr
convertFuncType argTypes returnType =
  foldr Agda.fun <$> convertType returnType <*> mapM convertType argTypes

convertRecFuncType :: Int -> [IR.Type] -> IR.Type -> Converter Agda.Expr
convertRecFuncType decIndex args returnType = pi "i" $ \i -> do
  startArgs <- mapM convertType $ take (decIndex - 1) args
  decArg    <- convertSizedType (Just $ Agda.hiddenArg_ i) $ args !! decIndex
  endArgs   <- mapM convertType $ drop (decIndex + 1) args
  foldr Agda.fun
    <*> pure (startArgs ++ (decArg : endArgs))
    <$> convertType returnType

-- | Constructors aren't evaluated until fully applied. Furthermore the return
--   type of a constructor for a data type D has to be D and therefore cannot be
--   lifted.
--
--   > τ₁ -> … -> τₙ -> ρ ↦ τ₁' → … → τₙ' → ρ*
convertConType :: [IR.Type] -> IR.Type -> Converter Agda.Expr
convertConType argTypes returnType =
  -- We can use the @star@ translation for the data type, because only the name
  -- and the application of type and @Size@ variables have to be translated.
  foldr Agda.fun <$> convertType' returnType <*> mapM convertType argTypes

-- | Converts a constructor type of a recursive data type by lifting it piecewise
--   in the free monad and annotating recursive occurrences of the type with
--   a variable of type @Size@.
convertRecConType :: IR.QName -> [IR.Type] -> IR.Type -> Converter Agda.Expr
convertRecConType ident argTypes returnType = pi "i" $ \i -> do
  let dagger'' = \t -> if t `appliesTo` ident
        then convertSizedType (Just $ Agda.hiddenArg_ i) t
        else convertType t
  foldr Agda.fun
    <$> (Agda.app <$> convertType' returnType <*> pure (Agda.hiddenArg_ $ up i))
    <*> mapM dagger'' argTypes

-------------------------------------------------------------------------------
-- Translations                                                              --
-------------------------------------------------------------------------------

-- | Converts a type from IR to Agda by lifting it into the @Free@ monad.
--
--   This corresponds to the dagger translation for monotypes as described by
--   Abel et al.
--
--   The optional @Agda.Expr@ is a size annotation, which is applied under the
--   free monad.
--
--   > τ' = Free τ*
convertSizedType :: Maybe Agda.Expr -> IR.Type -> Converter Agda.Expr
convertSizedType = fmap free .: convertSizedType'

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
convertSizedType' :: Maybe Agda.Expr -> IR.Type -> Converter Agda.Expr
convertSizedType' (Just i) t = Agda.app <$> convertType' t <*> pure i
convertSizedType' _ (IR.TypeVar s name) = Agda.Ident
  <$> lookupAgdaIdentOrFail s IR.TypeScope (IR.UnQual $ IR.Ident name)
convertSizedType' _ (IR.TypeCon s name) =
  applyFreeArgs <$> lookupAgdaIdentOrFail s IR.TypeScope name
convertSizedType' _ (IR.TypeApp _ l r) =
  Agda.app <$> convertType' l <*> convertType' r
convertSizedType' _ (IR.FuncType _ l r) =
  Agda.fun <$> convertType l <*> convertType r

-- | Converts a type from IR to Agda by lifting it into the @Free@ monad.
convertType :: IR.Type -> Converter Agda.Expr
convertType = convertSizedType Nothing

-- | Lifts a type from IR to Agda by renaming type variables and constructors,
--   adding the free arguments to constructors and lifting function types in
--   the @Free@ monad.
convertType' :: IR.Type -> Converter Agda.Expr
convertType' = convertSizedType' Nothing

-- | Tests whether the given type is a type application, which applies
--   arguments to the given constructor?
--
--   > appliesTo (((C x₁) …) xₙ) C ↦ True
appliesTo :: IR.Type -> IR.QName -> Bool
appliesTo (IR.TypeApp _ l _    ) name = l `appliesTo` name
appliesTo (IR.TypeCon _ conName) name = conName == name
appliesTo _                      _    = False

-------------------------------------------------------------------------------
-- Specialized Syntax                                                        --
-------------------------------------------------------------------------------

-- | Creates a new pi expression binding a variable with the given name.
pi
  :: String
  -- ^ Preferred name for the bound variable.
  -> (Agda.Expr -> Converter Agda.Expr)
  -- ^ Continuation for creating the expression using the variable.
  -> Converter Agda.Expr
pi name k = localEnv $ do
  var <- freshAgdaVar name undefined
  Agda.pi [Agda.unqualify var] <$> k (Agda.Ident var)
