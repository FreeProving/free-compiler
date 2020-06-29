-- | Implements the lifted IR to Agda translation.

module FreeC.Backend.Agda.Converter.Type
  ( convertFuncType
  , convertConType
  )
where


import           Prelude                 hiding ( pi )

import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.Backend.Agda.Converter.Free
                                                ( free
                                                , applyFreeArgs
                                                )
import           FreeC.Backend.Agda.Converter.Size
                                                ( up )
import           FreeC.Environment.Fresh        ( freshAgdaVar )
import           FreeC.Environment.LookupOrFail ( lookupAgdaIdentOrFail )
import qualified FreeC.IR.Syntax               as IR
import qualified FreeC.LiftedIR.Syntax         as LIR
import           FreeC.LiftedIR.Syntax.Type     ( decreasing )
import           FreeC.Monad.Converter          ( Converter
                                                , localEnv
                                                )

-------------------------------------------------------------------------------
-- Functions                                                                 --
-------------------------------------------------------------------------------

-- | Converts a lifted IR function type to an Agda type expression.
--
--   If the type contains decreasing annotations, a size type variable is bound
--   and used to annotate these occurrences.
convertFuncType :: [LIR.Type] -> LIR.Type -> Converter Agda.Expr
convertFuncType argTypes retType = if any decreasing argTypes
  then pi "i" $ \i -> convertType (Just i) funcType
  else convertType' funcType
  where funcType = foldr LIR.func retType argTypes

-------------------------------------------------------------------------------
-- Constructors                                                              --
-------------------------------------------------------------------------------

-- | Converts a constructor type from lifted IR to Agda.
--
--   If the constructor contains decreasing arguments (i.e. recursive arguments),
--   a new sized type variable is bound and used to annotate these types.
convertConType :: [LIR.Type] -> LIR.Type -> Converter Agda.Expr
convertConType argTypes retType = if any decreasing argTypes
  then convertRecConType argTypes retType
  else convertType' $ foldr LIR.func retType argTypes

-- | Converts a constructor from lifted IR to Agda by binding a new variable
--   @i : Size@ and annotating recursive occurrences and the return type.
convertRecConType :: [LIR.Type] -> LIR.Type -> Converter Agda.Expr
convertRecConType argTypes retType = pi "i" $ \i -> do
  retType' <- convertType' retType
  foldr Agda.fun (Agda.app retType' $ Agda.hiddenArg_ $ up i)
    <$> mapM (convertType $ Just $ Agda.hiddenArg_ i) argTypes

-------------------------------------------------------------------------------
-- Lifted IR to Agda translation                                             --
-------------------------------------------------------------------------------

-- | Translates a given type in lifted IR to Agda.
--
--   If a @Size@ variable is needed, but non is provided an error will be occur.
convertType :: Maybe Agda.Expr -> LIR.Type -> Converter Agda.Expr
convertType _ (LIR.TypeVar srcSpan name) = Agda.Ident
  <$> lookupAgdaIdentOrFail srcSpan IR.TypeScope (IR.UnQual $ IR.Ident name)
convertType i (LIR.TypeCon srcSpan name typeArgs dec) = do
  typeArgs' <- mapM (convertType i) typeArgs
  constr    <- applyFreeArgs <$> lookupAgdaIdentOrFail srcSpan IR.TypeScope name
  let type' = foldl Agda.app constr $ reverse typeArgs'
  if dec
    then Agda.app type' <$> maybe (fail "No Size annotation declared!") return i
    else return type'
convertType i (LIR.FuncType _ l r) =
  Agda.fun <$> convertType i l <*> convertType i r
convertType i (LIR.FreeTypeCon _ t) = free <$> convertType i t

-- | Calls @convertType'@ without providing a @Size@ annotation.
convertType' :: LIR.Type -> Converter Agda.Expr
convertType' = convertType Nothing

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
  var <- freshAgdaVar name
  Agda.pi [Agda.unqualify var] <$> k (Agda.Ident var)
