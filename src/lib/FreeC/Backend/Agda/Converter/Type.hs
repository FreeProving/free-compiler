-- | Implements the lifted IR to Agda translation.

module FreeC.Backend.Agda.Converter.Type
  ( convertLiftedFuncType
  , convertLiftedConType
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
import           FreeC.IR.SrcSpan               ( SrcSpan(NoSrcSpan) )
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
convertLiftedFuncType :: [LIR.Type] -> LIR.Type -> Converter Agda.Expr
convertLiftedFuncType argTypes retType = if any decreasing argTypes
  then pi "i" $ \i -> convertLiftedType (Just $ Agda.hiddenArg_ i) funcType
  else convertLiftedType' funcType
  where funcType = LIR.funcType NoSrcSpan argTypes retType

-------------------------------------------------------------------------------
-- Constructors                                                              --
-------------------------------------------------------------------------------

-- | Converts a constructor type from lifted IR to Agda.
--
--   If the constructor contains decreasing arguments (i.e. recursive arguments),
--   a new sized type variable is bound and used to annotate these types.
convertLiftedConType :: [LIR.Type] -> LIR.Type -> Converter Agda.Expr
convertLiftedConType argTypes retType = if any decreasing argTypes
  then convertLiftedRecConType argTypes retType
  else convertLiftedType' $ LIR.funcType NoSrcSpan argTypes retType

-- | Converts a constructor from lifted IR to Agda by binding a new variable
--   @i : Size@ and annotating recursive occurrences and the return type.
convertLiftedRecConType :: [LIR.Type] -> LIR.Type -> Converter Agda.Expr
convertLiftedRecConType argTypes retType = pi "i" $ \i -> do
  retType' <- convertLiftedType' retType
  foldr Agda.fun (Agda.app retType' $ Agda.hiddenArg_ $ up i)
    <$> mapM (convertLiftedType $ Just $ Agda.hiddenArg_ i) argTypes

-------------------------------------------------------------------------------
-- Lifted IR to Agda translation                                             --
-------------------------------------------------------------------------------

-- | Translates a given type in lifted IR to Agda.
--
--   If a @Size@ variable is needed, but none is provided, an error occurs.
convertLiftedType :: Maybe Agda.Expr -> LIR.Type -> Converter Agda.Expr
convertLiftedType _ (LIR.TypeVar srcSpan name) =
  Agda.Ident
    <$> lookupAgdaIdentOrFail srcSpan IR.TypeScope (IR.UnQual $ IR.Ident name)
convertLiftedType i (LIR.TypeCon srcSpan name typeArgs dec) = do
  typeArgs' <- mapM (convertLiftedType i) typeArgs
  constr    <- applyFreeArgs <$> lookupAgdaIdentOrFail srcSpan IR.TypeScope name
  let type' = foldl Agda.app constr typeArgs'
  if dec
    then Agda.app type' <$> maybe (fail "No Size annotation declared!") return i
    else return type'
convertLiftedType i (LIR.FuncType _ l r) =
  Agda.fun <$> convertLiftedType i l <*> convertLiftedType i r
convertLiftedType i (LIR.FreeTypeCon _ t) = free <$> convertLiftedType i t

-- | Calls @convertType'@ without providing a @Size@ annotation.
convertLiftedType' :: LIR.Type -> Converter Agda.Expr
convertLiftedType' = convertLiftedType Nothing

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
