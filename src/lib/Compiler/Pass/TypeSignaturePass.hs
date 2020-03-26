-- | This module contains a compiler pass that associates top-level type
--   signatures with the corresponding function declarations.
--
--   = Examples
--
--   == Example 1
--
--   For example, the following module that declares an unary function @null@
--   with a type signature
--
--   @
--   null :: forall a. [a] -> Bool
--   null xs = case xs of { [] -> True; x : xs' -> False }
--   @
--
--   will be be converted to a module that still contains the type signature
--   but the types of the argument @xs@ and the return type of @head@ are
--   also annotated explicitly in the function declaration itself.
--   In addition, the type arguments of the type schema are copied from the type
--   signature to the function declaration's type argument list.
--
--   @
--   null :: forall a. [a] -> Bool
--   null @a (xs :: [a]) = (case xs of { [] -> True; x : xs' -> False }) :: Bool
--   @
--
--   == Example 2
--
--   The type signature of an @n@-ary function declaration must not necessarily
--   be a function type with @n-1@ arrows. For example, the type signature
--   could contain type synonyms.
--
--   @
--   type Subst = String -> Expr
--
--   identity :: Subst
--   identity x = Var x
--   @
--
--   In this case, the type synonym needs to be expanded in order to determine
--   the type of the argument @x@ and the return type of @identity@.
--
--   @
--   type Subst = String -> Expr
--
--   identity :: Subst
--   identity (x :: String) = Var x :: Expr
--   @
--
--   The original type signature is left unchanged (not expanded) and type
--   synonyms are only expanded when necessary.
--
--   = Specification
--
--   == Preconditions
--
--   The environment contains entries for all type synonyms.
--   Otherwise this pass fails if a type synonym needs to be expanded to
--   determine the type of an argument.
--
--   == Translation
--
--   The declaration of every @n@-ary function @f@
--
--   @
--   f x₁ … xₙ = e
--   @
--
--   for which there exists a top-level type signature
--
--   @
--   …, f, … :: forall α₁ … αₘ. τ
--   @
--
--   will be converted into a function declaration with explicit type
--   annotations and type arguments
--
--   @
--   f @α₁ … @αₘ (x₁ :: τ₁) … (xₙ :: τₙ) = e :: τ'
--   @
--
--   where @τ₁ -> … -> τₙ -> τ@ is the smallest type that can be derived
--   from @τ@ by expanding type synonyms.
--
--   == Postconditions
--
--   The argument and return types of every function declaration that has a
--   top-level type signature are annotated explicitly.
--
--   == Error cases
--
--   * A fatal error is reported if the type of an argument cannot be
--     determined because a type synonym could not be expanded.
--
--   * A fatal error is reported if there are multiple type signatures for the
--     same function declaration.
--
--   * A warning is reported if there is a type signature without accompanying
--     function declaration.

module Compiler.Pass.TypeSignaturePass
  ( typeSignaturePass
  )
where

import           Control.Monad                  ( when )
import           Data.List                      ( intercalate )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set

import qualified Compiler.IR.Syntax            as HS
import           Compiler.Haskell.Inliner
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pass
import           Compiler.Pretty

-- | Associates top-level type signatures with the corresponding function
--   declarations in the given module.
typeSignaturePass :: Pass HS.Module
typeSignaturePass ast = do
  let typeSigs  = HS.modTypeSigs ast
      funcDecls = HS.modFuncDecls ast
  mapM_ (checkHasBinding funcDecls) typeSigs
  funcDecls' <- addTypeSigsToFuncDecls typeSigs funcDecls
  return ast { HS.modFuncDecls = funcDecls' }

-------------------------------------------------------------------------------
-- Checks                                                                    --
-------------------------------------------------------------------------------

-- | Checks whether there is a function declaration for all functions
--   annotated by the given type signature.
--
--   Reports a warning is there is a type signature without accompanying
--   function declaration.
checkHasBinding :: [HS.FuncDecl] -> HS.TypeSig -> Converter ()
checkHasBinding funcDecls = mapM_ checkHasBinding' . HS.typeSigDeclIdents
 where
  -- | The names of all declared functions.
  funcDeclNames :: Set HS.QName
  funcDeclNames = Set.fromList $ map HS.funcDeclQName funcDecls

  -- | Checks whether there is a function declaration for the function
  --   with the given name.
  checkHasBinding' :: HS.DeclIdent -> Converter ()
  checkHasBinding' (HS.DeclIdent srcSpan name) =
    when (name `Set.notMember` funcDeclNames)
      $ reportMissingBinding srcSpan name

-------------------------------------------------------------------------------
-- Translation                                                               --
-------------------------------------------------------------------------------

-- | Annotates the given function declarations with the type from the
--   corresponding type signature.
--
--   Reports a fatal error if the type of an argument cannot be inferred from
--   the type signature (see 'splitFuncType') or there are multiple type
--   signatures for the same function.
addTypeSigsToFuncDecls
  :: [HS.TypeSig] -> [HS.FuncDecl] -> Converter [HS.FuncDecl]
addTypeSigsToFuncDecls typeSigs funcDecls = mapM addTypeSigToFuncDecl funcDecls
 where
  -- | Maps the names of functions to their annotated type.
  typeSigMap :: Map HS.QName [HS.TypeSchema]
  typeSigMap = Map.fromListWith
    (++)
    [ (name, [typeSchema])
    | HS.TypeSig _ declIdents typeSchema <- typeSigs
    , HS.DeclIdent _ name                <- declIdents
    ]

  -- | Sets the type annotation of the given variable pattern.
  setVarPatType :: HS.VarPat -> HS.Type -> HS.VarPat
  setVarPatType arg argType = arg { HS.varPatType = Just argType }

  -- | Annotates the given function declaration with the type from the
  --   corresponding type signature.
  addTypeSigToFuncDecl :: HS.FuncDecl -> Converter HS.FuncDecl
  addTypeSigToFuncDecl funcDecl = do
    let name = HS.funcDeclQName funcDecl
        args = HS.funcDeclArgs funcDecl
    case Map.lookup name typeSigMap of
      Nothing -> return funcDecl
      Just [HS.TypeSchema _ typeArgs typeExpr] -> do
        (argTypes, retType) <- splitFuncType name args typeExpr
        return funcDecl { HS.funcDeclTypeArgs = typeArgs
                        , HS.funcDeclArgs = zipWith setVarPatType args argTypes
                        , HS.funcDeclReturnType = Just retType
                        }
      Just typeSchemas -> reportDuplicateTypeSigs
        (HS.funcDeclSrcSpan funcDecl)
        name
        (map HS.typeSchemaSrcSpan typeSchemas)

-- | Splits the annotated type of a Haskell function with the given arguments
--   into its argument and return types.
--
--   Type synonyms are expanded if necessary. Reports a fatal error if a type
--   synonym could not be expanded.
splitFuncType
  :: HS.QName    -- ^ The name of the function to display in error messages.
  -> [HS.VarPat] -- ^ The argument variable patterns whose types to split of.
  -> HS.Type     -- ^ The type to split.
  -> Converter ([HS.Type], HS.Type)
splitFuncType name = splitFuncType'
 where
  splitFuncType' :: [HS.VarPat] -> HS.Type -> Converter ([HS.Type], HS.Type)
  splitFuncType' []         typeExpr              = return ([], typeExpr)
  splitFuncType' (_ : args) (HS.FuncType _ t1 t2) = do
    (argTypes, returnType) <- splitFuncType' args t2
    return (t1 : argTypes, returnType)
  splitFuncType' args@(arg : _) typeExpr = do
    typeExpr' <- expandTypeSynonym typeExpr
    if typeExpr == typeExpr'
      then reportTypeSynExpansionError name arg
      else splitFuncType' args typeExpr'

-------------------------------------------------------------------------------
-- Error messages                                                            --
-------------------------------------------------------------------------------

-- | Warns the user that there is no function declaration for the type
--   signature of the function with the given name.
reportMissingBinding
  :: MonadReporter r
  => SrcSpan  -- ^ The location of the type signature.
  -> HS.QName -- ^ The name of the function.
  -> r ()
reportMissingBinding srcSpan name =
  report
    $  Message srcSpan Warning
    $  "The type signature for '"
    ++ showPretty name
    ++ "' lacks an accompanying binding."

-- | Reports a fatal error if there are multiple type signatures for the
--   same function declaration.
reportDuplicateTypeSigs
  :: MonadReporter r
  => SrcSpan   -- ^ The location of the function declaration.
  -> HS.QName  -- ^ The name of the function.
  -> [SrcSpan] -- ^ The locations of the type signatures.
  -> r a
reportDuplicateTypeSigs srcSpan funcName typeSigSrcSpans =
  reportFatal
    $  Message srcSpan Error
    $  "Duplicate type signatures for '"
    ++ showPretty funcName
    ++ "' at "
    ++ intercalate ", " (map showPretty typeSigSrcSpans)

-- | Reports a fatal error if the type of a function argument cannot be
--   determined by expanding a type synonyms from its type signature.
reportTypeSynExpansionError
  :: MonadReporter r
  => HS.QName  -- ^ The name of the function.
  -> HS.VarPat -- ^ The argument whose argument type could not be determined.
  -> r a
reportTypeSynExpansionError funcName arg =
  reportFatal
    $  Message (HS.varPatSrcSpan arg) Error
    $  "Could not determine type of argument '"
    ++ HS.varPatIdent arg
    ++ "' for function '"
    ++ showPretty funcName
    ++ "'."
