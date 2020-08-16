-- | This module contains functions for converting type synonym and data type
--   declarations and their constructors.
module FreeC.Backend.Coq.Converter.TypeDecl where

import           Control.Monad                    ( mapAndUnzipM )
import           Control.Monad.Extra              ( concatMapM )
import           Data.List                        ( partition )
import qualified Data.List.NonEmpty               as NonEmpty
import           Data.Maybe                       ( catMaybes )
import qualified Data.Set                         as Set

import qualified FreeC.Backend.Coq.Base           as Coq.Base
import           FreeC.Backend.Coq.Converter.Arg
import           FreeC.Backend.Coq.Converter.Free
import           FreeC.Backend.Coq.Converter.Type
import qualified FreeC.Backend.Coq.Syntax         as Coq
import           FreeC.Environment
import           FreeC.IR.DependencyGraph
import qualified FreeC.IR.Syntax                  as IR
import           FreeC.IR.TypeSynExpansion
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Strongly Connected Components                                             --
-------------------------------------------------------------------------------
-- | Converts a strongly connected component of the type dependency graph.
convertTypeComponent
  :: DependencyComponent IR.TypeDecl -> Converter [ Coq.Sentence ]
convertTypeComponent (NonRecursive decl)
  | isTypeSynDecl decl = convertTypeSynDecl decl
  | otherwise = convertDataDecls [decl]
convertTypeComponent (Recursive decls)   = do
  let (typeSynDecls, dataDecls) = partition isTypeSynDecl decls
      typeSynDeclQNames         = Set.fromList
        (map IR.typeDeclQName typeSynDecls)
  sortedTypeSynDecls <- sortTypeSynDecls typeSynDecls
  expandedDataDecls <- mapM
    (expandAllTypeSynonymsInDeclWhere (`Set.member` typeSynDeclQNames))
    dataDecls
  dataDecls' <- convertDataDecls expandedDataDecls
  typeSynDecls' <- concatMapM convertTypeSynDecl sortedTypeSynDecls
  return (dataDecls' ++ typeSynDecls')

-- | Sorts type synonym declarations topologically.
--
--   After filtering type synonym declarations from the a strongly connected
--   component, they are not mutually dependent on each other anymore (expect
--   if they form a cycle). However, type synonyms may still depend on other
--   type synonyms from the same strongly connected component. Therefore we
--   have to sort the declarations in reverse topological order.
sortTypeSynDecls :: [ IR.TypeDecl ] -> Converter [ IR.TypeDecl ]
sortTypeSynDecls = mapM fromNonRecursive . groupTypeDecls

-- | Extracts the single type synonym declaration from a strongly connected
--   component of the type dependency graph.
--
--   Reports a fatal error if the component contains mutually recursive
--   declarations (i.e. type synonyms form a cycle).
fromNonRecursive :: DependencyComponent IR.TypeDecl -> Converter IR.TypeDecl
fromNonRecursive (NonRecursive decl) = return decl
fromNonRecursive (Recursive decls)   = reportFatal
  $ Message (IR.typeDeclSrcSpan (head decls)) Error
  $ "Type synonym declarations form a cycle: "
  ++ showPretty (map IR.typeDeclIdent decls)

-------------------------------------------------------------------------------
-- Type Synonym Declarations                                                 --
-------------------------------------------------------------------------------
-- | Tests whether the given declaration is a type synonym declaration.
isTypeSynDecl :: IR.TypeDecl -> Bool
isTypeSynDecl (IR.TypeSynDecl _ _ _ _) = True
isTypeSynDecl (IR.DataDecl _ _ _ _)    = False

-- | Converts a Haskell type synonym declaration to Coq.
convertTypeSynDecl :: IR.TypeDecl -> Converter [ Coq.Sentence ]
convertTypeSynDecl decl@(IR.TypeSynDecl _ _ typeVarDecls typeExpr) = localEnv
  $ do
    let name = IR.typeDeclQName decl
    Just qualid <- inEnv $ lookupIdent IR.TypeScope name
    typeVarDecls' <- convertTypeVarDecls Coq.Explicit typeVarDecls
    typeExpr' <- convertType' typeExpr
    return [ Coq.definitionSentence qualid
               (genericArgDecls Coq.Explicit ++ typeVarDecls')
               (Just Coq.sortType) typeExpr'
           ]
-- Data type declarations are not allowed in this function.
convertTypeSynDecl (IR.DataDecl _ _ _ _)
  = error "convertTypeSynDecl: Data type declaration not allowed."

-------------------------------------------------------------------------------
-- Data type declarations                                                    --
-------------------------------------------------------------------------------
-- | Converts multiple (mutually recursive) Haskell data type declaration
--   declarations.
--
--   Before the declarations are actually translated, their identifiers are
--   inserted into the current environment. Otherwise the data types would
--   not be able to depend on each other. The identifiers for the constructors
--   are inserted into the current environment as well. This makes the
--   constructors more likely to keep their original name if there is a type
--   variable with the same (lowercase) name.
--
--   After the @Inductive@ sentences for the data type declarations there
--   is one @Arguments@ sentence and one smart constructor declaration for
--   each constructor declaration of the given data types.
convertDataDecls :: [ IR.TypeDecl ] -> Converter [ Coq.Sentence ]
convertDataDecls dataDecls = do
  (indBodies, extraSentences) <- mapAndUnzipM convertDataDecl dataDecls
  return
    (Coq.comment ("Data type declarations for "
                  ++ showPretty (map IR.typeDeclName dataDecls))
     : Coq.InductiveSentence (Coq.Inductive (NonEmpty.fromList indBodies) [])
     : concat extraSentences)

-- | Converts a Haskell data type declaration to the body of a Coq @Inductive@
--   sentence, the @Arguments@ sentences for it's constructors and the smart
--   constructor declarations.
--
--   Type variables declared by the data type or the smart constructors are
--   not visible outside of this function.
convertDataDecl :: IR.TypeDecl -> Converter (Coq.IndBody, [ Coq.Sentence ])
convertDataDecl (IR.DataDecl _ (IR.DeclIdent _ name) typeVarDecls conDecls) = do
  (body, argumentsSentences) <- generateBodyAndArguments
  smartConDecls <- mapM generateSmartConDecl conDecls
  return
    ( body
    , Coq.comment ("Arguments sentences for " ++ showPretty (IR.toUnQual name))
        : argumentsSentences
        ++ Coq.comment
        ("Smart constructors for " ++ showPretty (IR.toUnQual name))
        : smartConDecls
    )
 where
   -- | Generates the body of the @Inductive@ sentence and the @Arguments@
   --   sentences for the constructors but not the smart constructors
   --   of the data type.
   --
   --   Type variables declared by the data type declaration are visible to the
   --   constructor declarations and @Arguments@ sentences created by this
   --   function, but not outside this function. This allows the smart
   --   constructors to reuse the identifiers for their type arguments (see
   --   'generateSmartConDecl').
   generateBodyAndArguments :: Converter (Coq.IndBody, [ Coq.Sentence ])
   generateBodyAndArguments = localEnv
     $ do
       Just qualid <- inEnv $ lookupIdent IR.TypeScope name
       typeVarDecls' <- convertTypeVarDecls Coq.Explicit typeVarDecls
       conDecls' <- mapM convertConDecl conDecls
       argumentsSentences <- mapM generateArgumentsSentence conDecls
       return
         ( Coq.IndBody qualid (genericArgDecls Coq.Explicit ++ typeVarDecls')
             Coq.sortType conDecls'
         , argumentsSentences
         )

   -- | Converts a constructor of the data type.
   convertConDecl
     :: IR.ConDecl -> Converter (Coq.Qualid, [ Coq.Binder ], Maybe Coq.Term)
   convertConDecl (IR.ConDecl _ (IR.DeclIdent _ conName) args) = do
     Just conQualid <- inEnv $ lookupIdent IR.ValueScope conName
     Just returnType <- inEnv $ lookupReturnType IR.ValueScope conName
     args' <- mapM convertType args
     returnType' <- convertType' returnType
     return (conQualid, [], Just (args' `Coq.arrows` returnType'))

   -- | Generates the @Arguments@ sentence for the given constructor declaration.
   generateArgumentsSentence :: IR.ConDecl -> Converter Coq.Sentence
   generateArgumentsSentence (IR.ConDecl _ (IR.DeclIdent _ conName) _) = do
     Just qualid <- inEnv $ lookupIdent IR.ValueScope conName
     let typeVarNames = map IR.typeVarDeclQName typeVarDecls
     typeVarQualids <- mapM (inEnv . lookupIdent IR.TypeScope) typeVarNames
     return (Coq.ArgumentsSentence
             (Coq.Arguments Nothing qualid
              [Coq.ArgumentSpec Coq.ArgMaximal (Coq.Ident typeVarQualid) Nothing
              | typeVarQualid
              <- map fst Coq.Base.freeArgs ++ catMaybes typeVarQualids
              ]))

   -- | Generates the smart constructor declaration for the given constructor
   --   declaration.
   generateSmartConDecl :: IR.ConDecl -> Converter Coq.Sentence
   generateSmartConDecl (IR.ConDecl _ declIdent argTypes) = localEnv
     $ do
       let conName = IR.declIdentName declIdent
       Just qualid <- inEnv $ lookupIdent IR.ValueScope conName
       Just smartQualid <- inEnv $ lookupSmartIdent conName
       Just returnType <- inEnv $ lookupReturnType IR.ValueScope conName
       typeVarDecls' <- convertTypeVarDecls Coq.Implicit typeVarDecls
       (argIdents', argDecls') <- mapAndUnzipM convertAnonymousArg
         (map Just argTypes)
       returnType' <- convertType returnType
       rhs <- generatePure
         (Coq.app (Coq.Qualid qualid) (map Coq.Qualid argIdents'))
       return (Coq.definitionSentence smartQualid
               (genericArgDecls Coq.Explicit ++ typeVarDecls' ++ argDecls')
               (Just returnType') rhs)
-- Type synonyms are not allowed in this function.
convertDataDecl (IR.TypeSynDecl _ _ _ _)
  = error "convertDataDecl: Type synonym not allowed."
