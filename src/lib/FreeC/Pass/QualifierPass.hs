-- | This module contains a compiler pass that qualifies the names of all
--   top-level declarations of the converted module with the name of that
--   module.
--
--   = Example
--
--   Consider the following module.
--
--   @
--   module Data.Tree where
--
--   data Tree a = Leaf a | Branch (Tree a) (Tree a)
--
--   mapTree :: (a -> b) -> Tree a -> Tree b
--   mapTree f t = case t of
--     Leaf x     -> Leaf (f x)
--     Branch l r -> Branch (mapTree f l) (mapTree f r)
--   @
--
--   After this pass the declarations of @Tree@ and @mapTree@ as well
--   as the type signature for @mapTree@ and the constructors @Leaf@
--   and @Branch@ are qualified.
--
--   @
--   module Data.Tree where
--
--   data Data.Tree.Tree a
--     = Data.Tree.Leaf a
--     | Data.Tree.Branch (Tree a) (Tree a)
--
--   Data.Tree.mapTree :: (a -> b) -> Tree a -> Tree b
--   Data.Tree.mapTree f t = case t of
--     Leaf x     -> Leaf (f x)
--     Branch l r -> Branch (mapTree f l) (mapTree f r)
--   @
--
--   However, references to @Tree@, @Leaf@, @Branch@ and @mapTree@
--   in the fields of the constructor declarations and on the right-hand
--   side of the function's type signature and declaration remain unqualified.
--   Also (type) arguments and local variable are not affected.
--
--   = Specification
--
--   == Precondition
--
--   There are no special requirements.
--
--   == Translation
--
--   In a module @M@ all declarations, type signatures and pragmas of the forms
--
--   * @type T α₁ … αₘ = τ@
--   * @data D α₁ … αₘ = C₁ τ₍₁,₁₎ … τ₍₁,ₖ₁₎ | … | Cₙ τ₍ₙ,₁₎ … τ₍ₙ,ₖₙ₎@
--   * @f₁, …, fₙ :: τ@
--   * @f x₁ … xₙ = e@
--   * @{-\# HASKELL_TO_COQ f DECREASES ON x \#-}@
--
--   are translated to
--
--   * @type M.T α₁ … αₘ = τ@
--   * @data M.D α₁ … αₘ = M.C₁ τ₍₁,₁₎ … τ₍₁,ₖ₁₎ | … | M.Cₙ τ₍ₙ,₁₎ … τ₍ₙ,ₖₙ₎@
--   * @M.f₁, …, M.fₙ :: τ@
--   * @M.f x₁ … xₙ = e@
--   * @{-\# HASKELL_TO_COQ M.f DECREASES ON x \#-}@
--
--   If an identifier is qualified already, it keeps its original qualifier.
--
--   == Postcondition
--
--   All 'HS.DeclIdent's in the module contain qualified identifiers
--   (i.e., 'HS.Qual's).

module FreeC.Pass.QualifierPass
  ( qualifierPass
  )
where

import qualified FreeC.IR.Syntax               as HS
import           FreeC.Pass

-- | Compiler pass that qualifies the names of all declarations in the module
--   with the name of the module.
qualifierPass :: Pass HS.Module
qualifierPass = return . qualifyDecls

-- | Qualifies the names of declarations in the given module with the name
--   of the module.
qualifyDecls :: HS.Module -> HS.Module
qualifyDecls ast = ast
  { HS.modTypeDecls = map qualifyTypeDecl (HS.modTypeDecls ast)
  , HS.modTypeSigs  = map qualifyTypeSig (HS.modTypeSigs ast)
  , HS.modPragmas   = map qualifyPragma (HS.modPragmas ast)
  , HS.modFuncDecls = map qualifyFuncDecl (HS.modFuncDecls ast)
  }
 where
  -- | The name of the module to qualify the names of all declarations with.
  modName :: HS.ModName
  modName = HS.modName ast

  -- | Qualifies unqualified names with 'modName'.
  --
  --   If the name is qualified already, it remains unchanged.
  qualify :: HS.QName -> HS.QName
  qualify (     HS.UnQual name) = HS.Qual modName name
  qualify name@(HS.Qual _ _   ) = name

  -- | Qualifies the name of a declaration with 'modName'.
  qualifyDeclIdent :: HS.DeclIdent -> HS.DeclIdent
  qualifyDeclIdent declIdent =
    declIdent { HS.declIdentName = qualify (HS.declIdentName declIdent) }

  -- | Qualifies the name of the given type declaration with 'modName'.
  --
  --   If the declaration is a data type declaration, the names of its
  --   constructors are also qualified.
  qualifyTypeDecl :: HS.TypeDecl -> HS.TypeDecl
  qualifyTypeDecl decl@HS.TypeSynDecl{} =
    decl { HS.typeDeclIdent = qualifyDeclIdent (HS.typeDeclIdent decl) }
  qualifyTypeDecl decl@HS.DataDecl{} = decl
    { HS.typeDeclIdent = qualifyDeclIdent (HS.typeDeclIdent decl)
    , HS.dataDeclCons  = map qualifyConDecl (HS.dataDeclCons decl)
    }

  -- | Qualifies the name of the given constructor declaration with 'modName'.
  qualifyConDecl :: HS.ConDecl -> HS.ConDecl
  qualifyConDecl decl =
    decl { HS.conDeclIdent = qualifyDeclIdent (HS.conDeclIdent decl) }

  -- | Qualifies the function names annotated by the given type signature
  --   with 'modName'.
  qualifyTypeSig :: HS.TypeSig -> HS.TypeSig
  qualifyTypeSig typeSig = typeSig
    { HS.typeSigDeclIdents = map qualifyDeclIdent (HS.typeSigDeclIdents typeSig)
    }

  -- | Qualifies function names annotated by the given pragmas with 'modName'.
  qualifyPragma :: HS.Pragma -> HS.Pragma
  qualifyPragma (HS.DecArgPragma srcSpan funcName decArg) =
    HS.DecArgPragma srcSpan (qualify funcName) decArg

  -- | Qualifies the name of the given function declaration with 'modName'.
  qualifyFuncDecl :: HS.FuncDecl -> HS.FuncDecl
  qualifyFuncDecl decl =
    decl { HS.funcDeclIdent = qualifyDeclIdent (HS.funcDeclIdent decl) }
