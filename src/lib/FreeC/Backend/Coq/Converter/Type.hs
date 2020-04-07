-- | This module contains functions for converting Haskell types to Coq.

module FreeC.Backend.Coq.Converter.Type where

import qualified FreeC.Backend.Coq.Base        as Coq.Base
import           FreeC.Backend.Coq.Converter.Free
import qualified FreeC.Backend.Coq.Syntax      as Coq
import           FreeC.Environment.LookupOrFail
import           FreeC.Environment.Scope
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter

-- | Converts a Haskell type to Coq, lifting it into the @Free@ monad.
--
--   [\(\tau^\dagger = Free\,Shape\,Pos\,\tau^*\)]
--     A type \(\tau\) is converted by lifting it into the @Free@ monad and
--     recursivly converting the argument and return types of functions
--     using 'convertType''.
convertType :: IR.Type -> Converter Coq.Term
convertType t = do
  t' <- convertType' t
  return (genericApply Coq.Base.free [] [] [t'])

-- | Converts a Haskell type to Coq.
--
--   In contrast to 'convertType', the type itself is not lifted into the
--   @Free@ moand. Only the argument and return types of contained function
--   type constructors are lifted recursivly.
--
--   [\(\alpha^* = \alpha'\)]
--     A type variable \(\alpha\) is translated by looking up the corresponding
--     Coq identifier \(\alpha'\).
--
--   [\(T^* = T'\,Shape\,Pos\)]
--     A type constructor \(T\) is translated by looking up the corresponding
--     Coq identifier \(T'\) and adding the parameters \(Shape\) and \(Pos\).
--
--   [\((\tau_1\,\tau_2)^* = \tau_1^*\,\tau_2^*\)]
--     Type constructor applications are translated recursively but
--     remain unchanged otherwise.
--
--   [\((\tau_1 \rightarrow \tau_2)^* = \tau_1^\dagger \rightarrow \tau_2^\dagger\)]
--     Type constructor applications are translated recursively but
--     remain unchanged otherwise.
convertType' :: IR.Type -> Converter Coq.Term
convertType' (IR.TypeVar srcSpan ident) = do
  qualid <- lookupIdentOrFail srcSpan TypeScope (IR.UnQual (IR.Ident ident))
  return (Coq.Qualid qualid)
convertType' (IR.TypeCon srcSpan name) = do
  qualid <- lookupIdentOrFail srcSpan TypeScope name
  return (genericApply qualid [] [] [])
convertType' (IR.TypeApp _ t1 t2) = do
  t1' <- convertType' t1
  t2' <- convertType' t2
  return (Coq.app t1' [t2'])
convertType' (IR.FuncType _ t1 t2) = do
  t1' <- convertType t1
  t2' <- convertType t2
  return (Coq.Arrow t1' t2')
