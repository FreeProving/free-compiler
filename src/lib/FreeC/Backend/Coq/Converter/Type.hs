-- | This module contains functions for converting Haskell types to Coq.

module FreeC.Backend.Coq.Converter.Type where

import qualified FreeC.Backend.Coq.Base        as Coq.Base
import           FreeC.Backend.Coq.Converter.Free
import qualified FreeC.Backend.Coq.Syntax      as Coq
import           FreeC.Environment.LookupOrFail
import qualified FreeC.IR.Syntax               as IR
import           FreeC.LiftedIR.Converter.Type
import qualified FreeC.LiftedIR.Syntax         as LIR
import           FreeC.Monad.Converter

-------------------------------------------------------------------------------
-- IR to Coq translation                                                     --
-------------------------------------------------------------------------------

-- | Converts a type from IR to Coq, lifting it into the @Free@ monad.
--
--   [\(\tau^\dagger = Free\,Shape\,Pos\,\tau^*\)]
--     A type \(\tau\) is converted by lifting it into the @Free@ monad and
--     recursively converting the argument and return types of functions
--     using 'convertType''.
convertType :: IR.Type -> Converter Coq.Term
convertType = convertLiftedType . liftType

-- | Converts a type from IR to Coq.
--
--   In contrast to 'convertType', the type itself is not lifted into the
--   @Free@ monad. Only the argument and return types of the contained function
--   type constructors are lifted recursively.
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
convertType' = convertLiftedType . liftType'

-------------------------------------------------------------------------------
-- Lifted IR to Coq translation                                              --
-------------------------------------------------------------------------------

-- | Converts a given type in the lifted IR to a Coq term.
convertLiftedType :: LIR.Type -> Converter Coq.Term
convertLiftedType (LIR.TypeVar srcSpan ident) = do
  qualid <- lookupIdentOrFail srcSpan IR.TypeScope (IR.UnQual (IR.Ident ident))
  return $ Coq.Qualid qualid
convertLiftedType (LIR.TypeCon srcSpan name args _) = do
  qualid <- lookupIdentOrFail srcSpan IR.TypeScope name
  args'  <- mapM convertLiftedType args
  return $ genericApply qualid [] [] args'
convertLiftedType (LIR.FuncType _ l r) = do
  l' <- convertLiftedType l
  r' <- convertLiftedType r
  return $ Coq.Arrow l' r'
convertLiftedType (LIR.FreeTypeCon _ t) = do
  t' <- convertLiftedType t
  return $ genericApply Coq.Base.free [] [] [t']
