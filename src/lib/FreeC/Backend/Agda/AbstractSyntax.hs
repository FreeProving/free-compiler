{-# LANGUAGE GeneralisedNewtypeDeriving, FlexibleInstances #-}

module FreeC.Backend.Agda.AbstractSyntax
    ( module Agda.Syntax.Abstract
    , printExampleExpr
    , printExampleExpr'
    )
where

import qualified Control.Monad.Fail            as Fail
import           Control.Monad.Reader
import           Control.Monad.State

import           Data.Functor
import qualified Data.Map                      as Map

import           Agda.Interaction.Options       ( defaultOptions )

import           Agda.Syntax.Abstract
import           Agda.Syntax.Abstract.Pretty

import           Agda.Syntax.Info

import           Agda.Syntax.Literal            ( Literal(LitNat) )
import           Agda.Syntax.Position           ( Range'(NoRange) )
import           Agda.Syntax.Common             ( NameId(NameId)
                                                , defaultNamedArg
                                                )

import           Agda.TypeChecking.Monad.Base
import           Agda.TypeChecking.Monad.Builtin
import           Agda.TypeChecking.Monad.Debug

import           Agda.Utils.Monad               ( bracket_ )

import           Text.PrettyPrint.HughesPJ      ( Doc )

import           FreeC.Monad.Reporter


printExampleExpr :: IO Doc
printExampleExpr = either undefined id <$> runTCMTop (prettyATop $ exampleExpr)

printExampleExpr' :: Reporter Doc
printExampleExpr' = runCleanTCMT $ prettyATop exampleExpr

exampleExpr :: Expr
exampleExpr = Lam
    exprNoRange
    (DomainFree Nothing $ defaultNamedArg $ mkBinder_ $ mkName_ (NameId 0 0)
                                                                "foo"
    )
    (Lit $ LitNat NoRange 0)


-- Monad Boilerplate code

newtype CleanTCMT m a = CleanTCMT { unCleanTCMT :: ReaderT TCEnv (StateT TCState m) a } deriving (Functor, Applicative, Monad, MonadReader TCEnv, MonadState TCState)

runCleanTCMT :: Monad m => CleanTCMT m a -> m a
runCleanTCMT =
    flip evalStateT initState . flip runReaderT initEnv . unCleanTCMT


instance Monad m => MonadTCEnv (CleanTCMT m) where
    askTC   = ask

    localTC = local

instance Monad m => MonadTCState (CleanTCMT m) where
    getTC    = get

    modifyTC = modify

instance Monad m => ReadTCState (CleanTCMT m) where
    getTCState = get

    locallyTCState l f = bracket_ (useTC l <* modifyTCLens l f) (setTCLens l)

instance Monad m => MonadStConcreteNames (CleanTCMT m) where
    runStConcreteNames m = stateTCLensM stConcreteNames $ runStateT m

instance MonadTrans CleanTCMT where
    lift m = CleanTCMT $ ReaderT $ const $ StateT $ \s -> m <&> \a -> (a, s)

-- Mock command line options, which usually would reuqire IO.
instance Monad m => HasOptions (CleanTCMT m) where
    pragmaOptions      = useTC stPragmaOptions

    commandLineOptions = return defaultOptions

instance (Fail.MonadFail m) => Fail.MonadFail (CleanTCMT m) where
    fail msg = CleanTCMT $ fail msg

instance Monad m => HasBuiltins (CleanTCMT (ReporterT m)) where
    getBuiltinThing b = Map.lookup b <$> useTC stLocalBuiltins

-- TODO: link to reporter
instance Monad m => MonadDebug  (CleanTCMT (ReporterT m)) where
    formatDebugMessage _ _ _ = pure ""

    verboseBracket _ _ _ = id
