{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, UndecidableInstances
           , FunctionalDependencies #-}

-- | This module contains a type class for monads that can be used in tests.

module FreeC.Monad.Class.Testable
  ( MonadTestable(..)
  , shouldReturn
  , shouldFail
  )
where

import           System.IO.Error                ( catchIOError
                                                , ioeGetErrorString
                                                , ioeGetFileName
                                                )
import           Test.Hspec              hiding ( shouldReturn )

import           Data.Functor.Identity          ( Identity(..) )

import           FreeC.Monad.Reporter
import           FreeC.Pretty

-- | Type class for monads which can be used in tests.
class Monad m => MonadTestable m err | m -> err where
  -- | Sets the expectation returned by the given function for the value
  --   returned by the given computation.
  shouldReturnWith :: Show a => m a -> (a -> Expectation) -> Expectation

  -- | Sets the expectation returned by the given function for the error
  --   that was produced by the given computation instead of a value.
  shouldFailWith :: Show a => m a -> (err -> Expectation) -> Expectation

-- | Sets the expectation that the given computation successfully returns
--   the given value.
shouldReturn :: (Eq a, Show a, MonadTestable m err) => m a -> a -> Expectation
shouldReturn mx y = shouldReturnWith mx (`shouldBe` y)

-- | Sets the expectation that the given computation fails without returning
--   a value.
shouldFail :: (Show a, MonadTestable m err) => m a -> Expectation
shouldFail = flip shouldFailWith (const (return ()))

-------------------------------------------------------------------------------
-- Instances for common pure monads                                          --
-------------------------------------------------------------------------------

-- | A computation in the @Identity@ monad can return a result but never fails.
instance MonadTestable Identity () where
  shouldReturnWith = flip ($) . runIdentity
  shouldFailWith _ _ =
    expectationFailure "Expected failure, but the Identity monad cannot fail."

-- | A computation in the @Maybe@ monad fails if the result is @Nothing@ and
--   succeeds if the result is @Just@ a value.
instance MonadTestable Maybe () where
  shouldReturnWith (Just x) f = f x
  shouldReturnWith Nothing _ =
    expectationFailure "Unexpected failure in Maybe monad."
  shouldFailWith Nothing f = f ()
  shouldFailWith (Just x) _ =
    expectationFailure
      $  "Expected failure in Maybe monad, "
      ++ "but the following value was produced: "
      ++ show x

-- | A computation in the @Either@ monad fails if the result is @Left@ and
--   succeeds if the result is @Right@.
instance Show err => MonadTestable (Either err) err where
  shouldReturnWith (Right x) f = f x
  shouldReturnWith (Left err) _ =
    expectationFailure $ "Unexpected failure in Either monad, got " ++ show err
  shouldFailWith (Left err) f = f err
  shouldFailWith (Right x) _ =
    expectationFailure
      $  "Expected failure in Either monad, "
      ++ "but the following value was produced: "
      ++ show x

-------------------------------------------------------------------------------
-- Instance for the IO monad                                                 --
-------------------------------------------------------------------------------

-- | An impure computation in the @IO@ monad fails if an @IO@ error is thrown.
instance MonadTestable IO IOError where
  shouldReturnWith mx f = catchIOError (mx >>= f) $ \err ->
    expectationFailure
      $  "Unexpected IO error: "
      ++ ioeGetErrorString err
      ++ maybe "" (": " ++) (ioeGetFileName err)
  shouldFailWith mx f = flip catchIOError f $ do
    x <- mx
    expectationFailure
      $  "Expected IO error, but the following value was produced: "
      ++ show x

-------------------------------------------------------------------------------
-- Instance for the reporter monad                                           --
-------------------------------------------------------------------------------

-- | A reporter fails when a fatal message is reported.
instance MonadTestable m err => MonadTestable (ReporterT m) [Message] where
  shouldReturnWith reporter setExpectation =
    shouldReturnWith (runReporterT reporter) $ \result -> case result of
      (Just x, _) -> setExpectation x
      (Nothing, ms) ->
        expectationFailure
          $  "Unexpected fatal message was reported."
          ++ "\n\nThe following "
          ++ show (length ms)
          ++ " messages were reported:\n"
          ++ showPretty ms
  shouldFailWith reporter setExpectation =
    shouldReturnWith (runReporterT reporter) $ \result -> case result of
      (Nothing, ms) -> setExpectation ms
      (Just x, ms)
        | null ms
        -> expectationFailure
          $  "Expected a fatal message to be reported. "
          ++ "But no messages were reported."
          ++ "\n\nThe following value was produced: "
          ++ show x
        | otherwise
        -> expectationFailure
          $  "Expected a fatal message to be reported. Got "
          ++ show (length ms)
          ++ " messages, none of which is fatal."
          ++ "\n\nThe following value was produced: "
          ++ show x
          ++ "\n\nThe following messages were reported:\n"
          ++ showPretty ms
