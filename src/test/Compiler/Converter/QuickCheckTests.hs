module Compiler.Converter.QuickCheckTests where

import           Test.Hspec

import           Compiler.Converter.QuickCheck
import           Compiler.Environment
import           Compiler.Monad.Converter
import           Compiler.Util.Test

-- | Utility function that imports the environment of the @Test.QuickCheck@
--   module and enables support for the translation of QuickCheck properties.
importAndEnableQuickCheck :: Converter ()
importAndEnableQuickCheck = do
  modifyEnv $ importInterface quickCheckInterface
  modifyEnv $ importInterfaceAs quickCheckModuleName quickCheckInterface
  modifyEnv $ enableQuickCheck

-- | Test group for 'convertQuickCheckProperty' tests.
testConvertQuickCheckProperty :: Spec
testConvertQuickCheckProperty =
  describe "Compiler.Converter.QuickCheck.convertQuickCheckProperty" $ do
    it "does nothing if QuickCheck support is not enabled explicitly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo
              [ "prop_add_comm :: Integer -> Integer -> Bool"
              , "prop_add_comm n m = n + m == m + n"
              ]
            $  "Definition prop_add_comm (Shape : Type) (Pos : Shape -> Type)"
            ++ "  (n : Free Shape Pos (Integer Shape Pos))"
            ++ "  (m : Free Shape Pos (Integer Shape Pos))"
            ++ " : Free Shape Pos (Bool Shape Pos)"
            ++ " := eqInteger Shape Pos"
            ++ "     (addInteger Shape Pos n m)"
            ++ "     (addInteger Shape Pos m n)."

    it "translates boolean properties correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          importAndEnableQuickCheck
          shouldTranslateDeclsTo
              [ "prop_add_comm :: Integer -> Integer -> Bool"
              , "prop_add_comm n m = n + m == m + n"
              ]
            $  "(* QuickCheck properties *) "
            ++ "Theorem prop_add_comm"
            ++ " : forall (Shape : Type)"
            ++ "          (Pos : Shape -> Type)"
            ++ "          (n : Free Shape Pos (Integer Shape Pos))"
            ++ "          (m : Free Shape Pos (Integer Shape Pos)),"
            ++ "   eqInteger Shape Pos"
            ++ "     (addInteger Shape Pos n m)"
            ++ "     (addInteger Shape Pos m n)"
            ++ "   = True_ Shape Pos. "
            ++ "Proof. (* FILL IN HERE *) Admitted."

    it "translates implications correctly" $ shouldSucceed $ fromConverter $ do
      importAndEnableQuickCheck
      "odd"  <- defineTestFunc "odd" 1 "Integer -> Bool"
      "even" <- defineTestFunc "even" 1 "Integer -> Bool"
      shouldTranslateDeclsTo
          [ "prop_odd_even :: Integer -> Property"
          , "prop_odd_even n = odd n ==> even (n + 1)"
          ]
        $  "(* QuickCheck properties *) "
        ++ "Theorem prop_odd_even"
        ++ " : forall (Shape : Type)"
        ++ "          (Pos : Shape -> Type)"
        ++ "          (n : Free Shape Pos (Integer Shape Pos)),"
        ++ "   (odd Shape Pos n = True_ Shape Pos)"
        ++ "   -> (even Shape Pos (addInteger Shape Pos n (pure 1%Z))"
        ++ "      = True_ Shape Pos). "
        ++ "Proof. (* FILL IN HERE *) Admitted."

    it "translates structural equality correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          importAndEnableQuickCheck
          "head" <- definePartialTestFunc "head" 1 "[a] -> a"
          shouldTranslateDeclsTo
              [ "prop_head :: a -> [a] -> Property"
              , "prop_head x xs = head (x : xs) === x"
              ]
            $  "(* QuickCheck properties *) "
            ++ "Theorem prop_head"
            ++ " : forall (Shape : Type)"
            ++ "          (Pos : Shape -> Type)"
            ++ "          (P : Partial Shape Pos)"
            ++ "          {a : Type}"
            ++ "          (x : Free Shape Pos a)"
            ++ "          (xs : Free Shape Pos (List Shape Pos a)),"
            ++ "   head Shape Pos P (Cons Shape Pos x xs) = x. "
            ++ "Proof. (* FILL IN HERE *) Admitted."
