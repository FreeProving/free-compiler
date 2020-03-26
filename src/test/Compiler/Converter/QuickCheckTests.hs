module Compiler.Converter.QuickCheckTests where

import           Test.Hspec

import           Compiler.Converter.QuickCheck
import           Compiler.Monad.Converter
import           Compiler.Util.Test

-- | Utility function that makes the test entry module 'testEntryModuleName'
--   reexport all entries from the @Test.QuickCheck@ module.
importQuickCheck :: Converter ()
importQuickCheck = importTestModule quickCheckModuleName

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
          importQuickCheck
          shouldTranslateDeclsTo
              [ "prop_add_comm :: Integer -> Integer -> Property"
              , "prop_add_comm n m = property (n + m == m + n)"
              ]
            $  "(* QuickCheck properties *) "
            ++ "Theorem prop_add_comm"
            ++ " : forall (Shape : Type)"
            ++ "          (Pos : Shape -> Type)"
            ++ "          (n : Free Shape Pos (Integer Shape Pos))"
            ++ "          (m : Free Shape Pos (Integer Shape Pos)),"
            ++ "   isPureTrue Shape Pos"
            ++ "     (eqInteger Shape Pos"
            ++ "        (addInteger Shape Pos n m)"
            ++ "        (addInteger Shape Pos m n)). "
            ++ "Proof. (* FILL IN HERE *) Admitted."

    it "translates implications correctly" $ shouldSucceed $ fromConverter $ do
      importQuickCheck
      "odd"  <- defineTestFunc "odd" 1 "Integer -> Bool"
      "even" <- defineTestFunc "even" 1 "Integer -> Bool"
      shouldTranslateDeclsTo
          [ "prop_odd_even :: Integer -> Property"
          , "prop_odd_even n = odd n ==> property (even (n + 1))"
          ]
        $  "(* QuickCheck properties *) "
        ++ "Theorem prop_odd_even"
        ++ " : forall (Shape : Type)"
        ++ "          (Pos : Shape -> Type)"
        ++ "          (n : Free Shape Pos (Integer Shape Pos)),"
        ++ "   precondition Shape Pos"
        ++ "     (odd Shape Pos n)"
        ++ "     (isPureTrue Shape Pos"
        ++ "        (even Shape Pos (addInteger Shape Pos n (pure 1%Z)))). "
        ++ "Proof. (* FILL IN HERE *) Admitted."

    it "translates structural equality correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          importQuickCheck
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
            ++ "   @eqProp Shape Pos a"
            ++ "     (@head Shape Pos P a (@Cons Shape Pos a x xs))"
            ++ "     x. "
            ++ "Proof. (* FILL IN HERE *) Admitted."

    it "translates equality for partially applied functions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          importQuickCheck
          "map" <- defineTestFunc "map" 2 "(a -> b) -> [a] -> [b]"
          "id"  <- defineTestFunc "id" 1 "a -> a"
          shouldTranslateDeclsTo
              ["prop_map_id :: Property", "prop_map_id = map id === id"]
            $  "(* QuickCheck properties *) "
            ++ "Theorem prop_map_id"
            ++ " : forall (Shape : Type)"
            ++ "          (Pos : Shape -> Type)"
            ++ "          {t0 : Type},"
            ++ "   @eqProp Shape Pos (Free Shape Pos (List Shape Pos t0)"
            ++ "                      -> Free Shape Pos (List Shape Pos t0))"
            ++ "     (pure (fun x_0 => @map Shape Pos t0 t0"
            ++ "        (pure (fun x_1 => @id Shape Pos t0 x_1))"
            ++ "        x_0))"
            ++ "     (pure (fun x_0 => @id Shape Pos (List Shape Pos t0) x_0)). "
            ++ "Proof. (* FILL IN HERE *) Admitted."
