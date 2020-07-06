-- | This example is about the minimal language Hutton's Razor including
--   an evaluation function and two compilers that produce code for a simple
--   stack machine.

module Razor where

import           Test.QuickCheck

import           Proofs.AppendAssoc

-- First we define an expression of the language which is either an integer
-- value or an addition of two expressions.

data Expr =
    Val Integer
  | Add Expr Expr
 deriving (Eq, Show)

-- Now we define an evaluation function for such an expression.

eval :: Expr -> Integer
eval (Val n  ) = n
eval (Add x y) = eval x + eval y

-- Before we can write a compiler for Hutton's Razor, we need to define the
-- target machine which is a simple stack machine that can either push a value
-- on top of the stack or pop two values from the stack and push their sum.

type Stack = [Integer]
type Code = [Op]
data Op    =
    PUSH Integer
  | ADD
 deriving (Eq, Show)

-- The execution of a program works as follows.
-- Note that we make exec strict on the second argument.

exec :: Code -> Stack -> Stack
exec []           []          = []
exec []           (v : s)     = v : s
exec (PUSH n : c) []          = exec c [n]
exec (PUSH n : c) (v     : s) = exec c (n : v : s)
exec (ADD    : c) (m : n : s) = exec c (n + m : s)

-- A simple compiler for Hutton's Razor could look like this.

comp :: Expr -> Code
comp (Val n  ) = [PUSH n]
comp (Add x y) = comp x `append` comp y `append` [ADD]

-- A faster compiler can be constructed by avoiding list concatenation.

compApp :: Expr -> Code -> Code
compApp (Val n  ) c = PUSH n : c
compApp (Add x y) c = compApp x (compApp y (ADD : c))

comp' :: Expr -> Code
comp' e = compApp e []

-- Now we can define a property for the correctness of those compilers.

prop_comp_correct :: Expr -> Property
prop_comp_correct e = exec (comp e) [] === [eval e]

prop_comp'_correct :: Expr -> Property
prop_comp'_correct e = exec (comp' e) [] === [eval e]

-- We can also define the property that both compilers produce the same code.

prop_comp_comp'_eq :: Expr -> Property
prop_comp_comp'_eq e = comp e === comp' e
