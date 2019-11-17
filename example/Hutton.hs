module Hutton where

import           Test.QuickCheck

{-
  Auxiliary Definitions
-}

append :: [a] -> [a] -> [a]
append [] ys      = []
append (x:xs') ys = x : (append xs' ys)

data Expr = Val Integer | Add Expr Expr

eval :: Expr -> Integer
eval (Val n)   = n
eval (Add x y) = eval x + eval y

type Stack = [Integer]
type Code  = [Op]
data Op    = PUSH Integer | ADD

comp :: Expr -> Code
comp (Val n)   = [PUSH n]
comp (Add x y) = comp x `append` comp y `append` [ADD]

exec :: Stack -> Code -> Stack
exec s []                    = s
exec s (PUSH n : ops)        = exec (n : s) ops
exec s (ADD : ops) = case s of
                       (n : m : s' ) -> exec (n + m : s') ops

execStrict :: Stack -> Code -> Stack
execStrict s [] = s
execStrict s (PUSH n : ops) = case s of
                                []     -> execStrict [n] ops
                                (c:cs) -> execStrict (n : c :cs) ops
execStrict s (Add : ops) = case s of
                             (n : m : s') -> execStrict (n + m : s') ops

{-
 QuickCheck Properties
-}

execDistr :: Stack -> Code -> Code -> Property
execDistr s xs ys = exec s (xs `append` ys) === exec (exec s xs) ys

correctness :: Stack -> Expr -> Property
correctness s e = exec s (comp e) === eval e : s

execStrictDistr :: Stack -> Code -> Code -> Property
execStrictDistr s xs ys = execStrict s (xs `append` ys) === execStrict (execStrict s xs) ys

correctnessStrict :: Stack -> Expr -> Property
correctnessStrict s e = execStrict s (comp e) === eval e : s
