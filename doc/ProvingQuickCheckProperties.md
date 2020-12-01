# Proving QuickCheck Properties

## Motivation

The main goal for the translation of Haskell code to Coq is to prove properties of the Haskell program in Coq.
In order to do so, we have to formulate the properties to prove first.
Due to the overhead involved with our translation, stating propositions in Coq directly is very tedious.
Therefore, we provide a mechanism for deriving Coq properties from QuickCheck properties.
This allows us to state the proposition in Haskell instead of Coq.

## Writing QuickCheck Properties

The functions from the `Test.QuickCheck` module listed below are supported by our compiler and can be used to construct properties.
In QuickCheck there is the `Testable` type class.
Since our compiler does not support type classes, the types of `Testable` arguments are instantiated with `Property`.
In order to pass boolean values to such arguments (`Bool` has a `Testable` instance), the `property` function from `Testable` is exposed for `Bool`.

 - `property :: Bool -> Property`  
   Converts a boolean value to a property that is satisfied if and only if the value is `True` and does not have an effect.
   `property b` corresponds to `b = True_ Shape Pos` in Coq.

 - `(==>) :: Bool -> Property -> Property`  
   Creates an implication in Coq (i.e., `->`).
   The premise of the implication is that the boolean value is `True` and does not have an effect (like `property`).
   The conclusion is that the second argument is a pure (i.e., effect free) computation of a property that holds.

 - `(===) :: a -> a -> Property`  
   Creates a property that tests whether the given arguments are structurally equal (i.e., `=` in Coq).
   If the arguments have effects, it must be the same one.
   Since we do not require an `Eq` instance, you can even compare functions.

 - `(=/=) :: a -> a -> Property`  
   The negation of `(===)` (i.e., `<>` in Coq).

 - `(.&&.) :: Property -> Property -> Property`  
   Creates the conjunction of the given properties (i.e., `/\` in Coq).
   Both arguments must be pure computations of properties.

 - `(.||.) :: Property -> Property -> Property`  
   Creates the disjunction of the given properties (i.e., `\/` in Coq).
   Both arguments must be pure computations of properties.

Furthermore, there is the function `quickCheck` in our Coq version of the `Test.QuickCheck` module.
In Haskell `quickCheck` is used to test whether a QuickCheck property holds and has the type
`Testable prop => prop -> IO ()`.
In Coq we are using it to convert a QuickCheck property into a Coq property (i.e., a `Prop`) that can be used in `Theorem` sentences.
The argument does not have to be a `Property` since we have recreated the `Testable` type class in Coq.
If the argument of `quickCheck` is a monadic value, it must not have an effect and is converted recursively.
If the argument is a function, the function arguments are universally quantified and the result is converted recursively.

How QuickCheck properties can be proven in Coq is demonstrated below.

## Effect-Generic Proofs

Suppose we want to prove that list concatenation is associative.
First we have to define list concatenation since `(++)` is not yet part of the version of the `Prelude` that is included with the compiler.

```haskell
append :: [a] -> [a] -> [a]
xs `append` ys = case xs of
  []      -> ys
  x : xs' -> x : (xs' `append` ys)
```

Next we write a QuickCheck property that states that `append` is associative.

```haskell
import Test.QuickCheck

prop_append_assoc :: (Eq a, Show a) => [a] -> [a] -> [a] -> Property
prop_append_assoc xs ys zs =
  xs `append` (ys `append` zs) === (xs `append` ys) `append` zs
```

> **Note:** The type class contexts are needed only to form valid  QuickCheck properties.
> If you don't want to test the properties with GHC before proving them, they can be omitted.
> They are ignored by our compiler.

Both definitions can be found in the [`Proofs.AppendAssoc`][`example/Proofs/AppendAssoc.hs`] example.
Let's first convince ourselves that this property holds by running QuickCheck.

```bash
ghci ./example/Proofs/AppendAssoc.hs
*Proofs.AppendAssoc> quickCheck prop_append_assoc
+++ OK, passed 100 tests.
```

Before we can attempt a prove in Coq, we have to translate the Haskell code to Coq and compile the generated Coq code first.

```bash
freec -o ./example/generated ./example/Proofs/AppendAssoc.hs
./tool/compile-coq.sh ./example/generated
```

We do not have to touch the generated Coq code at all.
Just create a new `.v` file where you want to write your proofs.

> **Note:** Make sure that both the base library and the generated code are visible from your newly created Coq file.
> Ideally, you create a `_CoqProject` file that sets the `Base` and `Generated` logical names appropriately.

In the newly created `.v` file we first import the generated code and the QuickCheck library.
Then we can use the `quickCheck` function to transform our QuickCheck property to a Coq property that we can proof.

```coq
From Base Require Import Test.QuickCheck.
From Generated Require Import Proofs.AppendAssoc.

Theorem append_assocs: quickCheck prop_append_assoc.
Proof.
  (* FILL IN HERE *)
Qed.
```

Use your favorite editor with Coq integration to carry out the proof.
See [`example/Proofs/AppendAssocProofs.v`][] where we have carried out the proof for `append_assocs` already.
Proving the associativity of `append` requires some auxiliary lemmas.
A simpler [example][`example/Proofs/ListFunctor.hs`] for proving a QuickCheck property can be found in [`example/Proofs/ListFunctorProofs.v`][] where we proved that lists satisfy the functor law.

## Non-Effect-Generic Proofs

The proofs above have in common that they state a property that holds regardless of the effect.
This is not always the case, though.

Consider the `reverse` function which reverses a list for example.
One would expect that reversing a list twice yields the original list, i.e., that `reverse` is its own inverse.
However, while this is true in a total setting, it is not if we consider partiality.
We can use the same approach discussed above to prove this fact.

Again we start by defining `reverse` and stating our proposition in Haskell (See [`Proofs.ReverseInvolutive`][`example/Proofs/ReverseInvolutive.hs`] for details).

```haskell
import Test.QuickCheck

reverse :: [a] -> [a]
reverse = {- ... -}

prop_reverse_involutive :: (Eq a, Show a) => [a] -> Property
prop_reverse_involutive xs = reverse (reverse xs) === xs
```

Testing `prop_reverse_involutive` using QuickCheck suggests that the property is indeed true for arbitrary input lists.

```bash
ghci ./example/Proofs/ReverseInvolutive.hs
*Proofs.ReverseInvolutive> quickCheck prop_reverse_involutive
+++ OK, passed 100 tests.
```

This happens since the `Arbitrary` instance for lists considers total values only and never yields lists of the form
`x : ⊥`.
We can prove that `reverse` is not involutive in a partial setting by instantiating `prop_reverse_involutive` with the `Maybe` monad and negating the property returned by `quickCheck`.
Furthermore, we have to use `quickCheck'` instead of `quickCheck` because we don't want the `Shape` and `Position` to be universally quantified.

```coq
From Base Require Import Free.Instance.Maybe.

Example partial_reverse_non_involutive:
  ~quickCheck' (@prop_reverse_involutive Maybe.Shape Maybe.Pos).
Proof.
  (* FILL IN HERE *)
Qed.
```

Similarly, we can prove that `reverse` is its own inverse in a total setting by instantiating `prop_reverse_involutive` with the `Identity` monad instead.

```coq
From Base Require Import Free.Instance.Identity.

Theorem total_reverse_involutive:
  quickCheck' (@prop_reverse_involutive Identity.Shape Identity.Pos).
Proof.
  (* FILL IN HERE *)
Qed.
```

As usual the full proofs can be found in [`example/Proofs/ReverseInvolutiveProofs.v`][].

[`example/Proofs/AppendAssoc.hs`]:
  ../example/Proofs/AppendAssoc.hs
  "Free Compiler Examples — Associativity of Append"
[`example/Proofs/AppendAssocProofs.v`]:
  ../example/Proofs/AppendAssocProofs.v
  "Free Compiler Examples — Associativity of Append — Proofs"

[`example/Proofs/ListFunctor.hs`]:
  ../example/Proofs/ListFunctor.hs
  "Free Compiler Examples — List Functor Laws"
[`example/Proofs/ListFunctorProofs.v`]:
  ../example/Proofs/ListFunctorProofs.v
  "Free Compiler Examples — List Functor Laws — Proofs"
[`example/Proofs/ReverseInvolutive.hs`]:
  ../example/Proofs/ReverseInvolutive.hs
  "Free Compiler Examples — Reverse is (non-)Involutive"
[`example/Proofs/ReverseInvolutiveProofs.v`]:
  ../example/Proofs/ReverseInvolutiveProofs.v
  "Free Compiler Examples — Reverse is (non-)Involutive — Proofs"
