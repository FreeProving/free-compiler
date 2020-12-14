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
   Converts a boolean value to a property that is satisfied if and only if the value is `True`.
   If the computation of the boolean value has an effect, the meaning of the property depends on the chosen effect handler.

 - `(==>) :: Bool -> Property -> Property`  
   Creates an implication in Coq (i.e., `->`).
   The premise of the implication is that the boolean value is `True` (like `property`).
   The conclusion is that the property derived from the second argument holds.
   If the computation of the premise or conclusion has an effect, their meaning depends on the chosen effect handler.
   Effects in the premise are handled independently of effects in the conclusion.

 - `(===) :: a -> a -> Property`  
   Creates a property that tests whether the results of handling the given arguments are structurally equal (i.e., `=` in Coq).
   Since we do not require an `Eq` instance, you can even compare functions.

 - `(=/=) :: a -> a -> Property`  
   The negation of `(===)` (i.e., `<>` in Coq).

 - `(.&&.) :: Property -> Property -> Property`  
   Creates the conjunction of the given properties (i.e., `/\` in Coq).
   When one of the arguments is not a pure computation, the interpretation of the resulting property depends on the chosen effect handler.

 - `(.||.) :: Property -> Property -> Property`  
   Creates the disjunction of the given properties (i.e., `\/` in Coq).
   When one of the arguments is not a pure computation, the interpretation of the resulting property depends on the chosen effect handler.

## Converting QuickCheck Properties To Coq

In addition to the functions listed in the previous section, there is the function `quickCheck` in our Coq version of the `Test.QuickCheck` module.
In Haskell `quickCheck` is used to test whether a QuickCheck property holds and has the type
`Testable prop => prop -> IO ()`.
In Coq we are using it to convert a QuickCheck property into a Coq property (i.e., a `Prop`) that can be used in `Theorem` sentences.
The argument does not have to be a `Property` since we have recreated the `Testable` type class in Coq.
If the argument is a function, the function arguments are universally quantified and the result is converted recursively.

```coq
Theorem foo: quickCheck prop_foo.
```

If the construction of a property involves an effect, the interpretation of the resulting Coq property depends on the chosen effect handler.
In case of `quickCheck`, the effect handler is always instantiated with `NoHandler` which leaves the computation tree unchanged and interprets a property as `False` when its construction has an effect.
For example, the following property is `False` under the `NoHandler`.

```coq
prop_undefined :: Property
prop_undefined = undefined
```

In order to choose a different interpretation, use the `quickCheckHandle` function.
It has an additional parameter for the effect handler.
The following effect handlers are available for common combinations of effects.

| Effect Handler                  | Effect Stack                                  | Result                              | Interpretation of Impure Properties                                                                                                 |
|---------------------------------|-----------------------------------------------|-------------------------------------|-------------------------------------------------------------------------------------------------------------------------------------|
| `HandlerNoEffect`               | `Identity`                                    | `A`                                 | There are no impure values                                                                                                          |
| `HandlerShare`                  | `Share :+: Identity`                          | `A`                                 | Shared properties are evaluated at most once                                                                                        |
|  **Partiality**                 |                                               |                                     |                                                                                                                                     |
| `HandlerMaybe`                  | `Maybe :+: Identity`                          | `option A`                          | `undefined` properties are `False`                                                                                                  |
| `HandlerShareMaybe`             | `Share :+: Maybe :+: Identity`                | `option A`                          | `undefined` properties are `False`                                                                                                  |
| `HandlerError`                  | `Error :+: Identity`                          | `A + string`                        | Properties with `error`s are `False`                                                                                                |
| `HandlerShareError`             | `Share :+: Error :+: Identity`                | `A + string`                        | Properties with `error`s are `False`                                                                                                |
| **Non-Determinism**             |                                               |                                     |                                                                                                                                     |
| `HandlerND`                     | `ND :+: Identity`                             | `list A`                            | All properties must be satisfied, empty choices are `True`                                                                          |
| `HandlerShareND`                | `Share :+: ND :+: Identity`                   | `list A`                            | All properties must be satisfied, empty choices are `True`                                                                          |
| `HandlerNDMaybe`                | `ND :+: Maybe :+: Identity`                   | `option (list A)`                   | All properties must be satisfied, empty choices are `True`, but `undefined` properties are `False`                                  |
| `HandlerShareNDMaybe`           | `Share :+: ND :+: Maybe :+: Identity`         | `option (list A)`                   | All properties must be satisfied, empty choices are `True`, but `undefined` properties are `False`                                  |
| `HandlerNDError`                | `ND :+: Error :+: Identity`                   | `list A + string`                   | All properties must be satisfied, empty choices are `True`, but properties with `error`s are `False`                                |
| `HandlerShareNDError`           | `Share :+: ND :+: Error :+: Identity`         | `list A + string`                   | All properties must be satisfied, empty choices are `True`, but properties with `error`s are `False`                                |
| **Tracing**                     |                                               |                                     |                                                                                                                                     |
| `HandlerTrace`                  | `Trace :+: Identity`                          | `A * list string`                   | Logged messages are discarded                                                                                                       |
| `HandlerShareTrace`             | `Share :+: Trace :+: Identity`                | `A * list string`                   | Logged messages are discarded                                                                                                       |
| `HandlerMaybeTrace`             | `Maybe :+: Trace :+: Identity`                | `option A * list string`            | Logged messages are discarded, `undefined` properties are `False`                                                                   |
| `HandlerMaybeShareTrace`        | `Maybe :+: Share :+: Trace :+: Identity`      | `option A * list string`            | Logged messages are discarded, `undefined` properties are `False`                                                                   |
| `HandlerErrorTrace`             | `Error :+: Trace :+: Identity`                | `(A + string) * list string`        | Logged messages are discarded, properties with `error`s are `False`                                                                 |
| `HandlerErrorShareTrace`        | `Error :+: Share :+: Trace :+: Identity`      | `(A + string) * list string`        | Logged messages are discarded, properties with `error`s are `False`                                                                 |
| **Tracing and Non-Determinism** |                                               |                                     |                                                                                                                                     |
| `HandlerTraceND`                | `Trace :+: ND :+: Identity`                   | `list (A * list string)`            | Logged messages are discarded, all properties must be satisfied, empty choices are `True`                                           |
| `HandlerNDMaybeTrace`           | `ND :+: Maybe :+: Trace :+: Identity`         | `option (list A) * string string`   | Logged messages are discarded, all properties must be satisfied, empty choices are `True`, but `undefined` properties are `False`   |
| `HandlerNDErrorTrace`           | `ND :+: Error :+: Trace :+: Identity`         | `(list A + string) * string string` | Logged messages are discarded, all properties must be satisfied, empty choices are `True`, but properties with `error`s are `False` |

In contrast to `NoHandler` all handlers above are normalizing (where `A` is the normalized result type), i.e., all nested computations in the result are forced recursively.
For example, the property `[undefined] === undefined` does not hold with `NoHandler` because the left-hand side is pure and the right-hand side is impure.
But when another handler is used, the single element of `[undefined]` is forced which results in the left-hand side to evaluate to `undefined`, too.

## Selecting Evaluation Strategies

The compiler generates code that can be evaluated with arbitrary evaluation strategies that can be selected at runtime.
By default, properties are universally quantified over the evaluation strategy.
The evaluation `Strategy` type is an inductive data type with three constructors — one for every supported strategy.
Additionally there are smart constructors that take the `Shape` and `Pos`ition explicitly like all other constructors in our framework.

| Evaluation Strategy | Constructor | Smart Constructor  |
|---------------------|-------------|--------------------|
| Call-By-Name        | `cbn`       | `Cbn Shape Pos`    |
| Call-By-Need        | `cbneed`    | `Cbneed Shape Pos` |
| Call-By-Value       | `cbv`       | `Cbv Shape Pos`    |

You can `destruct` the evaluation strategy in order to prove a property that holds for every evaluation strategy.
However, most properties are evaluation strategy specific.
To select the call-by-name or call-by-value strategy, use the following notation.

```coq
Theorem foo_cbn: quickCheck (withStrategy Cbn prop_foo).
Theorem foo_cbv: quickCheck (withStrategy Cbv prop_foo).
```

The call-by-need strategy needs an additional `Injectable` constraint for the `Share` syntax.
Thus, the following alternative syntax must be used.

```coq
Theorem foo_cbneed: quickCheck (withSharing prop_foo).
```

`withStrategy` leaves the effect stack universally quantified.
However, when using `quickCheckHandle`, the effect stack is fixed and `withStrategy` cannot be used.
In this case, the following notation is needed.

```coq
Theorem foo_cbn:    quickCheckHandle (@prop_foo _ _ cbn)    SomeHandler.
Theorem foo_cbneed: quickCheckHandle (@prop_foo _ _ cbneed) SomeHandler.
Theorem foo_cbv:    quickCheckHandle (@prop_foo _ _ cbv)    SomeHandler.
```

In the next sections we want to demonstrate how to prove converted QuickCheck properties.

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
Let's consider call-by-name evaluation in this example.

```coq
From Base Require Import Test.QuickCheck.
From Generated Require Import Proofs.AppendAssoc.

Theorem append_assoc: quickCheck (withStrategy Cbn prop_append_assoc).
Proof.
  (* FILL IN HERE *)
Qed.
```

Use your favorite editor with Coq integration to carry out the proof.
See [`example/Proofs/AppendAssocProofs.v`][] where we have carried out the proof for `append_assocs` already.
Proving the associativity of `append` requires some auxiliary lemmas.
A simpler [example][`example/Proofs/ListFunctor.hs`] for proving a QuickCheck property can be found in [`example/Proofs/ListFunctorProofs.v`][] where we proved that lists satisfy the functor identity law.

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

## Limitations of Sharing in Proofs

The current implementation of sharing is quite difficult to work with.
While it is usually trivial to prove properties without parameters (since Coq can simply evaluate all expressions and makes sure that the equalities hold), it is very difficult to prove properties even with just a single parameter if the sharing effect is considered.
Additionally, arguments of QuickCheck properties are universally quantified when converted to Coq.
However, the generated Coq code expects all function and constructor applications to be in a flat form (i.e., all arguments are shared variables).
Thus, properties with arguments may behave unexpectedly.
For example, consider the following QuickCheck property.

```haskell
double :: Integer -> Integer
double x = x + x

prop_double :: Integer -> Property
prop_double x = double x === 2 * x
```

The property should be satisfied if we consider call-by-need or call-by-value evaluation.
However, since `double x` and `x + x` are in flat form already, the compiler generates no sharing syntax but correctly assumes the caller of `double` and `prop_double` to apply the function only with shared variables.
The universal quantification of `x` by our QuickCheck extension breaks this assumption, though.
As a workaround, you can introduce sharing syntax yourself.

```haskell
prop_double :: Integer -> Property
prop_double x = (let y = x in double y) === 2 * x
```

Since the framework supports deep sharing, this also works when `x` is a more complex data structure.

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
