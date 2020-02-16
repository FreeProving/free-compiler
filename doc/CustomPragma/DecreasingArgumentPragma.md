# Decreasing Argument Pragma

## Motivation

Our termination checker cannot identify the decreasing argument in all cases
(even if Coq can). For example, the following example does not compile (see
also [`example/Rose.hs`](https://github.com/FreeProving/free-compiler/blob/master/example/Rose.hs)).

```haskell
data Rose a = Rose a [Rose a]

mapRose :: (a -> b) -> Rose a -> Rose b
mapRose f r = case r of
  (Rose x rs) -> Rose (f x) (map (mapRose f) rs)
```

Since `mapRose` is recursive, it should decrease on one of it's arguments,
but the following error message is reported.

```
example/Rose.hs:11:1-12:49: error:
    Could not identify decreasing arguments of mapRose@0
    |
 11 | mapRose f r = case r of
    | ^^^^^^^^^^^^^^^^^^^^^^^...
```

> **Note:** The error message refers to the internal identifier `mapRose@0`
>           which is the function that results from moving the constant
>           argument `f` into a `Section` sentence. We can ignore this
>           implementation detail for the time being.

Obviously, `mapRose` decreases on it's second argument `r`, though.
However, since the partially applied recursive call `mapRose f` is η-expanded
to `\r' -> mapRose f r'` by our compiler and `r'` is not a sub-term of `r`,
our termination checker rejects the definition of `mapRose`.
Coq, on the other hand, is able to verify that `map` calls `mapRose f` only on
sub-terms of `rs` which is a sub-term of `r`.

## Solution

### Named decreasing arguments

As it is infeasible to reimplement Coq's entire termination checker, the user
has to provide information about the decreasing arguments in those cases
manually. For this purpose, we provide a custom pragma with the following
format.

```
{-# HASKELL_TO_COQ <function> DECREASES ON <argument> #-}
```

For instance, the user can tell our compiler that `mapRose` decreases on `r` by
adding the following line to the example above.

```
{-# HASKELL_TO_COQ mapRose DECREASES ON r #-}
```

The function compiles successfully now.

### Unnamed decreasing arguments

When using pattern matching on the left-hand side of the function declaration,
the name of the decreasing argument may not be known.

```haskell
mapRose' :: (a -> b) -> Rose a -> Rose b
mapRose' f (Rose x rs) = Rose (f x) (map (mapRose' f) rs)
```

For this reason, the decreasing argument can also be specified by its index
using a pragma of the following format.

```
{-# HASKELL_TO_COQ <function> DECREASES ON ARGUMENT <index> #-}
```

Where `<index>` is the position of the decreasing argument in the parameter
list. Counting starts at `1`, i.e. the function has index `1` and the tree
has index `2` in the example above.

```
{-# HASKELL_TO_COQ mapRose' DECREASES ON ARGUMENT 2 #-}
```
