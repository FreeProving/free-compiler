# Pattern Matching Compilation

## Motivation

By default, the compiler makes very strong assumptions about pattern matching.
For example, only function declarations with a single rule are supported. Thus pattern matching must be performed explicitly on the right-hand side using `case` expressions.
In consequence, the function `head` cannot be defined as it usually is

```haskell
head :: [a] -> a
head []      = error "head: empty list"
head (x : _) = x
```

but has to be defined like shown below.

```haskell
head :: [a] -> a
head xs = case xs of
  []     -> error "head: empty list"
  x : xs -> x
```

While the first alternative of the `case` expression could be omitted in Haskell, we require pattern matching to be exhaustive, i.e., all constructors of the matched data type must be present.
Furthermore, only variable patterns are allowed in constructor patterns.
Wildcard patterns, as-patterns, deeply nested patterns (e.g., `x : y : xys`) and so on are not allowed.
Guards are not supported either.

## Enabling pattern matching compilation

To relax the restrictions on pattern matching a [pattern matching compiler library][package/haskell-src-transformation] has been integrated into the compiler.
Support for pattern matching compilation can be enabled using the `--transform-pattern-matching` command line flag.
With pattern matching compilation enabled, the compiler does accept the first definition of `head` above.
Further examples can be found in [`example/PatternMatching.hs`][] and can be compiled as shown below.

```bash
freec --transform-pattern-matching ./example/PatternMatching.hs
```

A drawback of enabling pattern matching compilation is that the compiler will not automatically be able to provide source location information in error messages and local variables may be renamed.
For example, if you uncomment one of the unsupported declarations in `example/PatternMatching.hs`, the following error will be reported by the command above.

```
<no location info>: error:
    Local declarations are not supported!
```

In order to inspect what went wrong you can write the transformed modules to a file.
For this purpose, add the `--dump-transformed-modules` flag and specify a directory where the transformed Haskell modules should be placed.

```bash
freec --transform-pattern-matching                     \
      --dump-transformed-modules ./example/transformed \
      ./example/PatternMatching.hs
```

Now, the compiler is also able to provide location information.

```
./example/transformed/PatternMatching.hs:30:5-35:12: error:
    Local declarations are not supported!
    |
 30 |   = let a3 = undefined
    |     ^^^^^^^^^^^^^^^^^^...
```

## Limitations and known bugs

The feature is still marked as experimental since there are known conflicts with other features, the transformed code is not always accepted by our compiler and the pattern-matching transformation does not always terminate.
All of the following examples do not work.

### Recursive functions

If variable patterns and more complex patterns are mixed, the pattern matching compiler substitutes variables on the right-hand side by constructor applications.
For example, the following function

```haskell
flipQ :: ([a], [a]) -> ([a], [a])
flipQ ([],b) = (reverse b,[])
flipQ q      = q
```

is transformed as shown below (variable names have been changed to improve readability).

```haskell
flipQ :: QueueI a -> QueueI a
flipQ q = case q of
  (f, b) -> case f of
    []       -> (reverse b, [])
    (:) x f' -> (x : f', b)
```

This behavior is not a bug but an intentional feature which should prevent a loss of linearity.
However, this feature can be a problem when translating recursive functions.
In the example below both our termination checker and Coq will reject the function because it does not decrease on one of its arguments after the transformation.
The variable `xs` is substituted by `y : ys` in the third rule.

```haskell
intercalate :: a -> [a] -> [a]
intercalate _ []       = []
intercalate _ (x : []) = [x]
intercalate s (x : xs) = x : s : intercalate s xs
```

[`example/PatternMatching.hs`]:
  ../../example/PatternMatching.hs
  "Free Compiler Examples — Pattern Matching"

[package/haskell-src-transformation]:
  https://github.com/FreeProving/haskell-src-transformations
  "haskell-src-transformations on GitHub"
