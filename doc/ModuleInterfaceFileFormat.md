# Module Interface File Format

In order to tell the compiler which functions and data types are defined in a module, every module has a configuration file that contains all information about the module's interface.
The module interface file for the `Prelude` module can be found in `/base/coq/Prelude.toml`.
Since the module interface for predefined functions and data types needs to be maintained manually, we are using [TOML][] as a configuration file format.
If a Haskell module is translated by the compiler, a module interface file is saved alongside the `.v` file.
Since generated module interfaces are not intended to be read by humans, they use the JSON file format instead.
The contents of the TOML interface files is described below.
The JSON files contain the same information.

## File contents

The TOML document is expected to contain four arrays of tables: `types`, `type-synonyms`, `constructors` and `functions`.
Each table in these arrays defines a data type, type synonym, constructor or function respectively.
The expected contents of each table are described below.
In addition, the module interface file contains meta information in the top-level table.

### Top-Level

The top-level table must contain the following key/value pairs:

 - `version` (`Integer`) the version of the configuration file format.
   The current version is `1`. If there is a breaking change in the future, the module interface file format version is updated.
   The parser accepts module interface files that use the most recent version only.
 - `module-name` (`String`) the name of the module that is described by the module interface file.
 - `library-name` (`String`) the name of the Coq library that contains the module.
 - `exported-types` (`Array` of `String`) the qualified Haskell names (`haskell-name`) of the type-level entries exported by the module.
    All other entries in the `types` and `type-synonyms` tables are "hidden" (i.e., cannot be used by an importing module directly).
 - `exported-values` (`Array` of `String`) the qualified Haskell names (`haskell-name`) of the value-level entries exported by the module.
    All other entries in the `constructors` and `functions` tables are "hidden" (i.e., cannot be used by an importing module directly).

For example, the interface file of the following Haskell Module

```haskell
module Test where

data Foo = Bar | Baz

foo :: Foo
foo = -- ...
```

has the following top-level entries.

```toml
module-name     = 'Test'
exported-types  = ['Test.Foo']
exported-values = ['Test.Bar', 'Test.Baz', 'Test.foo']
```

### Data types

The tables in the `types` array must contain the following key/value pairs:

 - `haskell-name` (`String`) the qualified Haskell name of the type constructor in the module it has been defined in.
 - `coq-name` (`String`) the identifier of the corresponding Coq type constructor.
 - `arity` (`Integer`) the number of type arguments expected by the type constructor.

For example, the following entry defines the `Maybe` data type.

```toml
[[types]]
  haskell-name = 'Prelude.Maybe'
  coq-name     = 'Maybe'
  arity        = 1
```

### Type synonyms

The tables in the `type-synonyms` array must contain the following key/value pairs:

 - `haskell-name` (`String`) the qualified Haskell name of the type synonym in the module it has been defined in.
 - `coq-name` (`String`) the identifier of the corresponding Coq definition.
 - `arity` (`Integer`) the number of type arguments expected by the type synonym.
 - `haskell-type` (`String`) the Haskell type that is abbreviated by the type synonym.
 - `type-arguments` (`Array` of `String`) the Haskell identifiers of the type arguments.
    Must be of length `arity`.

For example, the following entry defines the `ReadS` type synonym.

```toml
[[type-synonyms]]
  haskell-name   = 'Prelude.ReadS'
  coq-name       = 'ReadS'
  arity          = 1
  haskell-type   = 'String -> [(a, String)]'
  type-arguments = ['a']
```

### Constructors

The tables in the `constructors` array must contain the following key/value pairs:

 - `haskell-type` (`String`) the Haskell type of the data constructor.
 - `haskell-name` (`String`) the qualified Haskell name of the data constructor in the module it has been defined in.
 - `coq-name` (`String`) the identifier of the corresponding Coq data constructor.
 - `coq-smart-name` (`String`) the identifier of the corresponding Coq smart constructor.
 - `arity` (`Integer`) the number of arguments expected by the data constructor.

For example, the following entries define the constructors `Just` and `Nothing` of the `Maybe` data type.

```toml
[[constructors]]
  haskell-type   = 'a -> Prelude.Maybe a'
  haskell-name   = 'Prelude.Just'
  coq-name       = 'just'
  coq-smart-name = 'Just'
  arity          = 1

[[constructors]]
  haskell-type   = 'Prelude.Maybe a'
  haskell-name   = 'Prelude.Nothing'
  coq-name       = 'nothing'
  coq-smart-name = 'Nothing'
  arity          = 0
```

### Functions

The tables in the `functions` array must contain the following key/value pairs:

 - `haskell-type` (`String`) the Haskell type of the function.
 - `haskell-name` (`String`) the qualified Haskell name of the function in the module it has been defined in.
 - `coq-name` (`String`) the identifier of the corresponding Coq function.
 - `arity` (`Integer`) the number of arguments expected by the function.
 - `partial` (`Boolean`) whether the function is partial (i.e., requires an instance of the `Partial` type class).
 - `needs-free-args` (`Boolean`) whether the arguments of the `Free` monad need to be passed to the function.

For example, the following entry defines the total function `(++)` ("append") and the partial function `head`.

```toml
[[function]]
  haskell-type    = '[a] -> [a] -> [a]'
  haskell-name    = 'Prelude.(++)'
  coq-name        = 'append'
  arity           = 2
  partial         = false
  needs-free-args = true

[[function]]
  haskell-type    = '[a] -> a'
  haskell-name    = 'Prelude.head'
  coq-name        = 'head'
  arity           = 1
  partial         = true
  needs-free-args = true
```

[TOML]:
  https://github.com/toml-lang/toml
  "Tom's Obvious, Minimal Language"
