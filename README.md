# Free Compile

<!-- Logo -->
<img src="https://raw.githubusercontent.com/FreeProving/free-compiler/master/img/logo.png" width="350" style="max-width: 100%" align="right" />

<!-- Badges -->
![Haskell To Coq Compiler CI][badge/ci]

<!-- Short description -->
A compiler for the monadic translation of Haskell programs to Coq that uses the `Free` monad as presented by [Dylus et al.][paper/DylusEtAl2018] to model partiality and other ambient effects.

## Table of Contents

1. [Documentation](#documentation)
2. [Installation](#installation)
    - [Required Software](#required-software)
    - [Base Library](#base-library)
    - [Building](#building)
5. [Running without Installation](#running-without-installation)
6. [Usage](#usage)
    - [Command line options](#command-line-options)
      + [`--output=DIR`, `-o DIR`](#--outputdir--o-dir)
      + [`--import=DIR`, `-i DIR`](#--importdir--i-dir)
      + [`--base-library=DIR`, `-b DIR`](#--base-librarydir--b-dir)
      + [`--no-coq-project`](#--no-coq-project)
7. [Experimental Features](#experimental-features)
    - [Pattern-Matching Compilation](#pattern-matching-compilation)
8. [Testing](#testing)
9. [License](#license)

## Documentation

This compiler was originally developed as part of a [bachelor's thesis][thesis/Andresen2019].
The compiler has been extended with additional features and its architecture changed compared to the [version presented in the thesis][tag/v0.1.0.0] but the explanation of the monadic translation in the thesis is still up to date.

The compiler's source code is documented using [Haddock][software/haddock].
The documentation is automatically build by our CI pipeline and published [here][gh-pages/haddock].

Additional documentation can be found in the [`doc/`][doc] directory.

## Installation

### Required Software

The Haskell to Coq compiler is written in Haskell and uses Cabal to manage its dependencies.
To build the compiler, the GHC and Cabal are required.
To use the Coq code generated by our compiler, the Coq proof assistant must be installed.
The compiler has been tested with the following software versions on a Debian based operating system.

 - [GHC][software/ghc], version 8.6.5
 - [Cabal][software/cabal], version 2.4
 - [Coq][software/coq], version 8.8.2

### Base Library

In order to use the base library, the Coq files in the base library need to be compiled first.
Make sure to compile the base library **before installing** the compiler.
We provide a shell script for the compilation of Coq files.
To compile the base library with that shell script, run the following command in the root directory of the compiler.

```bash
./tool/compile-coq.sh base
```

> **Note:** If you add or remove files from the `base` library (or any other directory that contains Coq code that you wish to compile using the script above), the automatically generated Makefile needs to be updated.
> For this purpose the script provides the command line option `--recompile`.
>
> ```bash
> ./tool/compile-coq.sh --recompile base
> ```

### Building

First, make sure that the Cabal package lists are up to date  by running the following command.

```bash
cabal new-update
```

To build and install the compiler and its dependencies, change into the compiler’s root directory and run the following command.

```bash
cabal new-install haskell-to-coq-compiler
```

The command above copies the base library and the compiler’s executable to Cabal’s installation directory and creates a symbolic link to the executable in
`~/.cabal/bin`.
To test whether the installation was successful, make sure that `~/.cabal/bin` is in your `PATH` environment variable and run the following command.

```bash
haskell-to-coq-compiler --help
```

## Running without Installation

If you want to run the compiler without installing it on your machine (i.e., for debugging purposes), execute the following command in the root directory of the compiler instead of the `haskell-to-coq-compiler` command.

```bash
cabal new-run haskell-to-coq-compiler -- [options...] <input-files...>
```

The two dashes are needed to separate the arguments to pass to the compiler from Cabal’s arguments.
Alternatively, you can use the `./tool/run.sh` bash script.

```bash
./tool/run.sh [options...] <input-files...>
```

Besides invoking Cabal and forwarding its command line arguments to the compiler, the script also sets the `-Wwarn` flag of the GHC automatically.
This overwrites the `-Werror` flag of the GHC that is set in addition to the `-Wall` flag by default.
The default configuration causes compilation to fail when there are unhandled warnings in the source code.
As a result, the CI pipeline rejects commits that introduce such warnings.
While it is important that no warnings are reported in a production setting, fatal warnings can be disrupting when debugging.
Thus, we recommend using the `./tool/run.sh` script during development and running `./tool/full-test.sh` (which uses the default settings) once before pushing your local changes.

## Usage

To compile a Haskell module, pass the file name of the module to `haskell-to-coq-compiler`.
For example, to compile the examples from the `Data.List` module run the the following command.

```bash
haskell-to-coq-compiler ./example/Data/List.hs
```

In order to compile multiple modules which `import` on each other, multiple file names can be passed as an argument.

```bash
haskell-to-coq-compiler ./example/Data/List.hs ./example/Data/Function.hs
```

Both commands above print the generated Coq code directly to the console.
See the `--output` option below for how to write the generated Coq code into files instead.

### Command line options

#### `--output=DIR`, `-o DIR`

By default generated Coq code is printed to the console.
To write to a file instead, specify an output directory using the `--output` option.
A file `X/Y/Z.v` is placed into the output directory for every module `X.Y.Z` that is compiled.
For example, the following command creates the files `example/generated/Data/List.v` and `example/generated/Data/Function.v`

```bash
haskell-to-coq-compiler -o ./example/generated ./example/Data/*.hs
```

In addition to the `.v` files `.json` files are generated as well.
The JSON files contain the [module interfaces][doc/ModuleInterfaceFileFormat.md] for the translated modules.
The module interface files can be used to import modules that have been translated already without specifying them on the command line.
For example, if `Data.List` and `Data.Functor` have been translated already, the `ListFunctor` example can be compiled on its own since its imports can be served from the module interface files.

```bash
haskell-to-coq-compiler -o ./example/generated ./example/ListFunctor.hs
```

#### `--import=DIR`, `-i DIR`

The compiler searches for module interfaces in the output directory (see `--output` option) and the current working directory by default.
If you want to compile modules that import files that have been written to a different output directory, you can use the `--import` command line option to specify additional paths to search for modules interfaces in.
For example, if `Data.List` and `Data.Functor` have been translated already and their output has been written to `./examples/generated`, you can translate `ListFunctor` and print its output to the console as follows.

```bash
haskell-to-coq-compiler -i ./example/generated ./example/ListFunctor.hs
```

To add multiple import paths just add one `--import` option for each path.
There can be arbitrarily many import paths and the `--import` and `--output` options can be mixed.

```bash
./tool/run.sh -o <dir0> -i <dir1> -i <dir2> … <input-files...>
```

In the example above, the compiler would search for a module interface file first in the current working directory and then in the directories in the order they have been specified on the command line (i.e., first `.`, then `<dir0>`, then `<dir1>`, then `<dir2>` and so on).

#### `--base-library=DIR`, `-b DIR`

Predefined data types and operations are not build directly into the compiler but part of the *base library* that accompanies the compiler.
The compiler uses the same mechanism that is used to load module dependencies to load modules from the base library, i.e., module interface files.
In contrast to automatically generated module interface files, the base library does not use the JSON file format but TOML since the module interfaces of the base library are maintained manually and TOML is a more user friendly format.
The module interface file format is documented in [`doc/ModuleInterfaceFileFormat.md`][doc/ModuleInterfaceFileFormat.md].

In order for the compiler to locate the `Prelude.toml` module interface file, the location of the base library must be known.
If the compiler is installed as described above or executed using `cabal`, it will usually be able to locate the base library automatically.
Otherwise, it may be necessary to tell the compiler where the base library can be found using the `--base-library` option.

```bash
haskell-to-coq-compiler -b ./base ./example/Data/List.hs
```

#### `--no-coq-project`

When an output directory has been specified using the `--output` option and the output directory does not contain a `_CoqProject` file, it is created automatically.
The `_CoqProject` file tells Coq where to find the compiler’s base library and assigns the logical name `Generated` to the directory that contains the generated Coq code.
The file has the following format where `<base-library>` is the path to the base library (see `--base-library` command line option).

```
-R <base-library> Base
-R . Generated
```

The logical names `Base` and `Generated` are used in the generated import sentences.
For example, a generated file could contain the following lines.

```coq
From Base Require Import Prelude.
From Generated Require Export Data.List.
```

You can safely edit the `_CoqProject` file or supply your own configuration as long as Coq is still able to locate the `.v` files under their logical prefixes.
The compiler will not overwrite your changes since the `_CoqProject` file is only written to if it does not exist.

If you don't want the `_CoqProject` file to be generated at all, you can add the `--no-coq-project` flag.
However, note that you may not be able to compile the generated Coq code if the `_CoqProject` file is missing.

## Experimental Features

### Pattern-Matching Compilation

By default the compiler does support a limited subset of the Haskell programming language only.
There is experimental support to relax some of those restrictions.
Add the `--transform-pattern-matching` command line option to enable the translation of function declarations with multiple rules and guards.
We are using a [pattern matching compiler][package/haskell-src-transformations] library for [`haskell-src-exts`][package/haskell-src-exts] to transform modules such that all pattern matching is performed explicitly using `case` expressions.
Note that if pattern matching compilation is enabled, error messages will not contain any location information and local variables may be renamed.
It is also known that the pattern matching compiler is currently integrated in such a way, that it may not work in conjunction with module imports.

For example, the `PatternMatching` example can be translated as follows.

```bash
haskell-to-coq-compiler --transform-pattern-matching ./example/PatternMatching.hs
```

If we uncomment the unsupported declarations at the end of the file, the following error will be reported.

```
<no location info>: error:
    Local declarations are not supported!
```

Since the original module does not contain any local declarations (i.e., `let` expressions or `where` clauses), the pattern matching compiler must have introduced such declarations.
We can inspect the code that has been generated using the `--dump-transformed-modules` command line option and specifying a directory where the transformed Haskell modules should be placed.

```bash
haskell-to-coq-compiler --transform-pattern-matching                      \
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

## Testing

To test whether the compiler is working correctly, you can run the included unit tests using via one of the following Cabal commands.

```bash
cabal new-test
cabal new-run unit-tests -- [options...]
```

Similar to how we discourage using `cabal new-run` during development to run the compiler, we recommend using our `./tool/test.sh` script to execute unit tests instead.

```bash
./tool/test.sh [options...]
```

 - Firstly it allows command line options such as `--match` to be passed to the test suite more easily.
   The `--match` command line option can be used to run specific unit tests instead of the full test suite.
   For more details on supported command line options use the following command

   ```bash
   ./tool/test.sh --help
   ```

 - Secondly the script configures HSpec (the library that we are using for testing) to create a failure report.
   The failure report allows you to add the `--rerun` command line option to run test that failed in the previous run only.

   ```bash
   ./tool/test.sh --rerun
   ```

   This allows you to focus on the failed test cases during debugging.
   Once all tests are fixed, all tests are executed again.

 - Finally the script overwrites GHC's `-Werror` flag that is set by default for our compiler with `-Wwarn`.
   Doing so improves the development workflow.
   However, in production, the compiler must compile without any warnings.
   Thus, the CI pipeline will reject any commits that contain unhandled warnings.
   To make sure that your local changes do not cause warnings to be reported,
   run the `full-test.sh` script before pushing.

   ```bash
   ./tool/full-test.sh
   ```

   The script simulates the CI pipeline locally but runs much faster since there is no overhead for creating test environments, uploading and downloading artifacts, initializing the cache etc.
   If the script succeeds, it is not guaranteed that the CI pipeline will defiantly pass, but it should catch the most common mistakes.

## License

The Haskell to Coq Compiler is licensed under The 3-Clause BSD License.  
See the LICENSE file for details.

[badge/ci]: https://github.com/FreeProving/free-compiler/workflows/Haskell%20To%20Coq%20Compiler%20CI/badge.svg

[doc]: https://github.com/FreeProving/free-compiler/tree/master/doc
[doc/ModuleInterfaceFileFormat.md]: https://github.com/FreeProving/free-compiler/blob/master/doc/ModuleInterfaceFileFormat.md

[gh-pages/haddock]: https://freeproving.github.io/free-compiler/docs/master

[package/haskell-src-transformations]: https://github.com/FreeProving/haskell-src-transformations
[package/haskell-src-exts]: https://hackage.haskell.org/package/haskell-src-exts

[paper/DylusEtAl2018]: https://arxiv.org/abs/1805.08059

[software/haddock]: https://www.haskell.org/haddock/
[software/ghc]: https://www.haskell.org/ghc/
[software/cabal]: https://www.haskell.org/cabal/
[software/coq]: https://coq.inria.fr/download

[tag/v0.1.0.0]: https://github.com/FreeProving/free-compiler/tree/v0.1.0.0

[thesis/Andresen2019]: https://freeproving.github.io/free-compiler/thesis/Andresen2019.pdf
