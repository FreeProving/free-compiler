# Free Compiler

<!-- Logo -->
<img src="https://raw.githubusercontent.com/FreeProving/free-compiler/master/img/logo.png" width="350" style="max-width: 100%" align="right" alt="Logo" />

<!-- Badges -->
![CI Pipeline](https://github.com/FreeProving/free-compiler/workflows/CI%20Pipeline/badge.svg)

<!-- Short description -->
A compiler for the monadic translation of Haskell programs to Coq that uses the `Free` monad as presented by [Dylus et al.][paper/DylusEtAl2018] to model partiality and other ambient effects.

## Table of Contents

1. [Documentation](#documentation)
2. [Directory Structure](#directory-structure)
3. [Getting Started](#getting-started)
    - [Required Software](#required-software)
    - [Base Library](#base-library)
    - [Installation](#installation)
    - [Running without Installation](#running-without-installation)
4. [Usage](#usage)
    - [Command line options](#command-line-options)
      + [`--output=DIR`, `-o DIR`](#--outputdir--o-dir)
      + [`--import=DIR`, `-i DIR`](#--importdir--i-dir)
      + [`--base-library=DIR`, `-b DIR`](#--base-librarydir--b-dir)
      + [`--no-coq-project`](#--no-coq-project)
      + [`--version`, `-v`](#--version--v)
      + [`--help`, `-h`](#--help--h)
    - [Proving properties](#proving-properties)
    - [Experimental Features](#experimental-features)
      + [Pattern-Matching Compilation](#pattern-matching-compilation)
5. [Get Involved](#get-involved)
6. [License](#license)

## Documentation

This compiler was originally developed as part of a [bachelor's thesis][thesis/Andresen2019].
The compiler has been extended with additional features and its architecture changed compared to the [version presented in the thesis][tag/v0.1.0.0] but the explanation of the monadic translation in the thesis is still up to date.
Read the [changelog][freec/CHANGELOG] for more information on what has changed since the initial release.

The compiler's source code is documented using [Haddock][software/haddock].
The documentation is automatically build by our CI pipeline and published [here][gh-pages/haddock].

Additional documentation can be found in the [`doc/`][doc] directory.

## Directory Structure

This repository is structured as follows.

 - `./`

   The root directory of the Free Compiler is home to important Markdown documents and central configuration files (e.g., Cabal configuration files).

 - `./.github`

   This directory contains GitHub related files such as issue and pull request templates as well as the configuration of the [CI pipeline](#the-ci-pipeline).

 - `./base`

   This directory contains the Coq base library of the compiler.
   The Coq base library is a collection of Coq files that are required by the generated code.
   This includes the definition of the `Free` monad as well as the `Prelude` and `Test.QuickCheck` implementation.

 - `./doc`

   This directory contains Markdown documentation of the compiler.
   The documentation in this directory is mainly intended for users and not so much for developers of the compiler.
   Documentation for more technical aspects such as *module interfaces* and the *intermediate representation* can also be found here.

 - `./example`

   This directory contains examples for Haskell modules that can (or cannot) be compiled with the Free Compiler.
   Examples that don't compile are commented out.
   If multiple examples belong together, they are placed in a common subdirectory.
   There are two `.gitignore`d subdirectories `./example/transformed` and `./example/generated`.

    + `./example/generated` is intended to be used as the `--output` directory of the compiler when testing the compiler.
    + `./example/transformed` is used to dump the output of the [pattern matching compiler][doc/ExperimentalFeatures/PatternMatchingCompilation.md].

   There are also Coq files (`.v` files) for proofs about translated examples.
   In contrast to the Coq files placed by the compiler into `./example/generated`, they are not `.gitignore`d.
   The `./example/_CoqProject` file, configures Coq such that the versioned Coq files can discover the generated Coq code and the base library.

 - `./img`

   This directory contains images that are embedded into the README or other Markdown documents.

 - `./src`

   This directory contains the Haskell source code of the compiler.
   There are three subdirectories.

    + `./src/exe` contains the code for the command line interface.
    + `./src/lib` contains the code for the actual compiler.
    + `./src/test` contains test cases for the modules located in `./src/lib`.
       * By convention modules containing test cases have the same name as the module they are testing but the name `Tests` is appended.
         For example, the module `FreeC.Pass.TypeInferencePassTests` contains test cases for the `FreeC.Pass.TypeInferencePass` module.
       * For tests of modules with a common prefix, there is often a `Tests.hs` file that simply invokes all tests of all modules with that prefix.
         For example, there is no `FreeC.IR` module but a `FreeC.IR.Tests` module that runs all tests for modules starting the the `FreeC.IR` prefix (e.g., `FreeC.IR.ReferenceTests`, `FreeC.IR.SubstTests`, etc.)
       * The `Spec` module serves as an entry point or "main module" for the unit tests.
         It invokes the unit tests in the other test modules.

   Except for the main modules `Main` and `Spec`, the names of all modules that belong to the Free Compiler start with the `FreeC` prefix.
   Modules are organized hierarchically based on their function.
   Common prefixes are listed below.

    + `FreeC.Backend` contains modules that are concerned with the translation from the intermediate representation to a target language.
    + `FreeC.Frontend` contains modules that are concerned with the traslation of an input language to the intermediate representation.
      This includes a front end for the intermediate representation itself.
    + `FreeC.IR` contains modules that define data types and operations for the intermediate representation such as the AST or commonly used operations on the AST.
    + `FreeC.Monad` contains modules that define monads that are used throughout the compiler (e.g., for error reporting, or stateful operations).
    + `FreeC.Monad.Class` contains type classes for monads.
    + `FreeC.Pass` contains one module for each *compiler pass*.
      A compiler pass is a transformation on the intermediate representation and environment.
    + `FreeC.Test` contains modules for writing unit tests.
    + `FreeC.Util` contains modules for utility functions.

   Additionally, if there is a module `FreeC.X`, related modules start with the prefix `FreeC.X`.

 - `./tool`

   This directory contains Bash scripts for common actions that need to be performed during development.
   The scripts are intended to be executed from the root directory of this repository.

   ```bash
   ./tool/run.sh --help
   ```

   However, most scripts will make sure that they change into the correct working directory beforehand.
   For example, the compiler runs in `/path/to/free-compiler` when invoked using the following command.

   ```bash
   /path/to/free-compiler/tool/run.sh ./example/Data/List.hs
   ```

   As a consequence `./example/Data/List.hs` refers to `/path/to/free-compiler/example/Data/List.hs` and not to `$(pwd)/example/Data/List.hs` in the example above.

   If there are other directories named `tool` in this repository, the contained scripts are interned to to be executed from the directory containing the `tool` directory by convention.

## Getting Started

### Required Software

The Free Compiler is written in Haskell and uses Cabal to manage its dependencies.
To build the compiler, the GHC and Cabal are required.
To use the Coq code generated by our compiler, the Coq proof assistant must be installed.
The compiler has been tested with the following software versions on a Debian based operating system.

 - [GHC][software/ghc], version 8.6.5
 - [Cabal][software/cabal], version 2.4.1.0
 - [Coq][software/coq], versions 8.8 through 8.11

### Download

We do not provide pre-build binaries for the compiler.
Instead, the compiler must be build from its source using GHC and Cabal as described below.
First, you have to obtain a copy of the source code.
You can either [download][freec/downloads] an archive containing the source code or clone the Git repository itself using the following command.

```bash
git clone https://github.com/FreeProving/free-compiler.git
```

### Base Library

In order to use the generated Coq code, the Coq files in the base library need to be compiled first.
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

### Installation

First, make sure that the Cabal package lists are up to date by running the following command.

```bash
cabal new-update
```

To build and install the compiler and its dependencies, change into the compiler’s root directory and run the following command.

```bash
./tool/install.sh
```

The command above copies the base library and the compiler’s executable to Cabal’s installation directory and creates a symbolic link to the executable in
`~/.cabal/bin`.
To test whether the installation was successful, make sure that `~/.cabal/bin` is in your `PATH` environment variable and run the following command.

```bash
freec --version
```

#### Upgrading to a Newer Version

If you have installed a previous version of the compiler and want to upgrade, [download][freec/downloads] a newer version of the compiler or run the following command if you are using Git.

```
git pull
```

Now follow the installation steps outlined above, i.e., recompile the Base library, make sure the Cabal package lists are up to date and run the installation script.
Finally, run the following command to confirm that the compiler has successfully been upgraded to a newer version.

```bash
freec --version
```

#### Advanced Installation

The `./tool/install.sh` command performs the following command internally.

```
cabal new-install --overwrite-policy=always freec
```

However, the compiler cannot be installed directly using Cabal, since additional steps are necessary before and after the installation.
However, all command line options given to the installation script are forwarded to Cabal.
So if you want to customize the installation process, you can run the installation script as follows.

```bash
./tool/install.sh [options...]
```

### Running without Installation

First, make sure that the Cabal package lists are up to date by running the following command.

```bash
cabal new-update
```

If you want to run the compiler without installing it on your machine (i.e., for debugging purposes), execute the following command in the root directory of the compiler instead of the `freec` command.

```bash
cabal new-run freec -- [options...] <input-files...>
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

To compile a Haskell module, pass the file name of the module to `freec`.
For example, to compile the examples from the `Data.List` module run the the following command.

```bash
freec ./example/Data/List.hs
```

In order to compile multiple modules which `import` on each other, multiple file names can be passed as an argument.

```bash
freec ./example/Data/List.hs ./example/Data/Function.hs
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
freec -o ./example/generated ./example/Data/*.hs
```

In addition to the `.v` files `.json` files are generated as well.
The JSON files contain the [module interfaces][doc/ModuleInterfaceFileFormat.md] for the translated modules.
The module interface files can be used to import modules that have been translated already without specifying them on the command line.
For example, if `Data.List` and `Data.Functor` have been translated already, the `ListFunctor` example can be compiled on its own since its imports can be served from the module interface files.

```bash
freec -o ./example/generated ./example/ListFunctor.hs
```

#### `--import=DIR`, `-i DIR`

The compiler searches for module interfaces in the output directory (see `--output` option) and the current working directory by default.
If you want to compile modules that import files that have been written to a different output directory, you can use the `--import` command line option to specify additional paths to search for modules interfaces in.
For example, if `Data.List` and `Data.Functor` have been translated already and their output has been written to `./examples/generated`, you can translate `ListFunctor` and print its output to the console as follows.

```bash
freec -i ./example/generated ./example/ListFunctor.hs
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
freec -b ./base ./example/Data/List.hs
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

#### `--version`, `-v`

To check which version of the Free Compiler is currently installed on your system, run the following command.

```bash
freec --version
```

#### `--help`, `-h`

To see a list of all available command line options, use the following command.

```bash
freec --help
```

### Proving properties

The main goal for the translation of Haskell code to Coq is to prove properties of the Haskell program in Coq.
In order to do so, we have to formulate the properties to prove first.
Due to the overhead involved with our translation, stating propositions in Coq directly is very tedious.
Therefore, we provide a mechanism for deriving Coq properties from QuickCheck properties.
This allows us to state the proposition in Haskell instead of Coq.

Consult [`doc/ProvingQuickCheckProperties.md`][doc/ProvingQuickCheckProperties.md] for more details and examples.

### Experimental Features

#### Pattern-Matching Compilation

By default the compiler does support a limited subset of the Haskell programming language only.
There is experimental support to relax some of those restrictions.
Add the `--transform-pattern-matching` command line option to automatically transform the input modules using a [pattern matching compiler library][package/haskell-src-transformations] for [`haskell-src-exts`][package/haskell-src-exts] before they are translated by our compiler.
For example, the `PatternMatching` example can be translated as follows.

```bash
freec --transform-pattern-matching ./example/PatternMatching.hs
```

Consult [`doc/ExperimentalFeatures/PatternMatchingCompilation.md`][doc/ExperimentalFeatures/PatternMatchingCompilation.md] for more details and examples.

## Get Involved

Feature requests, enhancement proposals, bug reports, pull requests and all other contributions are welcome!  
Have a look at our [contributing guidelines][guidelines/CONTRIBUTING] for more information on how to contribute.

## License

The Free Compiler is licensed under The 3-Clause BSD License.  
See the [LICENSE][freec/LICENSE] file for details.

[doc]:
  https://github.com/FreeProving/free-compiler/tree/master/doc
  "Free Compiler Documentation"
[doc/ModuleInterfaceFileFormat.md]:
  https://github.com/FreeProving/free-compiler/blob/master/doc/ModuleInterfaceFileFormat.md
  "Free Compiler Documentation — Module Interface File Format"
[doc/ExperimentalFeatures/PatternMatchingCompilation.md]:
  https://github.com/FreeProving/free-compiler/blob/master/doc/ExperimentalFeatures/PatternMatchingCompilation.md
  "Free Compiler Documentation — Pattern Matching Compilation"
[doc/ProvingQuickCheckProperties.md]:
  https://github.com/FreeProving/free-compiler/blob/master/doc/ProvingQuickCheckProperties.md
  "Free Compiler Documentation — Proving QuickCheck Properties"

[freec/CHANGELOG]:
  https://github.com/FreeProving/free-compiler/blob/master/CHANGELOG.md
  "Free Compiler — Changelog"
[freec/LICENSE]:
  https://github.com/FreeProving/free-compiler/blob/master/LICENSE
  "Free Compiler — The 3-Clause BSD License"
[freec/downloads]:
  https://github.com/FreeProving/free-compiler/releases
  "Free Compiler — Downloads"

[guidelines/CONTRIBUTING]:
  https://github.com/FreeProving/guidelines/blob/master/CONTRIBUTING.md
  "Contributing Guidelines of the FreeProving project"

[gh-pages/haddock]:
  https://freeproving.github.io/free-compiler/docs/master
  "Free Compiler Haddock Documentation"

[package/haskell-src-transformations]:
  https://github.com/FreeProving/haskell-src-transformations
  "haskell-src-transformations"
[package/haskell-src-exts]:
  https://hackage.haskell.org/package/haskell-src-exts
  "haskell-src-exts"

[paper/DylusEtAl2018]:
  https://arxiv.org/abs/1805.08059
  "One Monad to Prove Them All"

[software/haddock]:
  https://www.haskell.org/haddock/
  "Haddock"
[software/ghc]:     
  https://www.haskell.org/ghc/
  "The Glasgow Haskell Compiler"
[software/cabal]:
  https://www.haskell.org/cabal/
  "Common Architecture for Building Applications and Libraries"
[software/coq]:
  https://coq.inria.fr/download
  "The Coq Proof Assistant"

[tag/v0.1.0.0]:
  https://github.com/FreeProving/free-compiler/tree/v0.1.0.0
  "Free Compiler v0.1.0.0"

[thesis/Andresen2019]:
  https://freeproving.github.io/free-compiler/thesis/Andresen2019.pdf
  "Implementation of a Monadic Translation of Haskell Code to Coq"
