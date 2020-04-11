# Contributing

First off, thanks for considering to contribute to the FreeProving project!
Whether it is a feature request, enhancement proposal, bug report or pull request, all kinds of contributions are welcome and greatly appreciated.

We want to make the process of contributing to this project as easy and transparent as possible.
Thus, please take the time to read this document carefully if this is your first time contributing.
Note that the following is a set of guidelines and recommendations.
They are not rules and they are certainly not complete.
If you have questions or want to propose changes to this document, feel free to open an [issue][freec/issues] or [pull request][freec/pull-requests].

## Table of Contents

 1. [How Can I Contribute?](#how-can-i-contribute)
    - [Reporting Bugs](#reporting-bugs)
    - [Submitting Pull Requests](#submitting-pull-requests)
 2. [Directory Structure](#directory-structure)
 3. [Testing](#testing)
    - [Running Unit Tests](#running-unit-tests)
    - [Writing Unit Tests](#writing-unit-tests)
    - [The CI Pipeline](#the-ci-pipeline)
    - [Running The Pipeline Locally](#running-the-pipeline-locally)
 4. [Styleguides](#styleguides)
    - [Languages without Styleguide](#languages-without-styleguide)
    - [General Guidelines](#general-guidelines)
    - [Git Commit Messages](#git-commit-messages)
    - [Haskell Styleguide](#haskell-styleguide)
    - [Haddock Styleguide](#haddock-styleguide)
    - [Markdown Styleguide](#markdown-styleguide)
 5. [Legal Information](#leagal-information)
    - [Privacy](#privacy)
    - [License](#license)

## How Can I Contribute?

### Reporting Bugs

TODO

### Submitting Pull Requests

TODO

## Additional Software

In addition to the required software listed in the [README][freec/README], we recommend using the following additional software during development.
Both of these tools are used to make sure that we are using a consistent code style throughout the project and are described in more detail in the [Haskell Styleguide](#haskell-styleguide) below.

 - [Brittany][software/brittany], 0.12.1.1
 - [HLint][software/hlint], version 2.2.11

The versions mentioned above are the versions used by our [CI pipeline](#the-ci-pipeline).
Both tools must be installed in order to [run the CI pipeline locally](#running-the-pipeline-locally).
If you are not planning to make changes that involve the CI pipeline (i.e., modify Markdown documentation only), you do not have to install these tools.

## Directory Structure

In this section, we would like to give you a quick overview over what files are part of this repository, where they can be found and what's their purpose.

 - `./`

   The root directory of this repository is home to important Markdown documents and central configuration files (e.g., Cabal configuration files).
   Avoid adding new files directly to the root directory if possible.
   Instead, select an appropriate subdirectory from the list below or create a new subdirectory if the file really does not fit any of the existing categories.

 - `./.github`

   This directory contains GitHub related files such as issue and pull request templates as well as the configuration of the [CI pipeline](#the-ci-pipeline).
   Usually only project maintainers have to edit files in this directory.
   You can safely ignore it.

 - `./base`

   This directory contains the Coq base library of the compiler.
   The Coq base library is a collection of Coq files that are required by the generated code.
   This includes the definition of the `Free` monad as well as the `Prelude` and `Test.QuickCheck` implementation.

 - `./doc`

   This directory contains Markdown documentation of the compiler.
   The documentation in this directory is mainly intended for users and not so much for developers of the compiler.
   Documentation for more technical aspects such as *module interfaces* and the *intermediate representation* also belongs here.
   Nevertheless, avoid providing implementation details and don't require knowledge about internal workings of the compiler in these documents.

 - `./example`

   This directory contains examples for Haskell modules that can (or cannot) be compiled with the Free Compiler.
   Examples that don't compile should be commented out.
   If multiple examples belong together, they should be placed in a common subdirectory.
   There are two `.gitignore`d subdirectories `./example/transformed` and `./example/generated`.

    + `./example/generated` is intended to be used as the `--output` directory of the compiler when testing the compiler.
    + `./example/transformed` is used to dump the output of the [pattern matching compiler][doc/ExperimentalFeatures/PatternMatchingCompilation.md].

   There are also Coq files (`.v` files) for proofs about translated examples.
   In contrast to the Coq files placed by the compiler into `./example/generated`, they are not `.gitignore`d.
   The `./example/_CoqProject` file, configures Coq such that the versioned Coq files can discover the generated Coq code and the base library.

 - `./img`

   This directory contains images that are embedded into the README or other Markdown documents.
   Usually you should avoid adding large binary files to Git repositories.
   Frequent changes to files in this directory should be avoided and new files should only be added if necessary.

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

   Except for the main modules `Main` and `Spec`, the names of all modules that belong to the Free Compiler should start with the `FreeC` prefix.
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

   Additionally, if there is a module `FreeC.X`, the prefix `FreeC.X` contains related modules.

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

## Testing

Automated tests occupy a central role in our development and review process.
In this section we provide a quick overview over the general testing infrastructure, explain how you can run tests and give recommendations on how to write your own unit tests.

### Running Unit Tests

If you make changes to the code, you should run the unit tests to make sure that everything still works.
One option is to run the unit tests directly using Cabal via the following command.

```bash
cabal new-run freec-unit-tests -- [options...]
```

However, we recommend using the `./tool/test.sh` script for running unit tests during development instead which passes some handy default arguments to Cabal and the test suite.

```bash
./tool/test.sh [options...]
```

The most important difference is that the script overwrites GHC's `-Werror` flag with `-Wwarn`.
This allows the unit tests to run even if GHC reports warnings.
Doing so improves the development workflow.
Still remember to fix the warnings before creating a pull request since the [Ci pipeline](#the-ci-pipeline) fails otherwise.

Furthermore, the script configures HSpec (the library that we are using for testing) to create a failure report.
The failure report allows you to add the `--rerun` command line option to run test that failed in the previous run only.

```bash
./tool/test.sh --rerun
```

This allows you to focus on the failed test cases during debugging.
Once all tests are fixed, all tests are executed again.

More command line options are available.
Use the `--help` option for more information.

```bash
./tool/test.sh --help
```

### Writing Unit Tests

In addition to testing whether your changes do not break existing unit tests, we recommend writing your own test cases for every feature added.

TODO

### The CI Pipeline

Whenever a pull request is opened, reopened or if you push to the branch that is tracked by an open pull request, a run of the continuous integration pipeline (CI pipeline) is triggered.
We are using [GitHub Actions][GitHub/Actions] for the CI pipeline.
You can find the corresponding workflow configuration file in `.github/workflows/ci-pipeline.yml`.

The CI pipeline checks whether

 - the code has been formatted with [Brittany][software/brittany]
 - [HLint][software/hlint] prints no suggestion that is not explicitly ignored in `.hlint.yaml`
 - the `freec` executable and the unit tests compile without warnings,
 - all unit tests pass,
 - all examples in the `./example` directory compile using `freec --transform-pattern-matching` without errors,
 - Coq compiles the generated code as well as the example proofs without errors,
 - Haddock generates the documentation without errors and there
   are no out of scope references in the documentation.

If any check fails, the entire pipeline fails.
You will receive an email notification in this case.
A pull request cannot be merged unless the pipeline passed.

If a pull request does not modify the source code, examples, Cabal configuration or CI pipeline workflow file, the CI pipeline is not triggered.
This is for example the case when only Markdown documents have been edited.
The pull request can be merged as soon as all other requirements are met in this case.

### Running The Pipeline Locally

Since a full run of the CI pipeline can take a while, you should make sure that all checks that are performed by the CI pipeline pass on your machine before you push your changes.
Luckily, you do not have to perform these checks manually, we provide a Bash script for that purpose.
Run the following command to simulate a run of the pipeline locally.

```bash
./tool/full-test.sh
```

The script usually runs much faster since there is no overhead for creating test environments, uploading and downloading artifacts, initializing caches etc.
If the script succeeds, it is not guaranteed that the CI pipeline will definitely pass, but it should catch the most common mistakes.

## Styleguides

In order to maintain a consistent code style, we try to adhere to the following guidelines for formatting, structuring and organizing our code in various languages.

If you are unsure how a piece of code should be formatted and the corresponding styleguide is not helping either, have a glance at existing source files to see how they handle similar situations, [open an issue][freec/issues] to start a discussion on the topic or [create a pull request][freec/pull-requests] to extend or clarify the styleguide in this document.
Furthermore, there is probably a lot of code in this repository that violates the styleguides.
Don't hesitate to format the code accordingly and submit a [pull request][freec/pull-requests].

### Languages without Styleguide

We are using many different languages in this project.
There is Haskell code, Coq code, Bash scripts, Cabal, YAML and TOML configuration files, Markdown documents and many more to come in the future.
Unfortunately, there are not yet styleguides for all of those languages and for some there will probably never be one.
As always, you are of course encouraged to extend this document.
However, a compromise has to be found between the comprehensibility and completeness of this document.
At the moment, we do not see a need to add a style guide for script or configuration languages for example.
They make up only a very small fraction of the source code in this repository and are not expected to be edited frequently by many different contributors.

If you have to work with a language for which no styleguide exist or you don't find any reference files for in this repository, use your best judgment and keep the following two main goals in mind.

 1. **Consistency**

    Format your code based on how other files of the same format are formatted.
    Most importantly, don't mix completely different styles in the same file, though.

 2. **Readability**

    Format your code such that it can be parsed and understood by a human reader easily.
    Readability is more important than consistency.
    Don't format your code such that it is absolutely unreadable just to conserve a consistent style with the way other code was formatted.
    However, that does not mean that you can use the argument of readability to sacrifice consistency whenever you feel like it.
    It is a trade off after all.

Also the general rules discussed in the next subsection might help in such a situation.

### General Guidelines

The following general guidelines apply in every language if not noted otherwise in the styleguide for the language in question.

 - **Use spaces, not tabs**

   Use spaces to indent your code instead of tabs.
   The display width of a tab character varies from editor to editor and from configuration to configuration.
   As a result, you can never be sure that everybody sees all files the same way when tabs are used in a collaborative project.
   When using spaces, it is guaranteed that the code lines up as the original author intended everywhere.

   If not specified otherwise, we are using two spaces for indentation.
   If you prefer using the tab key of your keyboard, consider configuring your editor accordingly.

 - **Use Unix line endings**

   On Unix-like operating systems a line feed character (LF) is used to encode the end of a line while Microsoft Windows uses a carriage return followed by a line feed (CRLF) for line endings.
   When code is committed to this repository, it should use Unix line endings.
   If you are on a Windows machine, you can configure configure Git to automatically convert LF to CRLF when you check out code and back when you commit using the [following command][Git/Config/autocrlf].

   ```bash
   git config --global core.autocrlf true
   ```

 - **Wrap lines after 80 characters**

   Long lines of text and source code are difficult to scan for the human eye and thus should be avoided.
   In case of [Markdown](#markdown-styleguide) documents, we do not have to deal with this problem since text can usually be soft wrapped without changing its meaning.
   In case of structured text such as source code, automatic line wrapping is not a good strategy for dealing with long lines.
   Thus, long lines should be hard wrapped such that structure, indentation and alignment are preserved with respect to syntax and semantics of the source code.
   The goal is to enhance readability, avoid horizontal scrolling and eliminate the need for resizing editor windows.

   One exception to this rule are links.
   If an URL does not fit into the current line, consider placing it on a line by itself but never insert a line break into the URL.
   It should be easy for the URL to be copied to the clipboard or automatically recognized by software.

   Line ending characters do not count towards the line length limit.

 - **Comment your code**

   Good comments describe *what* your code does and *why* it does so.
   Avoid comments that simply reiterate *how* your code works.
   If the reader is interested in implementation details, they can refer to the code itself.
   However, the code will not teach them anything about your though process, theoretical understanding or hidden assumptions.

   + Every source file should start with a comment that states the purpose and contents of the file and how to use it.
   + At the very least every function and data type that is part of your code's public interface should be documented.
     However, also internal functions and data types should to be documented.
   + Inside functions you do not have to comment individual lines of code.
     It is usually best practice to split the code into small chunks with a well defined purpose and summarize what the code does and why it is necessary.

### Git Commit Messages

When writing Git Commit Messages, try to follow the following recommendations on [How to Write a Git Commit Message][GitCommit].

 - **Separate subject from body with a blank line**

   The commit message should start with a subject line that is separated from the rest of the commit message by a blank line.
   The subject line briefly summaries the changes in preferably 50 to at most 72 characters or less.

   ```
   Summarize changes using Markdown for formatting

   Give a more detailed explanation of the changes made by this commit in the
   body of the commit message. This explanation can span multiple lines or even
   paragraphs. This text is formatted using Markdown as well.
   ```

 - **Capitalize the subject line**

   The first word of the subject line should be capitalized (e.g. `Add feature XYZ` instead of `add feature XYZ`).

 - **Do not end the subject line with a period**

   Even though subject lines should form a sentence, trailing punctuation does not add any information and costs precious space.

 - **Use the present tense and imperative mood in the subject line**

   You should be able to read a Git commit message as "If applied, this commit will [subject]".

    + **DON'T:** `Added feature XYZ` or `Fixes #123`

    + **DO** `Add feature XYZ` or `Fix #123`

 - **Wrap lines at 72 characters**

    + One exception to this rule are links.
     Never wrap long links.
     Instead consider placing them on a line by themselves.
     This way, the links can be copied easily and can be recognized by terminals as clickable if such a feature is supported.

    + The subject line should be kept even shorter at below 50 characters if possible.
      You can exceed this limit if needed.
      However, the 72 characters should be considered a hard limit for the subject line.

 - **Reference issues and pull requests**

   If you are currently working on an issue or pull request, reference the number of the issue or pull request directly after the subject line.

    + `Add feature XYZ #42`
    + `Fix #42`

   If your change is related to multiple issues or pull requests, mention all of them.
   References to issues and pull requests don't count towards the line length limit.

    + `Add feature XYZ #42 #95`
    + `Fix #42 #95`

 - **Use Markdown to format your commit messages**

   If you want to format your commit messages use Markdown (for example, use [code spans][Markdown/code-spans] to format identifiers).
   The [Markdown Styleguide](#markdown-styleguide) applies but the rules above take precedence.
   For example, lines in Git commit messages are wrapped at 72 characters while they are not wrapped in Markdown documents.
   Also: just paste links into the commit message's body.
   There is no need for link reference definitions or links with text in commit messages.

- **Explain *what* and *why* something has been done and not *how***

- **The language of Git commit messages is English**

### Haskell Styleguide

TODO

We are using the following two tools to enforce the Haskell styleguide.

#### Brittany

[Brittany][software/brittany] is a code formatter for Haskell.
It can be installed via Cabal as follows.

```haskell
cabal new-install brittant
```

The CI pipeline runs `brittany` on all Haskell source files in the `src` and `example` directories and compares its output with the committed files.
If there are Haskell source files that have not been formatted using `brittany`, the CI pipeline fails.
The same check is performed by the `./tool/check-formatting.sh` and `./tool/full-test.sh` scripts.

There is Brittany support for various editors (see also [Editor Integration][software/brittany#editor-integration]).
If your editor is not supported, you can use the following shell script that we provide.

```haskell
./tool/format-code.sh [files...]
```

If no files are specified, all Haskell source files in the `src` and `example` directory are formatted by default.
Note that the script overwrites the formatted files.
Thus, you should create a backup beforehand by `git add`ing your changes, for example.

Of course Brittany is not perfect.
Among others, data type declarations are not formatted at the moment.
So don't rely entirely on the output of our automatic tests and manually check your code nonetheless according to the rules outlined above.

#### HLint

[HLint][software/hlint] is a tool that gives suggestions on how to improve Haskell source code.
It can be installed via Cabal as follows.

```haskell
cabal new-install hlint
```

The CI pipeline runs `hlint` on all Haskell source files in the `src` directory.
If HLint has suggestions for how the code can be improved, the CI pipeline fails.
The same check is performed by the `./tool/full-test.sh` script.

There are HLint plugnis for many editors.
If there is no such plugin for your editor, you can run the following command instead.

```haskell
hlint src
```

Remember, that HLint only makes suggestions and you don't have to follow these suggestions.
However, since the CI pipeline fails if HLint finds possible improvements, suggestions have to be ignored explicitly.
Edit the `.hlint.yaml` file for this purpose and leave a comment why you had to ignore that suggestion.
Try to be as specific as possible when ignoring suggestions.

### Haddock Styleguide

TODO

### Markdown Styleguide

While Haddock is used to document the Haskell source code, we are using [Markdown][Markdown] to write the remaining documentation.
Markdown is also used in commit messages and comments of all other languages (e.g., in Bash scripts) if not specified otherwise.
When writing markdown documents adhere to the following style considerations.

 - **Write one sentence per line**

   Unlike in source code, long lines of Markdown should not be wrapped.
   By writing one sentence per line, versioning the Markdown files gets easier.
   If lines are wrapped, whole paragraphs sometimes need to be relayouted even when just a single word was changed which obfuscates diffs unnecessarily.

   We still recommend enabling the soft wrapping feature (preferably at a line length of 80 characters) of your editor to avoid horizontal scrolling.

 - **Use ATX headings**

   There are two ways of writing headings in Markdown: ATX and Setext headings.

   ```markdown
   # This is an ATX Heading

   This is a Setext Heading
   ========================
   ```

   We prefer the usage of ATX headings.
   Their key advantage over Setext headings is that there are up to six levels of nesting as opposed to two.

    + Your document should start with a level one ATX heading.
      This heading contains the title of the document.
      There should be only one of those headings in the entire document.
    + Start each section of your document with its own level two ATX heading and add as many subsections at level three or deeper as necessary.
    + Avoid having a single subsection for a section (except if you have plans to add further items down the line).
    + Avoid two consecutive headings.
      Consider writing a short introduction to the section in this case.
    + Capitalize the first word of the heading (e.g. "The CI Pipeline" instead of "the CI Pipeline").
    + Capitalize all other words except for articles, conjunctions and prepositions (e.g. "How Can I Contribute?" instead of "How can I contribute?" but "Haskell to Coq" instead of "Haskell To Coq").

   ```markdown
   # Document Title
   ## Section 1
   ## Section 2
   ### Subsection 2.1
   ### Subsection 2.2
   ## Section 3
   ### Subsection 3.1
   ### Subsection 3.2
   #### Subsection 3.2.1
   #### Subsection 3.2.2
   ```

 - **Add a table of contents to long document**

   Markdown documents with many sections and subsections can get very difficult to navigate quickly.
   If you cannot break up the document into multiple files, consider adding a table of contents.

    + The table of contents should be the first section of a document.
    + Write a short description or introduction before the table of contents.
    + Don't list the table of contents in the table itself.
    + Avoid move than three levels of nesting.
      Two levels are preferred.
    + Every item of the table should be a link to the corresponding section or subsection.
      The link text should be the same as in the heading of the section.
      GitHub automatically generates an anchor for every heading in the document.
      Just use that anchor in the link, don't use the full address and don't use [link reference definitions][Markdown/link-reference-definition] for internal references.

   ```markdown
   # Document Title

   <short introduction>

   ## Table of Contents

   1. [Section 1](#section-1)
   2. [Section 2](#section-2)
      - [Section 2.1](#section-2-1)
      - [Section 2.2](#section-2-2)
   3. [Section 3](#section-3)
      - [Section 3.1](#section-3-1)
      - [Section 3.2](#section-3-2)
        + [Section 3.2.1](#section-3-2-1)
        + [Section 3.2.2](#section-3-2-2)
   ```

 - **Use link reference definitions for external links**

   If you have to link to external resources, don't write the URL directly in the text.
   Instead maintain all references in the form of [link reference definitions][Markdown/link-reference-definition] at the bottom of the document.

    + Make sure to give a concise name to each reference and include the title of the page you are linking to as the link label.
    + The list of link reference definitions should be sorted alphabetically.
    + Split the list of link reference definitions into logical blocks if necessary.

   ```markdown
    [doc/ModuleInterfaceFileFormat.md]:
      https://github.com/FreeProving/free-compiler/blob/master/doc/ModuleInterfaceFileFormat.md
      "Module Interface File Format — ­Free Compiler Documentation"

    [wiki/ANSI]:
      https://en.wikipedia.org/wiki/ANSI_escape_code
      "ANSI escape code — Wikipedia"
    [wiki/Unicode]:
      https://en.wikipedia.org/wiki/Unicode_subscripts_and_superscripts
      "Unicode subscripts and superscripts — Wikipedia"
   ```

   Inside the document you link to these resources as follows.

   ```markdown
   See this [wikipedia article][wiki/ANSI] for more information.
   ```

   Links of the form `[...](URL)` should be used for internal references only (i.e., to link to sections in the same document).

 - **Format and syntax highlight code snippets**

   When you use code snippets in your Markdown document (and you probably should be!) format the embedded source code as you would format any other source code.
   For example, if you have an example involving Haskell code, format that code using Brittany first.

   You should use [fenced code blocks][Markdown/fenced-code-blocks] rather than indented code blocks and specify the language of the embedded source code explicitly.
   For example, if you want to give an example hello world program written in Haskell, embed the source code as follows.

   ~~~Markdown
   ```haskell
   main :: IO ()
   main = putStrLn "Hello, World!"
   ```
   ~~~

   By specifying the language explicitly, GitHub automatically performs syntax highlighting for most languages.
   The example above should look as follows.

   ```haskell
   main :: IO ()
   main = putStrLn "Hello, World!"
   ```

   + Use `bash` as the default language of shell commands.

   + You may omit language specifiers when you just want to include a block of monospaced or pre-wrapped text (e.g., to show the output of a command).

 - **Use code spans for identifiers and filenames**

   If you have to refer to variables, functions, types, modules, files, small code fragments etc. in the text, use backticks (`` ` ``) to format them as [code spans][Markdown/code-spans].

   ```markdown
   DON'T: The append function defined in ./example/Data/List.hs
          corresponds to (++) from the Prelude.

   DO:    The `append` function defined in `./example/Data/List.hs`
          corresponds to `(++)` from the `Prelude`.
   ```

 - **Use block quotes to highlight important paragraphs**

   If you want to draw the users attention to an important paragraph (e.g., a notice or warning), this paragraph should be wrapped in a [block quote][Markdown/block-quotes].

    + The paragraph should start with a word like "Warning", "Note" or similar followed by a colon.
      The word and colon should be bold text.
    + Each line of the paragraph starts with a block quote marker (`>`).

   ```markdown

   > **Warning:** Never commit the private key to the Git repository!

   ```

   > **Remember:** Consider wisely when to use a such a paragraph and don't overdo it.
   > Most importantly, don't scare the user but inform them such that they can make their own decisions.

## Leagal information

This section discusses the legal consequences of your contributions to the FreeProving project.
We know that legal topics can be tiresome.
However, we encourage you to carefully read this section nonetheless.
Please make sure that you understand and agree with all what's is written here before you contribute.

### Privacy

The Free Compiler is developed and maintained on [GitHub][].
In order to contribute to the FreeProving project, you have to create a GitHub account.
By contributing to the FreeProving project, you agree that your contributions are published on GitHub.
GitHub's [terms of privacy][GitHub/Privacy] apply.

Note that if you contribute by the means of Git commits, your locally configured name and email address will be part of the commit message and permanently stored as part of the publicly visible commit history once you push your changes.
Of course, you are free to anonymise/pseudonymise your contributions to the extend permitted by applicable law and GitHub's [terms of service][GitHub/Terms].
We do not require you to provide any personal information.
If you chose to disclose personal information about your own person through your contributions nonetheless, you are doing so completely voluntarily and at your own risk.

Please respect the privacy of other project members and contributors.
This includes that you do not disclose their personal information (neither directly nor indirectly) unless they have deliberately done so in the past themselves.
This is especially true for but not limited to [sensitive personal information][GDPR/Art9] such as racial or ethnic origin, political opinions, religious or philosophical beliefs, health or sexual orientation.
If you have to mention another person, best practice is to use their GitHub user name instead of their real name even if you know them in person or their real name is publicly visible on their GitHub profile page.

### License

The Free Compiler is an open source project.
Its source code, associated documentation, configuration, toolchain and everything else you find in this repository is licensed under The 3-Clause BSD License.
By contributing to the FreeProving project, you agree that your contributions will be licensed under the same license.

This includes that your contributions can be

 - modified and distributed almost arbitrarily and
 - used royalty free for private or commercial purposes

by anyone provided that the requirements of the license regarding the attribution of the copyright holders are met.  
See the [LICENSE][] file for details.


[doc/ExperimentalFeatures/PatternMatchingCompilation.md]:
  https://github.com/FreeProving/free-compiler/blob/master/doc/ExperimentalFeatures/PatternMatchingCompilation.md
  "Free Compiler Documentation — Pattern Matching Compilation"

[freec/haddock]:
  https://freeproving.github.io/free-compiler/docs/master
  "Free Compiler — Haddock Documentation"
[freec/issues]:
  https://github.com/FreeProving/free-compiler/issues
  "Free Compiler ­— Issues"
[freec/pull-requests]:
  https://github.com/FreeProving/free-compiler/pulls
  "Free Compiler ­— Pull Requests"

[GDPR/Art9]:
  https://gdpr-info.eu/art-9-gdpr/
  "Art. 9 ­GDPR — Processing of special categories of personal data"

[Git/Config/autocrlf]:
  https://git-scm.com/book/en/v2/Customizing-Git-Git-Configuration#_code_core_autocrlf_code
  "core.autocrlf — Git Configuration"

[GitCommit]:
  https://chris.beams.io/posts/git-commit/
  "Chris Beams — How to Write a Git Commit Message"

[GitHub]:
  https://github.com/FreeProving/free-compiler
  "Free Compiler on GitHub"
[GitHub/Actions]:
  https://github.com/features/actions
  "GitHub Actions"
[GitHub/Privacy]:
  https://help.github.com/en/github/site-policy/github-privacy-statement
  "GitHub Privacy Statement"
[GitHub/Terms]:
  https://help.github.com/en/github/site-policy/github-terms-of-service
  "GitHub Terms of Service"

[LICENSE]:
  https://github.com/FreeProving/free-compiler/blob/master/LICENSE
  "Free Compiler — License"

[Markdown]:
  https://github.github.com/gfm/
  "GitHub Flavored Markdown Spec"
[Markdown/block-quotes]:
  https://github.github.com/gfm/#block-quotes
  "GitHub Flavored Markdown Spec — Block quotes"
[Markdown/code-spans]:
  https://github.github.com/gfm/#code-spans
  "GitHub Flavored Markdown Spec — Code spans"
[Markdown/fenced-code-blocks]:
  https://github.github.com/gfm/#fenced-code-blocks
  "GitHub Flavored Markdown Spec — Fenced code blocks"
[Markdown/link-reference-definition]:
  https://github.github.com/gfm/#link-reference-definition
  "GitHub Flavored Markdown Spec — Link reference definitions"

[software/brittany]:
  https://github.com/lspitzner/brittany/
  "Brittany"
[software/brittany#editor-integration]:
  https://github.com/lspitzner/brittany/#editor-integration
  "Brittany — Editor Integration"
[software/hlint]:
  https://github.com/ndmitchell/hlint
  "HLint"
