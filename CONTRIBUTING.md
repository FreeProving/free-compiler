# Contributing

First off, thanks for considering to contribute to the FreeProving project!
Whether it is a feature request, enhancement proposal, bug report or pull request, all kinds of contributions are welcome and greatly appreciated.

We want to make the process of contributing to this project as easy and transparent as possible.
Thus, please take the time to read this document carefully if this is your first time contributing.
Note that the following is a set of guidelines.
They are not rules and they are certainly not complete.
If you have questions or want to propose changes to this document, feel free to open an [issue][freec/issues] or [pull request][freec/pull-requests].

## Table of Contents

 1. [How Can I Contribute?](#how-can-i-contribute)
    - [Reporting Bugs](#reporting-bugs)
    - [Submitting Pull Requests](#submitting-pull-requests)
 2. [Styleguides](#styleguides)
    - [Languages without Styleguide](#languages-without-styleguide)
    - [General Guidelines](#general-guidelines)
    - [Git Commit Messages](#git-commit-messages)
    - [Haskell Styleguide](#haskell-styleguide)
    - [Haddock Styleguide](#haddock-styleguide)
    - [Markdown Styleguide](#markdown-styleguide)
 3. [Legal Information](#leagal-information)
    - [Privacy](#privacy)
    - [License](#license)

## How Can I Contribute?

### Reporting Bugs

TODO

### Submitting Pull Requests

TODO

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

 - **Capitalize the subject line**

 - **Do not end the subject line with a period**

 - **Use the present tense and imperative mood in the subject line**

 - **Wrap lines at 72 characters**

   One exception to this rule are links.
   Never wrap long links but consider placing them on a line by themselves.
   This way, the links can be copied easily and are recognized by some terminals as clickable.

   It is highly encouraged to keep the subject line below 50 characters.
   However, the 72 characters should be considered a hard limit for the subject line.

 - **Explain *what* and *why* something has been done as opposed to *how***

The language of Git commits is English.

If you want to format your commit messages use Markdown (for example, use [code spans][Markdown/code-spans] to format identifiers).
The [Markdown Styleguide](#markdown-styleguide) applies but the rules above take precedence.
For example, lines in Git commit messages are wrapped at 72 characters while they are not wrapped in Markdown documents.
Also: just paste links into the commit message's body.
There is no need for link reference definitions or links with text in commit messages.

### Haskell Styleguide

TODO

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
   # This is an ATX heading

   This is a Setext heading
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
    + Capitalize the first letter of every word except for prepositions in a heading (e.g. "How Can I Contribute?" instead of "How can I contribute?" but "Haskell to Coq" instance of "Haskell To Coq").

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

   If you want to draw the users attention to an important paragraph (e.g., a notice or warning), this paragph should be wrapped in a [block quote][Markdown/block-quotes].

    + The paragraph should start with a word like "Warning", "Note" or similar followed by a colon.
      The word and colon should be bold text.
    + Each line of the praragraph starts with a block quote marker (`>`).

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

[freec/issues]:
  https://github.com/FreeProving/free-compiler/issues
  "Free Compiler ­— Issues"
[freec/pull-requests]:
  https://github.com/FreeProving/free-compiler/pulls
  "Free Compiler ­— Pull Requests"

[GDPR/Art9]:
  https://gdpr-info.eu/art-9-gdpr/
  "Art. 9 ­GDPR — Processing of special categories of personal data"

[GitCommit]:
  https://chris.beams.io/posts/git-commit/
  "Chris Beams — How to Write a Git Commit Message"

[GitHub]:
  https://github.com/FreeProving/free-compiler
  "Free Compiler on GitHub"
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
