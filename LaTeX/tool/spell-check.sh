#!/bin/bash

# This script uses `aspell` to check whether there are misspelled words in
# LaTeX files.
# In addition, this script checks whether there are words, that should be
# hyphenated but are not. For this purpose, we manually maintain a list of
# compound words.

# Formatted and colored output.
bold=$(tput bold)
reset=$(tput sgr0)
red=$(tput setaf 1)
green=$(tput setaf 2)
yellow=$(tput setaf 3)

# Change into LaTeX directory.
script="$0"
script_dir=$(dirname "$script")
cd "$script_dir/.."

# Custom dictionary file that contains words to ignore.
dictionary="./tool/spell-check/dictionary"

# Custom dictionary file that contains words to hyphenate.
compound_words="./tool/spell-check/compound-words"

# Words that must (eventually) be followed by a comma.
transitional_words="./tool/spell-check/transitional-words"

# Construct a regular expression that matches any of the $transitional_words.
transitional_word_pattern=$(
  cat "$transitional_words" |
  perl -pe 'chomp if eof' |
  tr '\n' '|'
)

# Spell check all LaTeX files in the current directory.
error_code="0"
files=$(find . -name "*.tex")
for file in $files; do
  echo -n "[  ] ${bold}${file}${reset}"

  # Remove minted code blocks and math from input file.
  contents=$(
    cat "$file"                                                |

    # Ignore minted code blocks and math.
    perl -0pe 's|\$([^\$@]+\|@\$[^\$]+\$@)*?\$||smg'           |
    perl -0pe 's|\\\[(.*?)\\\]|"\n"x($1 =~ tr/\n//)|smge'      |
    perl -0pe 's|\\begin\{minted\}(.*?)\\end\{minted\}|"\n"x($1 =~ tr/\n//)|smge' |
    perl -0pe 's|\\begin\{align\*?\}(.*?)\\end\{align\*?\}|"\n"x($1 =~ tr/\n//)|smge'
  )

  # Find misspelled words.
  typos=$(
    echo "$contents" |

    # Spell check.
    aspell list                                                \
           --lang=en                                           \
           --encoding=utf-8                                    \
           --mode=tex                                          \
           --add-tex-command "aspellIgnore p"                  \
           --add-tex-command "autoref p"                       \
           --add-tex-command "bash p"                          \
           --add-tex-command "citep p"                         \
           --add-tex-command "citet p"                         \
           --add-tex-command "coq p"                           \
           --add-tex-command "coqM p"                          \
           --add-tex-command "digraph pp"                      \
           --add-tex-command "haskell p"                       \
           --add-tex-command "haskellM p"                      \
           --add-tex-command "newcommand pop"                  \
           --add-tex-command "newmintinline opp"               \
           --add-tex-command "path p"                          \
           --add-tex-command "setminted p"                     \
           --add-tex-command "texttt p"                        \
           --add-tex-command "toml p"                          |

    # Remove duplicates.
    sort                                                       |
    uniq                                                       |

    # Ignore words from dictionary file.
    grep -i -v -w -f "$dictionary"
  )

  # Find unhyphenated compound words.
  unhyphenated=$(
    echo "$contents"                                  |
    grep -w -o -f <(cat $compound_words | tr '-' ' ') |
    sort                                              |
    uniq
  )

  # Find sentences that start with a transitional word, but do not contain a
  # comma.
  missing_commas=$(
    echo "$contents" |
    perl -ne 's/(.*?)('"$transitional_word_pattern"')\s[^,]*\.(.*?)/ - '"$bold"'line $.'"$reset"': $2'"${red}${bold},${reset}"'/sg && print'
  )

  # Print misspelled words.
  if [ -z "$typos" ] && [ -z "$unhyphenated" ] && [ -z "$missing_commas" ]; then
    echo $'\r'"[${bold}${green}✓${reset}"
  else
    if [ -z "$typos" ]; then
      echo $'\r'"[${bold}${yellow}!${reset}"
    else
      echo $'\r'"[${bold}${red}✕${reset}"
    fi

    if ! [ -z "$typos" ]; then
      echo "$typos" | sed -rn 's/^(.*)$/ - '"${red}"'\1'"${reset}"' /gp'
    fi
    if ! [ -z "$unhyphenated" ]; then
      echo "$unhyphenated" | sed -rn 's/^(.*)$/ - '"${yellow}"'\1'"${reset}"' /gp'
    fi
    if ! [ -z "$missing_commas" ]; then
      echo "$missing_commas"
    fi
    error_code="1"
  fi
done

# Return falsy error code if there are misspelled words.
exit "$error_code"
