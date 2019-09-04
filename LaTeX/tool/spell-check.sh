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

# Spell check all LaTeX files in the current directory.
error_code="0"
files=$(find . -name "*.tex")
for file in $files; do
  echo -n "[  ] ${bold}${file}${reset}"

  # Find misspelled words.
  typos=$(
    cat "$file"                                                |

    # Ignore minted code blocks and math.
    perl -0pe 's|\\begin\{minted\}.*?\\end\{minted\}||smg'     |
    perl -0pe 's|\$([^\$@]+\|@\$[^\$]+\$@)*?\$||smg'           |
    perl -0pe 's|\\\[.*?\\\]||smg'                             |
    perl -0pe 's|\\begin\{align\*?\}.*?\\end\{align\*?\}||smg' |

    # Spell check.
    aspell list                                                \
           --lang=en                                           \
           --encoding=utf-8                                    \
           --mode=tex                                          \
           --add-tex-command "aspellIgnore p"                  \
           --add-tex-command "autoref p"                       \
           --add-tex-command "coq p"                           \
           --add-tex-command "coqM p"                          \
           --add-tex-command "digraph pp"                      \
           --add-tex-command "haskell p"                       \
           --add-tex-command "haskellM p"                      \
           --add-tex-command "newcommand pop"                  \
           --add-tex-command "newmintinline opp"               \
           --add-tex-command "setminted p"                     \
           --add-tex-command "texttt p"                        |

    # Remove duplicates.
    sort                                                       |
    uniq                                                       |

    # Ignore words from dictionary file.
    grep -v -w -f "$dictionary"
  )

  # Find unhyphenated compound words.
  unhyphenated=$(
    cat "$file"                                       |
    grep -w -o -f <(cat $compound_words | tr '-' ' ') |
    sort                                              |
    uniq
  )

  # Print misspelled words.
  if [ -z "$typos" ] && [ -z "$unhyphenated" ]; then
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
    error_code="1"
  fi
done

# Return falsy error code if there are misspelled words.
exit "$error_code"
