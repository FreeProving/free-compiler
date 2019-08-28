#!/bin/bash

# Formatted and colored output.
bold=$(tput bold)
reset=$(tput sgr0)
red=$(tput setaf 1)
green=$(tput setaf 2)

# Change into LaTeX directory.
script="$0"
script_dir=$(dirname "$script")
cd "$script_dir/.."

# Custom dictionary file that contains words to ignore.
dictionary=".dictionary"

# Spell check all LaTeX files in the current directory.
error_code="0"
files=$(find . -name "*.tex")
for file in $files; do
  echo -n "[  ] ${bold}${file}${reset}"
  words=$(
    cat "$file"                                             |

    # Ignore minted code blocks.
    tr '\n' ' '                                             |
    sed -e 's/\\begin{minted}.*\end{minted}//g'             |

    # Spell check.
    aspell list                                             \
           --lang=en                                        \
           --mode=tex                                       \
           --add-tex-command "autoref p"                    \
           --add-tex-command "newcommand pop"               \
           --add-tex-command "setminted p"                  \
           --add-tex-command "newmintinline opp"            \
           --add-tex-command "haskell p"                    \
           --add-tex-command "coq p"                        |

    # Remove duplicates.
    sort                                                    |
    uniq                                                    |

    # Ignore words from dictionary file.
    grep -v -w -f "$dictionary"
  )

  # Print misspelled words.
  if [ -z "$words" ]; then
    echo $'\r'"[${bold}${green}✓${reset}"
  else
    echo $'\r'"[${bold}${red}✕${reset}"
    echo "$words" | sed -rn 's/^(.*)$/ - '"${red}"'\1'"${reset}"' /gp'
    error_code="1"
  fi
done

# Return falsy error code if there are misspelled words.
exit "$error_code"
