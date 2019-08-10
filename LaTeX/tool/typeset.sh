#!/bin/bash

# Formatted and colored output.
bold=$(tput bold)
reset=$(tput sgr0)

# Change into LaTeX directory.
script="$0"
script_dir=$(dirname "$script")
cd "$script_dir/.."

# Name of the LaTeX file to typeset.
input_file="thesis.tex"
bib_name="thesis"

# Additional arguments for `pdflatex`.
# The `-shell-escape` flag is necessary because we use the `minted` package.
latex_options=(
  "-shell-escape"
)

# Helper function that runs `pdflatex` and filters error messages.
function run_latex {
  texfot --quiet                         \
         --no-stderr                     \
         --ignore "^This is XeTeX"       \
         --ignore "^Output written on"   \
        "xelatex  -halt-on-error                 \
                  -interaction 'nonstopmode'     \
                  -output-driver 'xdvipdfmx -z0' \
                  '${latex_options[@]}'          \
                  '$input_file'"
}

# Run LaTeX. We have to run LaTeX multiple times in order to get the table of
# contents and all references right.
echo $'\n'"${bold}Running LaTeX... (1/3)${reset}" && run_latex &&
echo $'\n'"${bold}Running BibTeX... (1/1)${reset}" && bibtex "$bib_name" &&
echo $'\n'"${bold}Running LaTeX... (2/3)${reset}" && run_latex &&
echo $'\n'"${bold}Running LaTeX... (3/3)${reset}" && run_latex
