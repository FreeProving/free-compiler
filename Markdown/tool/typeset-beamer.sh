#!/bin/bash

script="$0"
script_dir=$(dirname "$script")
theme_dir=$(realpath "$script_dir/cau_beamertheme")

# Clone CAU beamer theme if it does not exist.
if ! [ -d "$theme_dir" ]; then
  git clone https://cau-git.rz.uni-kiel.de/RZ/document_templates/latex/beamer.git "$theme_dir"
fi

# Make theme visible to LaTeX.
export TEXINPUTS="$theme_dir:$TEXINPUTS"

# Forward all arguments and add beamer arguments.
"$script_dir"/typeset.sh "$@" --to beamer --incremental
