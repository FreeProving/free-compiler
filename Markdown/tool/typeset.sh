#!/bin/bash

script="$0"
script_dir=$(dirname "$script")
pandoc_scripts_dir=$(realpath "$script_dir/pandoc-scripts")

# Clone repositorty with custom pandoc scripts and filters if it was not
# cloned before.
if ! [ -d "$pandoc_scripts_dir" ]; then
  git clone git@bitbucket.org:just95/pandoc-scripts.git "$pandoc_scripts_dir"
fi

# Forward all arguments.
"$pandoc_scripts_dir"/typeset.sh "$@"
