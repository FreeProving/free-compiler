#!/bin/bash

# This script updates the `floskell.json` configuration file by merging the
# `floskell.toml` template from the guidelines repository with the file in
# this repository and converting it to JSON.
#
# This script is indented by be used by maintainers whenever the template or
# repository-specific configuration file changes to keep the generated file
# up to date.

# Change into the compiler's root directory.
script=$(realpath "$0")
script_dir=$(dirname "$script")
root_dir=$(dirname "$script_dir")
cd "$root_dir"

# URL of the template configuration file.
template_host="raw.githubusercontent.com"
template_repo="FreeProving/guidelines"
template_branch="main"
template_url="https://$template_host/$template_repo/$template_branch/floskell.toml"

# Download the latest version of the template configuration.
temp_dir=$(mktemp -d)
template_file="$temp_dir/floskell.toml"
echo "Fetching template configuration file... "
curl -fs -S "$template_url" -o "$template_file"

# Cancel if the download failed.
status_code="$?"
if [ "$status_code" -ne 0 ]; then
  echo "Download of template configuration file failed."
  rm -r $temp_dir
  exit 1
fi

# Merge the template and repository-specific configuration files.
echo "Merging and converting to JSON..."
docker run                 \
  -v "$PWD:/pwd"           \
  -v "$temp_dir:/template" \
  just95/toml-to-json      \
  /template/floskell.toml  \
  /pwd/floskell.toml       \
 >floskell.json

# Clean up.
rm -r $temp_dir
