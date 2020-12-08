#!/bin/bash

# This script is used by workflows to "slug" arbitrary environment variables.
# We have to "slug" names of branches such that it is save to use them in URLs.
# The code for the function below has been copied from the following action.
#
#   https://github.com/rlespinasse/github-slug-action
#
# We've adapted their script to work with arbitrary environment variables.
#
#   usage: slug.sh <input-variable-contents> <output-variable-name>

slug_ref() {
    echo "$1" \
         | tr "[:upper:]" "[:lower:]" \
         | sed -r 's#refs/[^\/]*/##;s/[~\^]+//g;s/[^a-zA-Z0-9]+/-/g;s/^-+\|-+$//g;s/^-*//;s/-*$//' \
         | cut -c1-63
}

echo "$2=$(slug_ref "$1")" >> $GITHUB_ENV
