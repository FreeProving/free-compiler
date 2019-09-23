#!/bin/bash

clear
echo
cat "$1"  | pygmentize -l haskell | sed 's/^/     /'
echo

read _
echo '----------------------------------------------------------------------'

temp=$(mktemp -d)
haskell-to-coq-compiler "$1" >"$temp/output.txt" 2>"$temp/errors.txt"

echo
cat "$temp/errors.txt" | sed 's/^/     /'
echo
cat "$temp/output.txt" | pygmentize -l coq | sed 's/^/     /'
echo
rm -r "$temp"
