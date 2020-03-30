#!/bin/bash

# This script has been used to convert the original SVG logo to a PNG file.

# Get input file name or print help.
svg_file=$1
if [ -z "$svg_file" ] || [ "$svg_file" == "--help" ]; then
  echo "Usage: $0 <input-svg-file> [<output-png-file>]"
  echo
  echo "The PNG_WIDTH environment variable controls the size of the PNG file."
  exit 1
fi

# Get output file name. Defaults to the name of the input file with it's
# extension replaced by `.png`.
png_file=$2
if [ -z "$png_file" ]; then
  dirname=$(dirname "$svg_file")
  basename=$(basename -s ".svg" "$svg_file")
  png_file="$dirname/$basename.png"
fi

# The width of the PNG file defaults to 350 pixel.
if [ -z "$PNG_WIDTH" ]; then
  PNG_WIDTH=350
fi

# Convert using Inkscape.
inkscape -z -w $PNG_WIDTH "$svg_file" -e "$png_file"
