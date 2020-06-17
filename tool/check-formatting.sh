#!/bin/bash

###############################################################################
# Paths                                                                       #
###############################################################################

# Get path to the compiler's root directory.
script=$0
script_abs=$(realpath "$script")
script_dir=$(dirname "$script_abs")
script_dir_rel=$(realpath --relative-to . "$script_dir")
root_dir=$(dirname "$script_dir")
root_dir_rel=$(realpath --relative-to . "$root_dir")

# By default files in the `src` and `example` directory are formatted.
default_files=("$root_dir_rel/src" "$root_dir_rel/example")

###############################################################################
# Command Line Option Defaults                                                #
###############################################################################

# Constants for the names of the two available modes of operation.
check_mode="check"
overwrite_mode="overwrite"

# By default, the usage information is not displayed.
help=false

# By default, colored output is enabled.
enable_color_default=true; enable_color="$enable_color_default"

# By default files that are not tracked by Git are skipped.
enable_skip_default=true; enable_skip="$enable_skip_default"

# By default, check mode is enabled, i.e., files will not be overwritten.
default_mode="$check_mode"; mode="$default_mode"

# Brittany is enabled by default.
enable_brittany_default=true; enable_brittany="$enable_brittany_default"

# The formatter that normalizes line endings is enabled by default.
enable_eol_default=true; enable_eol="$enable_eol_default"

# The check whether the line length limit of 80 characters is exceeded or not
# is enabled by default.
enable_column_check_default=true;
enable_column_check="$enable_column_check_default"

###############################################################################
# Command Line Option Parser                                                  #
###############################################################################

# Parse command line options.
options=$(getopt                      \
  --long help -o h                    \
  --long brittany,no-brittany         \
  --long color,no-color               \
  --long column-check,no-column-check \
  --long eol,no-eol                   \
  --long skip,no-skip                 \
  --long overwrite                    \
  -- "$@")
if [ $? -ne 0 ]; then
  echo
  echo "Type '$script --help' for more information."
  exit 1
fi
eval set -- "$options"
while true; do
  case "$1" in
  -h | --help) help=true; shift ;;

  --brittany) enable_brittany=true; shift ;;
  --no-brittany) enable_brittany=false; shift ;;

  --color) enable_color=true; shift ;;
  --no-color) enable_color=false; shift ;;

  --column-check) enable_column_check=true; shift ;;
  --no-column-check) enable_column_check=false; shift ;;

  --eol) enable_eol=true; shift ;;
  --no-eol) enable_eol=false; shift ;;

  --skip) enable_skip=true; shift ;;
  --no-skip) enable_skip=false; shift ;;

  --overwrite) mode="$overwrite_mode"; shift ;;
  --) shift; break ;;
  *) break ;;
  esac
done

# The user can optionally specify files and directories to process.
# By default all Haskell files in the `src` and `example` directories are
# processed.
files=("$@")
if [ "${#files[@]}" -eq 0 ]; then
  files=("${default_files[@]}")
fi

###############################################################################
# Usage Message                                                               #
###############################################################################

# Utility function that prints whether a command line option is `"on"` or
# `"off"` by default.
function on_or_off() {
  local default_value="$1"
  if [ "$default_value" = true ]; then
    echo "on"
  else
    echo "off"
  fi
}

# Print usage information if the `--help` flag is set.
if [ "$help" = true ]; then
  echo "Usage: $script [options...] [input-files...]"
  echo
  echo "This script can be used to check whether there are Haskell source"
  echo "files that have not been formatted using Brittany or that contain"
  echo "non-Unix line endings. It is used by the CI pipeline and the"
  echo "'$script_dir_rel/full-test.sh' scripts."
  echo
  echo "There are the following two modes of operation."
  echo
  echo " - In *check* mode, the formatted output is discarded. The script"
  echo "   prints for each file whether would have been modified and a summary"
  echo "   at the end. You have to apply the formatting manually or in a"
  echo "   second run of the script using the '--overwrite' option."
  echo "   Check mode is enabled by default."
  echo
  echo " - In *overwrite* mode, the input files are overwritten after"
  echo "   formatting. If you enable this mode, there is a chance that"
  echo "   uncommitted changes are lost. Thus, it is strongly recommended"
  echo "   to backup your files beforehand (e.g., by staging them using the"
  echo "   'git add' command)."
  echo
  echo "If no input files are specified, all source files in the following"
  echo "directories are processed by default: ${default_files[@]}."
  echo
  echo "Command line options:"
  echo "  -h    --help                Display this message."
  echo "        --[no-]brittany       Enable formatting using Brittany."
  echo "                              ('$(on_or_off                     \
                                          "$enable_brittany_default")'" \
                                       "by default)"
  echo "        --[no-]color          Enable colored output."
  echo "                              ('$(on_or_off                     \
                                          "$enable_brittany_default")'" \
                                       "by default)"
  echo "        --[no-]column-check   Enable 80 column line length limit check."
  echo "                              ('$(on_or_off                     \
                                          "$enable_column_check_default")'" \
                                       "by default)"
  echo "        --[no-]eol            Enable normalization of line endings."
  echo "                              ('$(on_or_off                     \
                                          "$enable_eol_default")'" \
                                       "by default)"
  echo "        --[no-]skip           Enable skipping of untracked files."
  echo "                              ('$(on_or_off                     \
                                          "$enable_skip_default")'" \
                                       "by default)"
  echo "        --overwrite           Enable overwrite mode"
  echo "                              (see above for details)."
  exit 0
fi

###############################################################################
# Colored Output                                                              #
###############################################################################

# Enable/disable colored output.
if [ "$enable_color" = false ]; then
  function tput {
    echo ""
  }
fi
red=$(tput setaf 1)
green=$(tput setaf 2)
yellow=$(tput setaf 3)
bold=$(tput bold)
reset=$(tput sgr0)

###############################################################################
# Dependencies                                                                #
###############################################################################

# Check whether brittany is installed if the Brittany formatter is enabled.
if [ "$enable_brittany" = true ] && ! which brittany >/dev/null 2>&1; then
  echo "${red}${bold}Error:${reset}" \
       "${bold}Could not find Brittany.${reset}"
  echo " |"
  echo " | Run the ${bold}cabal new-install brittany${reset} to install it."
  echo " | Also make sure that ${bold}brittany${reset} is in your" \
       "${bold}\$PATH${reset}!"
  exit 1
fi

###############################################################################
# Utility Functions                                                           #
###############################################################################

# Utility function that returns either its first argument in check mode or
# its second argument in overwrite mode.
function select_by_mode() {
  case "$mode" in
    "$check_mode")     echo "$1" ;;
    "$overwrite_mode") echo "$2" ;;
  esac
}

# Utility function that writes its `stdin` to a temporary file and copies
# the contents to the given file afterwards. This is intened to be used
# instead of an redirect if the file to redirect to is also used by the
# command whose output to redirect.
function write_to_file() {
  local file="$1"
  local temp_file=$(mktemp)
  cat - >"$temp_file"
  mv "$temp_file" "$file"
}

###############################################################################
# Statistics                                                                  #
###############################################################################

# Counters for statistics.
okay_counter=0
error_counter=0
skipped_counter=0
processed_counter=0

# Counters for error statistics.
eol_counter=0
format_counter=0
column_counter=0

###############################################################################
# Formatter and Check Runners                                                 #
###############################################################################

# Applies the given command (first argument) to the given contents of the file
# with them given name (second argument).
#
# Prints the given message (fourth argument) and increments the variable with
# the given name (third argument) if the file has been changed.
#
# Sets the `is_okay` environment variable to `false` if the file has been
# changed or there was an error executing the command. Returns the exit code
# of the command.
#
# The last argument indicates whether the formatter is enabled or not. Returns
# status code `0` without modifying the file if the formatter is not enabled.
function run_formatter() {
  local command="$1"
  local file="$2"
  local counter_var="$3"
  local msg="$4"
  local enabled="$5"

  # Test whether the formatter is enabled or not.
  if [ "$enabled" = false ]; then
    return 0
  fi

  # Save hash of file before the command such that we can test whether the
  # command changed the file.
  hash_before=$(sha256sum "$file")

  # Run the command on the file.
  "$command" "$file" >/dev/null 2>&1
  local exit_code=$?

  # Test whether the command was successful.
  if [ "$exit_code" -eq 0 ]; then
    # Test whether the file has changed.
    hash_after=$(sha256sum "$temp_file")
    if [ "$hash_before" != "$hash_after" ]; then
      # The file has changed. Print the message and increment the counter.
      if [ "$is_okay" = false ]; then
        echo -n " and "
      fi
      echo -n "$msg"
      eval $counter_var=$(expr ${!counter_var} + 1)
      is_okay=false
    fi
  else
    echo "${red}${bold}ERROR${reset}"
    error_counter=$(expr $error_counter + 1)
    is_okay=false
  fi
  return "$exit_code"
}

# A check is like a formatter (see `run_formatter`), but it never changes the
# file. Whether a check was successful or not is determined from the status
# code returned by the command instead of the hash of the checked file.
#
# Always returns status code `0`.
function run_check() {
  local command="$1"
  local file="$2"
  local counter_var="$3"
  local msg="$4"
  local enabled="$5"

  # Test whether the check is enabled or not.
  if [ "$enabled" = true ]; then
    # Run the command on the file.
    "$command" "$file" >/dev/null 2>&1
    local exit_code=$?

    # Test whether the command was sucessful or not.
    if [ "$exit_code" -ne 0 ]; then
      echo -n "$msg"
      eval $counter_var=$(expr ${!counter_var} + 1)
      is_okay=false
    fi
  fi

  # Always return `0` such that subsequent checks still run.
  return 0
}

###############################################################################
# Formatters                                                                  #
###############################################################################

# Formatter that converts Windows line endings (CRLF) to Unix line endings (LF)
# by removing all carriage return (CR) bytes.
function eol_formatter() {
  local file="$1"
  cat "$file" | tr -d '\r' | write_to_file "$file"
}
eol_formatter_msg=$(select_by_mode                      \
    "${yellow}${bold}HAS WRONG LINE ENDINGS${reset}"  \
    "${yellow}${bold}NORMALIZED LINE ENDINGS${reset}" \
  )

# Formatter that formats code with Brittany.
function brittany_formatter() {
  local file="$1"
  brittany --write-mode=inplace "$file"
}
brittany_formatter_msg=$(select_by_mode           \
    "${red}${bold}NEEDS FORMATTING${reset}"     \
    "${green}${bold}HAS BEEN FORMATTED${reset}" \
  )

###############################################################################
# Checks                                                                      #
###############################################################################

# Check that tests whether a file contains lines that exceed the 80 character
# line length limit.
function column_check() {
  local file="$1"

  # Search for long lines but ignore lines that contain URLs.
  cat "$file" | grep -Pv 'https?:' | grep -Pq '^.{81,}$'

  # Return with status code `1` if a line that exceeds the limit was found.
  local status_code="$?"
  if [ "$status_code" -eq 0 ]; then
    return 1
  fi
}
column_check_msg="${yellow}${bold}EXCEEDS COLUMN LIMIT${reset}"

###############################################################################
# Run All Enabled Formatters and Checks                                       #
###############################################################################

# Process all given Haskell files that are tracked by `git` and count how
# many files are not formatted or encoded correctly.
for file in $(find "${files[@]}" -name '*.hs' -type f); do
  # Skip files that are not tracked by Git unless the `--no-skip` command
  # line flag has been specified.
  if [ "$enable_skip" = false ] ||
     ! git rev-parse --is-inside-work-tree >/dev/null 2>&1 ||
     git ls-files --error-unmatch "$file" >/dev/null 2>&1; then
    # Print which file is processed.
    echo -n "$(select_by_mode "Checking" "Formatting")" \
            "${bold}$file${reset} ... "
    processed_counter=$(expr $processed_counter + 1)
    is_okay=true

    # Create temporary file for formatting.
    temp_file=$(mktemp)
    cp "$file" "$temp_file"

    # Run formatters.
    run_formatter eol_formatter "$temp_file" \
                  "eol_counter"              \
                  "$eol_formatter_msg"       \
                  "$enable_eol" &&
    run_formatter brittany_formatter "$temp_file" \
                  "format_counter"                \
                  "$brittany_formatter_msg"       \
                  "$enable_brittany" &&
    run_check column_check "$temp_file" \
              "column_counter"          \
              "$column_check_msg"       \
              "$enable_column_check"

    # Stop processing the current file if any formatter or check failed.
    error_code="$?"
    if [ "$error_code" -ne 0 ]; then
      continue
    fi

    # Test whether all checks where successful.
    if [ "$is_okay" = true ]; then
      select_by_mode "${green}${bold}OK${reset}" \
                     "${bold}UNCHANGED${reset}"
      okay_counter=$(expr $okay_counter + 1)

      # Clean up.
      rm "$temp_file"
    else
      # Error messages have been printed above after the file name.
      # Move to new line.
      echo

      # Overwrite input file if overwrite mode is enabled.
      # Otherwise clean up the temporary file.
      if [ "$mode" = "$overwrite_mode" ]; then
        mv "$temp_file" "$file"
      else
        rm "$temp_file"
      fi
    fi
  else
    # The file is not tracked by Git.
    echo "Skipping ${bold}$file${reset} ... ${bold}NOT TRACKED${reset}"
    skipped_counter=$(expr $skipped_counter + 1)
  fi
done

###############################################################################
# Summary                                                                     #
###############################################################################

# Print statistics.
echo "${bold}"
echo "----------------------------------------------------------------------"
echo "${reset}"
echo "Processed ${bold}$processed_counter${reset} and" \
     "skipped ${bold}$skipped_counter${reset} files."

# Test whether all processed files were okay.
if [ "$okay_counter" -eq "$processed_counter" ]; then
  echo "${green}${bold}All processed files are formatted correctly.${reset}"
else
  # Print command error statistics.
  if [ "$error_counter" -ne 0 ]; then
    echo "${red}${bold}Error:${reset}"                                     \
         "There were ${bold}$error_counter${reset} errors when processing" \
         "files."
  fi

  # Print line ending error statistics.
  if [ "$eol_counter" -ne 0 ]; then
    echo $(select_by_mode "${yellow}${bold}Warning:${reset}"          \
                          "${bold}Info:${reset}")                     \
         "There were ${bold}$eol_counter${reset} files with non-Unix" \
         "line endings."
  fi

  # Print formatting error statistics.
  if [ "$format_counter" -ne 0 ]; then
    echo $(select_by_mode "${red}${bold}Error:${reset}"                  \
                          "${bold}Info:${reset}")                        \
         "There were ${bold}$format_counter${reset} files that were not" \
         "formatted correctly."
  fi

  # Print line length limit error statistics.
  if [ "$column_counter" -ne 0 ]; then
    echo "${yellow}${bold}Warning:${reset}"                                \
         "There were ${bold}$column_counter${reset} files that exceed the" \
         "line length limit of 80 characters."
  fi

  # Exit with status code `1` in check mode if any check failed.
  if [ "$mode" = "$check_mode" ]; then
    exit 1
  fi
fi
