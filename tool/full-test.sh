#!/bin/bash

# This script can be used to simulate the CI pipeline locally.
# First it tests whether the required software (i.e., GHC, Cabal and Coq) is
# installed in the right version.
# Then, it executes all build steps locally and runs the unit tests.
# If this script reports an error, it is very likely that the CI pipeline
# would fail as well when the current state of the repository is pushed.
# If no error is reported, there is no guarantee that the CI pipeline will
# succeed. Local caches or configurations could distort the results.
# However, this script is much faster and more convenient than waiting
# for the CI pipeline to finish and should be executed before each commit.
# It is especially useful to spot mistakes in the documentation for example
# since building the documentation is not part of the usual workflow.

###############################################################################
# ANSI and Unicode                                                            #
###############################################################################

# ANSI escape sequence to go to start of line and clear the line.
go_home=$'\033[1G'
clear_line=$'\033[2K'
clear_rest_of_line=$'\033[0K'

# ANSI escape sequences to save and restore the cursor position.
save_cursor=$'\033[s'
restore_cursor=$'\033[u'

# ANSI escape sequences to move the cursor.
cursor_up=$'\033[1A'
cursor_down=$'\033[1B'

# ANSI escape sequences for colored output.
default=""
red=$'\033[31m'
green=$'\033[32m'
yellow=$'\033[33m'
gray=$'\033[90m'
reset=$'\033[0m'

# Makes text bold using ANSI escape sequences.
function bold() {
  local text=$1
  echo $'\033[1m'"$text"$'\033[22m'
}

# Unicode characters.
check_mark="✓"
cross_mark="✗"
question_mark="?"

# Selects a random emoji for error messages.
function fail_emoji() {
  local emojis=("🤔" "🤔" "😷" "🤒" "🤕" "🤢" "🤮" "😵" "🧐" "😕"
                "😟" "🙁" "😮" "😱" "😞" "😓" "😩" "😫" "🤬" "💩")
  echo "${emojis[$RANDOM % ${#emojis[@]} ]}"
}

# Selects a random emoji for success messages.
function success_emoji() {
  local emojis=("😊" "😇" "😌" "🥳" "😎" "🤓" "😤" "🤩" "🤯" "😁"
                "🙈" "👌" "👍" "👏" "💪" "🎉" "🎊" "🎈" "💥" "💯")
  echo "${emojis[$RANDOM % ${#emojis[@]} ]}"
}

# Selects a random emoji for to display when a command takes a long time.
function waiting_emoji() {
  local emojis=("🙄" "😪" "😴")
  echo "${emojis[$RANDOM % ${#emojis[@]} ]}"
}

###############################################################################
# Text processing                                                             #
###############################################################################

# Removes the given number of leading spaces from the input.
function trimN() {
  local n=$1
  sed -E 's/^[ ]{0,'"$n"'}//'
}

# Prepends every line of its input with the given string.
function indent() {
  local indentation=$1
  while IFS= read -r line; do
    echo "$indentation$line"
  done
}

###############################################################################
# Status messages                                                             #
###############################################################################

# Formats the status badge for a status message.
function status_badge() {
  local symbol_color=$1
  local message_color=$2
  local symbol=$3
  echo -n "${message_color} [ ${symbol_color}$symbol${message_color} ]${reset}"
}

# Replaces the current status badge.
function update_status_badge() {
  echo -n "${save_cursor}${go_home}"
  status_badge "$@"
  echo -n "${restore_cursor}"
}

# Formats a status message.
function status() {
  local symbol_color=$1
  local message_color=$2
  local symbol=$3
  local message=$4
  status_badge "$symbol_color" "$message_color" "$symbol"
  echo -n " ${message_color}$(bold "$message")${reset}"
}

# Replaces the current status message and starts a new line for the
# next status.
function update_status() {
  echo -n "${go_home}${clear_line}"
  status "$@"
  echo
}

# Selects a random set of characters to use in the progress indicator.
function random_spinner() {
  local spinners=(
    "⠋ ⠙ ⠹ ⠸ ⠼ ⠴ ⠦ ⠧ ⠇ ⠏"
    "⣾ ⣽ ⣻ ⢿ ⡿ ⣟ ⣯ ⣷"
    "⠋ ⠙ ⠚ ⠞ ⠖ ⠦ ⠴ ⠲ ⠳ ⠓"
    "⠄ ⠆ ⠇ ⠋ ⠙ ⠸ ⠰ ⠠ ⠰ ⠸ ⠙ ⠋ ⠇ ⠆"
    "⠋ ⠙ ⠚ ⠒ ⠂ ⠂ ⠒ ⠲ ⠴ ⠦ ⠖ ⠒ ⠐ ⠐ ⠒ ⠓ ⠋"
    "⠁ ⠉ ⠙ ⠚ ⠒ ⠂ ⠂ ⠒ ⠲ ⠴ ⠤ ⠄ ⠄ ⠤ ⠴ ⠲ ⠒ ⠂ ⠂ ⠒ ⠚ ⠙ ⠉ ⠁"
    "⠈ ⠉ ⠋ ⠓ ⠒ ⠐ ⠐ ⠒ ⠖ ⠦ ⠤ ⠠ ⠠ ⠤ ⠦ ⠖ ⠒ ⠐ ⠐ ⠒ ⠓ ⠋ ⠉ ⠈"
    "⠁ ⠁ ⠉ ⠙ ⠚ ⠒ ⠂ ⠂ ⠒ ⠲ ⠴ ⠤ ⠄ ⠄ ⠤ ⠠ ⠠ ⠤ ⠦ ⠖ ⠒ ⠐ ⠐ ⠒ ⠓ ⠋ ⠉ ⠈ ⠈"
    "⢹ ⢺ ⢼ ⣸ ⣇ ⡧ ⡗ ⡏"
    "⢄ ⢂ ⢁ ⡁ ⡈ ⡐ ⡠"
    "⠁ ⠂ ⠄ ⡀ ⢀ ⠠ ⠐ ⠈"
  )
  echo "${spinners[$RANDOM % ${#spinners[@]} ]}"
}

# Runs currently during `step` and displays a spinning progress indicator.
function progress_indicator() {
  local rounds=$1
  local spinner=$2

  # Write each character for short time into status badge.
  local delay=0.1
  local chars=($spinner)
  for char in ${chars[@]}; do
    update_status_badge "$default" "$default" "$char";  sleep $delay
  done

  # Print waiting emoji and hint to cancel the operation when the animation
  # played 30 or 60 times, respectively.
  if [ $rounds == "30" ]; then
    echo -n " $(waiting_emoji) "
  fi
  if [ $rounds == "60" ]; then
    echo -n " | $(bold "Hint:")" \
            "Press $(bold "CTRL + C") to cancel anytime"
  fi

  progress_indicator $(expr $rounds + 1) "$spinner"
}

# Prints a success or failure message.
function print_message() {
  local color=$1
  local title=$2
  local message=$3
  echo
  echo "${color}$(bold "$title")${reset}"
  echo -n "${color}"
  echo "$message" | trimN 6 | indent " | "
  echo -n "${reset}"
}

###############################################################################
# Testing required software                                                   #
###############################################################################

# Utility function to get the version of an installed program.
function version() {
  local $program=$1
  bash -c "$program --version" | grep -Po '\d+\.\d+\.\d+(\.\d+)?' | head -n 1
}

# Utility function to tests whether the given version of a program is installed.
function check_version() {
  local program_name=$1
  local program=$2
  local supported_versions=()
  IFS='|' read -r -a supported_versions <<< "$3"
  local installation_command=$4

  local supported_versions_text=""
  for i in "${!supported_versions[@]}"; do
    local supported_version="${supported_versions[$i]}"
    if ! [ -z "$supported_versions_text" ]; then
      if [ "$(expr "$i" + 1)" == "${#supported_versions[@]}" ]; then
        supported_versions_text+=" or "
      else
        supported_versions_text+=", "
      fi
    fi
    supported_versions_text+="$(bold "$supported_version")"
  done

  # Check whether the program is installed.
  if ! which $program >/dev/null; then
    update_status "$red" "$gray" "$cross_mark" "Missing required software"
    print_message "$red" "Oops, something went wrong! $(fail_emoji)" "\
      Expected $(bold "$program_name") in version $supported_versions_text
      to be installed, but the command $(bold "$program") could not be found.

      Try to install it by running the following command

      $(bold "$installation_command" | indent "    ")

      Also make sure that your PATH variable is set correctly."
    exit 1
  fi

  # Check whether a supported version is installed.
  local version=$(version $program)
  for supported_version in "${supported_versions[@]}"; do
    if [[ "$version" == $supported_version ]]; then
      # The installed version is supported.
      return 0
    fi
  done

  # The installed version is not supported.
  echo \
    "• Expected $(bold "$program_name") in version $supported_versions_text" \
    "to be installed, but found version $(bold "$version")."
  return 1
}

# Tests whether the required software versions are installed.
function check_required_software() {
  status "$default" "$default" "*" "Checking required software..."
  local temp_log=$(mktemp)
  check_version "GHC" ghc '8.6.5' '
      sudo add-apt-repository ppa:hvr/ghc
      sudo apt update
      sudo apt install ghc-8.6.5' >> "$temp_log"
  check_version "Cabal" cabal '2.4.1.*|3.*' '
      sudo add-apt-repository ppa:hvr/ghc
      sudo apt update
      sudo apt install cabal-install-2.4' >> "$temp_log"
  check_version "Coq" coqc '8.8.*|8.9.*|8.10.*|8.11.*' '
      sudo apt install opam
      opam init
      eval `opam config env`
      opam repo add coq-released https://coq.inria.fr/opam/released
      opam update
      opam install coq.8.11.0' >> "$temp_log"
  check_version "HLint" hlint '3.1.*' '
      cabal new-install hlint' >> "$temp_log"
  check_version "Brittany" brittany '0.12.*' '
      cabal new-install brittany' >> "$temp_log"

  # Print reported messages.
  local log_text=$(cat "$temp_log")
  rm "$temp_log"
  if [ -z "$log_text" ]; then
    update_status "$green" "$gray" "$check_mark" "Found required software"
  else
    update_status "$yellow" "$gray" "$question_mark" "Unsupported software versions"
    print_message "$yellow" "Something may go wrong!" "$log_text"
    echo
  fi
}

###############################################################################
# Pipeline tests                                                              #
###############################################################################

# Flag that is set to `0` is any step has been canceled using CTRL + C
canceled_any=1

# Runs a command in the background and display status information.
function step() {
  local pending_msg=$1
  local success_msg=$2
  local failure_msg=$3
  local cancel_message=$4
  local command=$5

  # Create error log.
  local error_log=$(mktemp)
  echo " [ $(date) ] Error log for:" >$error_log
  echo "    $command" >>$error_log
  echo "--------------------------------------------------------" >>$error_log
  echo >>$error_log

  # Show progress indicator.
  status "$default" "$default" "-" "$pending_msg..."
  progress_indicator 0 "$(random_spinner)" &
  local progress_indicator_pid=$!

  # Catch CTRL + C.
  local canceled=1
  function ctrl_c() {
    canceled=0
    canceled_any=0
  }
  trap ctrl_c INT

  # Run command.
  bash -c "$command" >>$error_log 2>&1
  local exit_code=$?

  # Handle CTRL + C.
  if [ "$canceled" == "0" ]; then
    trap - INT
    update_status "$yellow" "$gray" "$question_mark" "$cancel_message"

    # Ask whether to continue with remaining tests or exit.
    while true; do
      read -n 1 -p "Do you want to run the remaining tests? [y/N] " answer
      echo -n "${go_home}${clear_line}"
      case $answer in
        [Yy]* ) return;;
        * )     exit 0;;
      esac
    done
  fi

  # Stop progress indicator.
  kill $progress_indicator_pid
  wait $progress_indicator_pid >/dev/null 2>&1

  # Add exit code to error log.
  echo >>$error_log
  echo "--------------------------------------------------------" >>$error_log
  echo " [ $(date) ] Exit code: $exit_code" >>$error_log

  # Print error message when the command failed.
  if ! [ $exit_code == "0" ]; then
    update_status "$red" "$gray" "$cross_mark" "$failure_msg"
    print_message "$red" "Oops, something went wrong! $(fail_emoji)" "\
      Failed to run the following command

      $(bold "$command" | indent "    ")

      The command exited with $(bold "status code $exit_code")
      Output has been logged to $(bold "$error_log")"
    exit 1
  fi

  # Remove error log.
  rm $error_log

  # Print success message
  update_status "$green" "$gray" "$check_mark" "$success_msg"
}

# Change into the compiler's root directory.
script=$(realpath "$0")
script_dir=$(dirname "$script")
root_dir=$(dirname "$script_dir")
cd "$root_dir"

# Make sure that the required software is installed.
check_required_software

# Make sure that we are working with the latest version of all dependencies.
step "Downloading latest package list"          \
     "Downloaded latest package list"           \
     "Failed to download latest package list"   \
     "Canceled download of latest package list" \
     "cabal new-update"

# We don't want to rebuild dependencies every time but the modules in this
# repository should be recompiled. Otherwise, Cabal does not realize, that the
# previously compiled modules may have been compiled using `-Wwarn`.
cached_cabal_builds=$(find dist-newstyle/ -type d -name "freec-*" | head -n 1)
if [ -d "$cached_cabal_builds" ]; then
  step "Removing cached builds"          \
       "Removed cached builds"           \
       "Failed remove cached builds"     \
       "Canceled removing cached builds" \
       "rm -r '$cached_cabal_builds'"
fi

# Build the internal compiler library and its dependencies.
step "Installing compiler library dependencies"               \
     "Installed compiler library dependencies"                \
     "Failed to install compiler library dependencies"        \
     "Canceled installation of compiler library dependencies" \
     "cabal new-build freec-internal --only-dependencies"
step "Building the compiler library"        \
     "Built compiler library successfully"  \
     "Failed to build the compiler library" \
     "Canceled compiler library build"      \
     "cabal new-build freec-internal"

# Build the unit tests and their dependencies.
step "Installing test suite dependencies"               \
     "Installed test suite dependencies"                \
     "Failed to install test suite dependencies"        \
     "Canceled installation of test suite dependencies" \
     "cabal new-build freec-unit-tests --only-dependencies"
step "Building the test suite"        \
     "Built test suite successfully"  \
     "Failed to build the test suite" \
     "Canceled test suite build"      \
     "cabal new-build freec-unit-tests"

# Build the command line interface and its dependencies.
step "Installing command line interface dependencies"               \
     "Installed command line interface dependencies"                \
     "Failed to install command line interface dependencies"        \
     "Canceled installation of command line interface dependencies" \
     "cabal new-build freec --only-dependencies"
step "Building the command line interface"        \
     "Built command line interface successfully"  \
     "Failed to build the command line interface" \
     "Canceled command line interface build"      \
     "cabal new-build freec"

# Build the Coq base library.
step "Building the Coq base library"        \
     "Built Coq base library successfully"  \
     "Failed to build the Coq base library" \
     "Canceled Coq base library build"      \
     "./tool/compile-coq.sh --recompile base/coq"

# Build the Agda base library.
step "Building the Agda base library"        \
     "Built Agda base library successfully"  \
     "Failed to build the Agda base library" \
     "Canceled Agda base library build"      \
     "./tool/check-agda-base-lib.sh -r"

# Generate Haddock documentation.
step "Generating Haddock documentation"              \
     "Generated Haddock documentation successfully"  \
     "Failed to generate Haddock documentation"      \
     "Canceled Haddock documentation generation"     \
     "./tool/make-docs.sh"

# Run tests.
step "Running unit tests"     \
     "All unit tests passed"  \
     "Some unit tests failed" \
     "Canceled unit tests"    \
     "cabal new-run freec-unit-tests"

step "Compiling examples"               \
     "Compiled examples successfully"   \
     "Failed to compile examples"       \
     "Canceled compilation of examples" \
     "cabal new-run freec --                           \\
        --transform-pattern-matching                   \\
        --dump-transformed-modules example/transformed \\
        -b ./base/coq                                  \\
        -o ./example/generated                         \\
        \$(find ./example -path ./example/transformed -prune -o -name \"*.hs\" -print)"

step "Testing generated Coq code"               \
     "Generated Coq code compiles successfully" \
     "Generated Coq code does not compile"      \
     "Canceled test of generated Coq code"      \
     "./tool/compile-coq.sh --recompile example"

# Check code style.
step "Checking code with HLint"          \
     "HLint had no suggestions"          \
     "HLint suggested changes"           \
     "Canceled checking code with HLint" \
     "hlint src"

step "Checking code style with Brittany"            \
     "All Haskell files have been formatted"        \
     "There are Haskell files that need formatting" \
     "Canceled checking code style with Brittany"   \
     "./tool/check-formatting.sh"

# Test whether the user canceled any of the steps above using CTRL + C.
if [ "$canceled_any" == "0" ]; then
  print_message "$yellow" \
    "Some steps were canceled, but the rest seems to work!" \
    "You can still push your local changes but there is
     a high risk that the CI pipeline fails in case the
     skipped steps are faulty."
else
  # All steps above were successful.
  print_message "$green" "Yay, everything seems to work! $(success_emoji)" "\
    It should be safe to push your local changes.
    The CI pipeline could still fail, but that is
    very unlikely."
fi
