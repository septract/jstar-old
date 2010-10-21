#!/bin/bash 

# counts
PASSED_COUNT=0
TESTS_COUNT=0

# Default values for options
CLEAN=0
HELP=0
QUIET=0
TESTS=""
VERBOSE=0

# UI
PROGRESS_STRING="/-\\|"
PROGRESS_STRING_INDEX=0
indicate_progress() {
  echo -ne "\r${PROGRESS_STRING:PROGRESS_STRING_INDEX:1}"
  PROGRESS_STRING_INDEX=$((($PROGRESS_STRING_INDEX+1)%${#PROGRESS_STRING}))
}
say() { echo -e "\r$1 "; }
think() { (( $VERBOSE )) && say "> $1"; }

# some helpers, which do most of the work

is_test_ok() {
  [[ -d $1/begin_state ]] || { say "ERROR $1 missing begin_state"; return 0; }
  [[ -d $1/end_state ]] || { say "ERROR $1 missing end_state"; return 0; }
  [[ -r $1/command ]] || { say "ERROR $1 missing command"; return 0; }
  return 1
}

run_test() {
  local START_TIME
  local STOP_TIME
  cp -r $1/begin_state $1/work
  cd $1/work
  START_TIME=`date +%s.%N`
  jStar.native $(cat ../command) > out.log 2> err.log
  STOP_TIME=`date +%s.%N`
  TIME=`echo "($STOP_TIME-$START_TIME)/0.001" | bc`ms
  think "run $1 in $TIME"
  cd - > /dev/null
}

# Removes stuff which *normally* changes.
filter_test_results() {
  local PATTERN="^Soot" # Will remove lines that match this pattern.
  local TEXT_FILES
  local TEMPORARY_FILE
  cd $1/work
  TEXT_FILES=$(find . -type f | xargs file | grep ":.*text" | sed 's/:.*//')
  TEMPORARY_FILE=$(mktemp)
  for f in $TEXT_FILES; do
    grep -v -e "$PATTERN" $f > $TEMPORARY_FILE
    cp $TEMPORARY_FILE $f
  done
  rm $TEMPORARY_FILE
  cd - > /dev/null
}

check_test_results() {
  if $(diff -ru $1/end_state $1/work > $1/diff.log 2> /dev/null); then
    let ++PASSED_COUNT
    (( $QUIET )) || say " OK $1"
  else
    say "NOK $1"; continue
  fi
}

# Parse command line arguments
while (( $# )); do
  case "$1" in
    (*\ *) say "ERROR \"$1\" has spaces"; TESTS="$TESTS ";;
    (-*) {
      case "$1" in
        -q) QUIET=1;;
        -v) VERBOSE=1;;
        -clean) CLEAN=1;;
        -help) HELP=1;;
        *) say "ERROR $1 is an unknown option"; HELP=1;;
      esac };;
    (*) 
      if [[ -d $1 ]]; then 
        TESTS="$TESTS $1"
      else 
        say "ERROR $1 is not a directory"
      fi;;
  esac
  shift
done
[ -z $TESTS ] && TESTS="$(cat alltests)"
(( ($VERBOSE && $QUIET) || $HELP )) && { cat io_test.usage; exit 0; }

CD=`pwd`
think "Running tests in $CD."
for t in $TESTS; do
  find "$t" -name diff.log -o -type d -name work | xargs rm -rf
  think "cleaned $t"
done
(( $CLEAN )) && exit 0

for t in $TESTS; do
  indicate_progress
  let ++TESTS_COUNT
  cd $CD # Shouldn't be needed; just to make sure.
  is_test_ok $t && continue
  run_test $t
  filter_test_results $t
  check_test_results $t
done

FAILED_COUNT=$(($TESTS_COUNT-$PASSED_COUNT))
think "summary: $PASSED_COUNT passed, $FAILED_COUNT failed"
echo -en "\r"
exit $FAILED_COUNT
