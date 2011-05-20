#!/bin/bash
if [ -z "$TIMELIMIT" ]; then
  TIMELIMIT=5
fi
echo -n .
( ulimit -t $TIMELIMIT; "$1/bin/jstar" -v -f $2.jimple ) 2> /dev/null
EC=$?
case $EC in
  137)
    echo
    echo "Time limit (${TIMELIMIT}s) exceeded. Try"
    echo "  TIMELIMIT=${TIMELIMIT}0 make test"
    echo "(or some other number >$TIMELIMIT)."
    ;;
  0)
    ;;
  *)
    echo 
    echo "Failed $2 in $(pwd) (errorcode $EC)"
    ;;
esac

