#!/bin/bash
PROGRAM="jstar"
COPY="\
     configure \
     COPYRIGHT \
     corestar_src \
     library \
     LICENSE.txt \
     README \
     src \
     unit_tests \
     "

log () {
  echo "$1"
}

usage () {
  echo "make_release.sh <root> [<version>]"
  exit 1
}

try () {
  "$@"
  if (( $? )); then
    echo "Failed: $*" > /dev/stderr
    exit 2
  fi
}

HERE="$(pwd)"
VERSION="$(date +%Y%m)"
if (( $# < 1 )); then usage; fi
ROOT="$1"
if (( $# == 2 )); then VERSION="$2"; fi
log "HERE=$HERE; ROOT=$ROOT; VERSION=$VERSION"

DIR="$PROGRAM-$VERSION"
TAR="$DIR.tar.bz2"
log "DIR=$DIR; TAR=$TAR"

mkdir -p "$DIR"
rm -rf "$DIR/*"

cd "$ROOT"
try make clean
try make corestar_src
for f in $COPY; do cp -L -r "$f" "$HERE/$DIR"; done
grep -v -e "\<DEV\>" Makefile > "$HERE/$DIR/Makefile"
try make doc
mkdir -p "$HERE/$DIR/doc"
try cp doc/tutorial/jstartut.pdf "$HERE/$DIR/doc/tutorial.pdf"
mkdir -p "$HERE/$DIR/bin"

cd "$HERE"
rm -f "$TAR"
tar caf "$TAR" "$DIR"

rm -rf "$DIR"
