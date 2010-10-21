#!/bin/bash
if (( $# != 1 )); then echo "Usage: $0 <testdir>"; exit 1; fi
rm -rf $1/end_state
mv $1/work $1/end_state
