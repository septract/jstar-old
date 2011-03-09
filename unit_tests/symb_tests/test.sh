#!/bin/bash

for file in `ls *_test | sed "s/_test//"` 
do 
  ( ulimit -t 2; $JSTAR_HOME/bin/test_symb  -f $file\_test -l $file\_logic -a $file\_abs )
done
