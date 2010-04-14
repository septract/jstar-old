#!/bin/bash
svn copy trunk@HEAD releases/ && \
svn move releases/trunk releases/$1 && \
for i in `ls releases/$1/src/*/*.ml*`; do 
  COPYRIGHT=`svn propget Copyright $i | tr '\n' '±'`
  LICENSE=`cat releases/$1/LICENSE.txt | tr '\n' '±' | tr '/' '§' `
  DATE=`date "+DATE: %Y-%m-%d"`
  cat $i | sed "s/\\\$Copyright\\\$/$COPYRIGHT/" \
      | sed "s/   jStar is distributed under a BSD license,  see,/$LICENSE/" \
      | sed "s/      LICENSE.txt//" \
      | sed "s/\\\$Release\\\$/$1 ($DATE)/" \
      | tr "±" "\n"  | tr '§' '/' > $i.tmp;
  mv $i.tmp $i
done;
cd releases
 cp -r $1 jstar
 rm -rf `find jstar -name ".svn"`
 rm $1/wishlist
 svn --force remove $1/wishlist
 cp -r $1/doc/tutorial/jstartut.pdf $1/tutorial.pdf
 rm -rf $1/doc/tutorial
 svn --force remove $1/doc/tutorial
 zip -r jstar-$1.zip jstar 
 rm -rf jstar
cd ..