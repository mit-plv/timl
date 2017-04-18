#!/usr/bin/env bash

FILE=$1.tar
git archive -o $FILE --prefix=timl/ HEAD
tar --delete -f $FILE timl/compiler
tar --delete -f $FILE timl/todo.md
tar --delete -f $FILE timl/archive.sh
gzip $FILE

