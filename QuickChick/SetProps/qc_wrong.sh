#!/bin/sh

for f in query*.v; do
    name=`echo "$f" | sed -e 's/\.v//g'`
    query="Load SetLib. Load ${name}. QuickChick ${name}."
    echo "---Input---"
    echo "$query"
    echo "---Output---"
    echo "$query" | coqtop
done
