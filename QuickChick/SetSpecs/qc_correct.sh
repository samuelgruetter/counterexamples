#!/bin/sh

for f in *_correct.v; do
    op=`echo "$f" | sed -e 's/_correct.v//g'`
    query="Load SetPreamble. Load ${op}_correct. Load ${op}_spec. QuickChick ${op}_spec."
    echo "---Input---"
    echo "$query"
    echo "---Output---"
    echo "$query" | coqtop
done
