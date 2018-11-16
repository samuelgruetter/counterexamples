#!/bin/sh

for f in *_correct.v; do
    op=`echo "$f" | sed -e 's/_correct.v//g'`
    for g in ${op}_wrong*.v; do
	wrong_def=`echo "$g" | sed -e 's/\.v//g'`
	query="Load SetPreamble. Load ${wrong_def}. Load ${op}_spec. QuickChick ${op}_spec."
	echo "---Input---"
	echo "$query"
	echo "---Output---"
	echo "$query" | coqtop
    done
done
