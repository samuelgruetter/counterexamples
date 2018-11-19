#!/bin/sh

for f in *_correct.v; do
    op=`echo "$f" | sed -e 's/_correct.v//g'`
    for g in ${op}_spec*.v; do
	spec_name=`echo "$g" | sed -e 's/\.v//g'`
	for h in ${op}_wrong*.v; do
	    wrong_name=`echo "$h" | sed -e 's/\.v//g'`
	    query="Load MapPreamble. Load ${wrong_name}. Load ${spec_name}. QuickChick ${spec_name}."
	    echo "---Input---"
	    echo "$query"
	    echo "---Output---"
	    echo "$query" | coqtop
	done
    done
done
