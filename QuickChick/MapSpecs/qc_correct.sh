#!/bin/sh

for f in *_correct.v; do
    op=`echo "$f" | sed -e 's/_correct.v//g'`
    for g in ${op}_spec*.v; do
	spec_name=`echo "$g" | sed -e 's/\.v//g'`
	query="Load MapPreamble. Load ${op}_correct. Load ${spec_name}. QuickChick ${spec_name}."
	echo "---Input---"
	echo "$query"
	echo "---Output---"
	echo "$query" | coqtop
    done
done
