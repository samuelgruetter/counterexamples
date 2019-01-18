#!/bin/sh

# needs up to ~7GB of RAM

./isabelle.sh &

sleep 2

~/installs/Isabelle2017/Isabelle2017 ../isabelle/MapTests.thy +line:86 &

sleep 2

./QuickChick.sh &

sleep 2

./coq-smt-notations.sh &

sleep 2

./dafny.sh &

sleep 2

./SMTCoq.sh &

sleep 2

./coqhammer.sh &

sleep 2

./ltac1.sh &

sleep 2

./nunchaku.sh &
