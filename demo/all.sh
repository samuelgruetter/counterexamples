#!/bin/sh

# launches next only once previous is closed
# except

~/installs/Isabelle2017/Isabelle2017 &

./isabelle.sh

./QuickChick.sh

./coq-smt-notations.sh
./dafny.sh
./SMTCoq.sh
./coqhammer.sh

./ltac1.sh
./nunchaku.sh
