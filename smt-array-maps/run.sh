#!/bin/sh

set -x

runfile () {
    cat preamble.smt2 "$1" check-sat.smt2 | z3 -in -smt2
}

runfile extends_trans.smt2
runfile mysubset.smt2
runfile goal5.smt2
