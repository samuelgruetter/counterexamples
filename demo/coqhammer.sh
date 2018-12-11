#!/bin/sh

opam switch coqhammer
eval `opam config env`

export PATH=/home/sam/installs/Eprover/E/PROVER/:$PATH
export LD_LIBRARY_PATH=/home/sam/Documents/git/clones/z3/build:$LD_LIBRARY_PATH
export PATH=/home/sam/Documents/git/clones/z3/build:$PATH

emacs --load=./coqhammer.el --load=./common.el
