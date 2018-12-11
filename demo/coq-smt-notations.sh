#!/bin/sh

# Coq 8.8.2
opam switch 4.03.0
eval `opam config env`

emacs --load=./coq-smt-notations.el --load=./common.el
