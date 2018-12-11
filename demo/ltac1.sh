#!/bin/sh

# Coq 8.8.2
opam switch 4.03.0
eval `opam config env`

emacs --load=./ltac1.el --load=./common.el
