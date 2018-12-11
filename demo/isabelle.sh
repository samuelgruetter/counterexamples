#!/bin/sh

# Coq 8.8.2
opam switch 4.03.0
eval `opam config env`

emacs --load=./isabelle.el --load=./common.el
