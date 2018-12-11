#!/bin/sh

# Coq 8.8.2
opam switch smtcoq_cvc4 # also contains nunchaku opam installation
eval `opam config env`

export PATH=/home/sam/installs/Isabelle2017/contrib/cvc4-1.5-3/x86_64-linux/:$PATH

emacs --load=./nunchaku.el --load=./common.el
