#!/bin/sh

opam switch qc
eval `opam config env`

emacs --load=./QuickChick.el --load=./common.el
