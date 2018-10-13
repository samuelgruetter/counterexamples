## Questions

-    https://github.com/smtcoq/smtcoq/issues/13

## Used software versions

-    OCaml 4.04.0
-    Coq 8.6.1
-    SMTCoq version: commit 5cf9c7774c95a6d4c538f0a558471b2adc401699 (current HEAD of lfsc branch, Oct 13 2018)
-    CVC4 version 1.7-prerelease [git master 9168f325]
-    veriT 9f48a98


## Installation notes

```
export COQBIN=/home/sam/.opam/smtcoq_src_opamcoq/bin/
./configure.sh
make
make install
```


## Setup notes

Open `source_setup.sh`, adapt absolute paths, then run `source source_setup.sh`.
