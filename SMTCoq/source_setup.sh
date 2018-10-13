# to be run with "source" in bash

export PATH=/home/sam/installs/smtcoq2/veriT9f48a98/:$PATH
export LD_LIBRARY_PATH=/home/sam/installs/smtcoq3cvc/cvc4install/lib/:$LD_LIBRARY_PATH
export PATH=/home/sam/installs/smtcoq3cvc/cvc4install/bin/:$PATH

opam switch smtcoq_src_opamcoq

eval `opam config env`
