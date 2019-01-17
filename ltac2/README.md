## Versions

-   Coq 449c9384f (Aug 20, 2018)
-   Ltac2 da4c15c519 (Jul 23, 2018)


## Setup

Install nix

```
git clone git@github.com:coq/coq.git
cd coq
nix-shell
```

Now we're in a "nix shell"

```
./configure -local
make -j
```

```
export PATH=PATH_TO_THE_COQ_CLONE/bin/:$PATH
```

Now for Ltac2, stay in the same nix shell:

```
cd ../
git@github.com:ppedrot/ltac2.git
cd ltac2
make
make install
```

Note that `make install` will install Ltac2 into the above local coq installation into `coq/user-contrib/Ltac2/`, because it will choose the installation destination relative to the output of `which coqtop` (or relative to `$COQBIN` if it is set).

Then, in any terminal, if you want to use this Coq version with Ltac2, do

```
export PATH=PATH_TO_THE_COQ_CLONE/bin/:$PATH
```

which is, on my machine:

```
export PATH=/home/sam/Documents/git/ltac2/coq/bin/:$PATH
```
