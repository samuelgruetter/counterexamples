## Versions

Using my opam switch `smtcoq_cvc4` with

-    OCaml 4.03.0
-    coq 8.6.1
-    smbc 0.4.2
-    cvc4 1.5 (shipped with Isabelle 2017)
-    nunchaku 0.5.1 70e5101
-    nunchaku-coq master (cb96ecad3b4ddf8ae0cbc486e7e38a230ee77e14, Jun 26 2017)


## Setup


for CVC4:

```
export PATH=/home/sam/installs/Isabelle2017/contrib/cvc4-1.5-3/x86_64-linux/:$PATH
```

Note: CVC4 version 1.7-prerelease [git master 9168f325] [does not work](https://github.com/nunchaku-inria/nunchaku/issues/27).


## Emacs

`M-x` `eval-expression`

```
(global-set-key (kbd "<f8>") (lambda () (interactive) (save-buffer) (shell-command (concat "nunchaku " (buffer-file-name)) "*nunchaku stdout*" "*nunchaku stderr*")))
```

or better:

```
(global-set-key (kbd "<f8>") (lambda () (interactive) (save-buffer) (set (make-local-variable 'compile-command) (concat "nunchaku -nc " (buffer-file-name))) (recompile)))
```
