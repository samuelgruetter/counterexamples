(setq frame-title-format "SMTCoq")
(find-file "../SMTCoq/MyExample.v")
(end-of-buffer)
(ignore-errors (company-coq-proof-goto-point))
(ignore-errors (company-coq-proof-goto-point))
