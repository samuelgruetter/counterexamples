Conjecture union_spec: forall (x: E) (A B: set E),
    contains (union A B) x <-> contains A x \/ contains B x.
