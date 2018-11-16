Conjecture diff_spec: forall (x: E) (A B: set E),
    contains (diff A B) x <-> contains A x /\ ~ contains B x.
