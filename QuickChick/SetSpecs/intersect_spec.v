Conjecture intersect_spec: forall (x: E) (A B: set E),
    contains (intersect A B) x <-> contains A x /\ contains B x.
