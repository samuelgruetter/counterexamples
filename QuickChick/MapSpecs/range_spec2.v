Conjecture range_spec2: forall m v,
    (forall k, get m k <> Some v) -> ~ contains (range m) v.
