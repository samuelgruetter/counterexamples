Conjecture restrict_spec2: forall m k ks,
    ~ contains ks k -> get (restrict m ks) k = None.
