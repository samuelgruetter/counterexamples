Conjecture reverse_get_spec2: forall m v,
    reverse_get m v = None -> forall k, get m k <> Some v.
