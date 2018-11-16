Conjecture reverse_spec1: forall m k v,
    reverse_get m v = Some k -> get m k = Some v.
