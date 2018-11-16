Conjecture put_spec1: forall (m: map K V) (k: K) (v: V),
    get (put m k v) k = Some v.
