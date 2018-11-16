Conjecture put_spec2: forall (m: map K V) (k1 k2: K) (v: V),
    k1 <> k2 -> get (put m k1 v) k2 = get m k2.
