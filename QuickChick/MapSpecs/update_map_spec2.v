Conjecture update_map_spec2: forall m1 m2 k v,
    get m2 k = Some v ->
    get (update_map m1 m2) k = Some v.

