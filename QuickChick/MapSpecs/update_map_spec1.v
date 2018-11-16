Conjecture update_map_spec1: forall m1 m2 k,
    get m2 k = None ->
    get (update_map m1 m2) k = get m1 k.
