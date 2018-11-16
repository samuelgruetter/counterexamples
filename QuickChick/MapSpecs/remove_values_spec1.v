Conjecture remove_values_spec1: forall m k vs,
    get m k = None ->
    get (remove_values m vs) k = None.
