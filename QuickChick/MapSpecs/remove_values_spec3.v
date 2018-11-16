Conjecture remove_values_spec3: forall m k v vs,
    get m k = Some v ->
    ~ contains vs v ->
    get (remove_values m vs) k = Some v.
