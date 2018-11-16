Conjecture remove_by_value_spec1: forall k v m,
    get m k = Some v -> get (remove_by_value m v) k = None.
