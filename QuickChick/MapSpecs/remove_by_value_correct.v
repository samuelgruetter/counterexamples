Definition remove_by_value(M: map K V)(v: V): map K V :=
  remove_keys M (preimage M (singleton_set v)).
