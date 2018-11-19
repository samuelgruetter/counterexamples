Definition remove_values(M: map K V)(vs: set V): map K V :=
  remove_keys M (preimage M vs).
