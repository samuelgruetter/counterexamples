(* intersect_map containing shadowed keys version 2 *)
Definition intersect_map(M1 M2: map K V): map K V :=
  fold_left (fun res a => if in_dec tupleeq a M2 then a :: res else res) M1 nil.
