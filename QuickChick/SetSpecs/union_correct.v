Definition union(A B: list E): list E :=
  (*! *)
  fold_left (fun res a => if in_dec eeq a res then res else a :: res) A B
  (*!! initial accumulator in union nil instead of B *)
  (*! fold_left (fun res a => if in_dec eeq a res then res else a :: res) A nil *)
  (*!! then/else branch swapped in union *)
  (*! fold_left (fun res a => if in_dec eeq a res then a :: res else res) A B *)
.
