(* initial accumulator in union nil instead of B *)
Definition union(A B: list E): list E :=
  fold_left (fun res a => if in_dec eeq a res then res else a :: res) A nil.
