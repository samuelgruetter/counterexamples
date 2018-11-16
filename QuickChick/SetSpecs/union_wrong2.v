(* then/else branch swapped *)
Definition union(A B: list E): list E :=
  fold_left (fun res a => if in_dec eeq a res then a :: res else res) A B.
