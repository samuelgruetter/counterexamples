(* then/else branch swapped *)
Definition intersect(A B: list E): list E :=
  fold_left (fun res a => if in_dec eeq a B then res else a :: res) A nil.
