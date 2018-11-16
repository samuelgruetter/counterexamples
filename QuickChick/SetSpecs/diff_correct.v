Definition diff(A B: list E): list E :=
  fold_left (fun res b => remove eeq b res) B A.
