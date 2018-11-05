Goal ~ (forall (t: Type), exists (a: t), a = a).
  intro C.
  specialize (C Empty_set).
  destruct C as [a C].
  destruct a.
Qed.
