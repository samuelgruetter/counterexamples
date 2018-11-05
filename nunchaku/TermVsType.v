Check (Type -> Type -> Type). (* Type *)
Check prod. (* Type -> Type -> Type *)
(* fully apply it, and then say that something has this as its type: *)
Compute (prod nat nat). (* (nat * nat)%type : Set *)
Check (_: nat * nat).

Check (Type -> (Type * Type)). (* Type *)
Check (fun T => (list T, T)). (* Type -> Type * Type *)
(* fully apply it, and then say that something has this as its type: *)
Compute ((fun T => (list T, T)) nat). (* (list nat, nat) : Type * Type *)
Fail Check (_: (list nat, nat)).
(* Error: The term "(list nat, nat)" has type "(Set * Set)%type"
   which should be Set, Prop or Type. *)
