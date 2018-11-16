Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

From QuickChick Require Import QuickChick.

(* should be in QuickChick library: *)
Global Instance Dec_iff {P Q} {H : Dec P} {I : Dec Q} : Dec (P <-> Q).
Proof.
  constructor. unfold ssrbool.decidable.
  destruct H as [D]; destruct D;
    destruct I as [D]; destruct D; intuition auto.
Defined.


(** List Sets *)

(* this would normally be kept abstract as a section variable,
   but for testing, we make it concrete *)
Definition E := nat.
Definition eeq: forall (e1 e2: E), {e1 = e2} + {e1 <> e2} := Nat.eq_dec.

Definition set: Type -> Type := list.

Definition contains(A: set E)(e: E): Prop := List.In e A.




(*
Definition range(M: map K V): set V :=
  (*! *)
  snd (domain_and_range M)
  (*!! range returning values of shadowed keys *)
  (*! List.map snd M *)
  (*!! range copy pasted body of domain *)
  (*! List.map fst M *)
.

Definition reverse_get(M: map K V)(v: V): option K :=
  (*! *)
  snd (fold_left (fun '(seen_keys, res) '(ki, vi) =>
                    if in_dec keq ki seen_keys then (seen_keys, res)
                    else (ki :: seen_keys, if veq vi v then Some ki else res))
                 M (empty_set, None))
  (*!! reverse_get returning values of shadowed keys *)
  (*! match find (fun '(ki, vi) => if veq vi v then true else false) M with
     | Some (k, _) => Some k
     | None => None
     end *)
.

Definition intersect_map(M1 M2: map K V): map K V :=
  (*! *)
  filter (fun '(k1, v1) => match get M1 k1, get M2 k1 with
                           | Some v1', Some v2 => if veq v1' v1
                                                  then if veq v1 v2 then true else false
                                                  else false
                           | _, _ => false
                           end) M1
  (*!! intersect_map containing shadowed keys v2 *)
  (*! filter (fun '(k1, v1) => match get M2 k1 with
                           | Some v2 => if veq v1 v2 then true else false
                           | None => false
                           end) M1 *)
  (*!! intersect_map containing shadowed keys v1 *)
  (*! fold_left (fun res a => if in_dec tupleeq a M2 then a :: res else res)
      M1 nil *)
.

Definition preimage(M: map K V)(vs: set V): set K :=
  filter (fun ki => match get M ki with
                    | Some vi => if in_dec veq vi vs then true else false
                    | None => false
                    end)
         (domain M).

Definition remove_keys(M: map K V)(ks: set K): map K V :=
  filter (fun '(ki, vi) => if in_dec keq ki ks then false else true) M.

Definition remove_by_value(M: map K V)(v: V): map K V :=
  (*! *)
  remove_keys M (preimage M (singleton_set v))
  (*!! remove_by_value reactivates a shadowed key *)
  (*! filter (fun '(ki, vi) => if veq vi v then false else true) M *)
.

Definition remove_values(M: map K V)(vs: set V): map K V :=
  (*! *)
  remove_keys M (preimage M vs)
  (*!! remove_values might reactivate a shadowed key *)
  (*! filter (fun '(ki, vi) => if in_dec veq vi vs then false else true) M *)
.

Definition update_map(M1 M2: map K V): map K V :=
  (*! *)
  (filter (fun '(k1, v1) =>
             if (find (fun '(k2, v2) => if keq k1 k2 then true else false) M2)
             then false else true) M1) ++ M2
  (*!! update_map with then/else switched *)
  (*! (filter (fun '(k1, v1) =>
             if (find (fun '(k2, v2) => if keq k1 k2 then false else true) M2)
             then false else true) M1) ++ M2 *)
.
*)