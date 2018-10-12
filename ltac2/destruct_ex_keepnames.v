Require Import Ltac2.Ltac2.


(* "destruct h as [x y]"
destruct2 : ident -> ident -> ident -> unit
*)
Ltac2 destruct2 h x y :=
  let use := fun _ => None in
  let ic := [{
    Std.indcl_arg := Std.ElimOnIdent h;
    Std.indcl_eqn := None;
    Std.indcl_as  := Some (Std.IntroOrPattern
              [[Std.IntroNaming (Std.IntroIdentifier x);
                Std.IntroNaming (Std.IntroIdentifier y)]]);
    Std.indcl_in := None
  }] in
  destruct0 false ic use.

Ltac2 rec map f l :=
  match l with
  | h :: t => f h :: map f t
  | [] => []
  end.

Ltac2 hypnames () :=
  map (fun e => match e with (n, _, _) => n end) (Control.hyps()).

Ltac2 myfresh basename :=
  Fresh.fresh (Fresh.Free.of_ids (hypnames ())) basename.

Fail Ltac2 destruct_ex_keepnames () :=
  repeat (match! goal with
          | [ h: exists x, _ |- ?g ] =>
            let x' := myfresh x in
            destruct2 h x' h
         end).
(*
The command has indeed failed with message:
         Unbound value x
*)

Ltac2 destruct_ex_keepnames () :=
  repeat (match! goal with
          | [ h: exists x, _ |- ?g ] =>
            let x' := myfresh @x in
            destruct2 h x' h
         end).

Goal forall (a: nat),
    (exists b, a = 2 * b) ->
    (exists b, a = 3 * b) ->
    (exists b, a = 6 * b).
Proof.
  intros a D2 D3.
  destruct_ex_keepnames ().
(*
  a, x0 : nat
  D2 : a = 2 * x0
  x : nat
  D3 : a = 3 * x
  ============================
  exists b : nat, a = 6 * b
 *)
