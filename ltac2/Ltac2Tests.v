Require Import Coq.ZArith.ZArith.
Require Import Ltac2.Ltac2.


Ltac2 foo () := Message.print (Message.of_string "Hello world!").

Goal False.
  foo ().
Abort.

Ltac2 Eval foo ().

Ltac2 Eval [ 10; Int.add 5 6 ].

Ltac2 Type Address := {
  name: string;
  street: string;
  city: string;
}.

Ltac2 Eval
      let a := { name := "Joe Doe"; street := "42 Main St"; city := "Springfield" } in
      let l := [ a; a ] in
      match l with
      | h :: t => Message.print (Message.of_string (h.(street)))
      | _ => Control.throw (Tactic_failure (Some (Message.of_string "whoops")))
      end.

Goal 2 = 3.
  match! goal with
  | [ |- ?a = ?b ] => Message.print (Message.of_constr a); Message.print (Message.of_constr b)
  end.
Abort.

(* this has to be a thunk, because creating the constr (which involves typechecking it)
   is a runtime action, so the right-hand side is not a syntactic value *)
Ltac2 sample_nats () := [ constr:(0); constr:(1); constr:(2) ].

Ltac2 rec type_list l :=
  match l with
  | h :: t => (Constr.type h) :: (type_list t)
  | [] => []
  end.

Ltac2 Eval type_list (sample_nats ()).

Ltac2 Eval sample_nats ().

Ltac2 rec concat_many msgs :=
  match msgs with
  | m :: rest => Message.concat m (concat_many rest)
  | [] => Message.of_string ""
  end.

Ltac2 log msgs :=
  Message.print (concat_many msgs).

Ltac2 Eval log [ Message.of_string "hello"; Message.of_string " world" ].


Goal exists (a: nat), a = 2.
  match! goal with
  | [ |- exists (y: ?t), _ ] => Message.print (Message.of_constr t)
  end.

  Fail lazy_match! goal with
  | [ |- exists (y: ?t), _ ] => Message.print (Message.of_ident y)
  end.
  (* The command has indeed failed with message:
         Unbound value y *)
Abort.

(* stack: list of list of constr to backtrack for exists-instantiation *)
Ltac2 rec go stack :=
  lazy_match! goal with
  | [ |- exists (y: ?t), _ ] =>
    lazy_match! t with
    | nat => match stack with
             | h :: t => match h with
                         | x :: xs =>
                           log [ Message.of_string "Trying ";
                                 Message.of_string "varnameIcannotPrint";
                                 Message.of_string " = ";
                                 Message.of_constr x ];
                           exists $x; go ((sample_nats ()) :: xs :: t)
                         | [] => ()
                         end
             | _ => ()
             end
    | _ => Control.throw (Tactic_failure (Some
              (Message.concat (Message.of_string "Cannot sample ")
                              (Message.of_constr t))))
    end
  | [ |- ?g ] => () (*Message.print (Message.of_constr g)*)
  end.


Goal exists a b, 2 * a = b.
  go [sample_nats ()].
Abort.

Goal 2 = 3.
  lazy_match! goal with
  | [ |- 2 = 3 ] => fail
  | [ |- 2 = _ ] => Message.print (Message.of_string "should not be printed")
  end.
Abort.

Ltac2 rec inst indent toTry :=
  lazy_match! goal with
    | [ |- _ = _ ] => reflexivity
    | [ |- _ ] =>
      match toTry with
      | x :: xs =>
        log [ indent;
                Message.of_string "Trying ";
                Message.of_string "varnameIcannotPrint";
                Message.of_string " = ";
                Message.of_constr x ];
        let moreIndent := Message.concat indent (Message.of_string "  ") in
        Control.plus
          (fun _ => exists $x; inst moreIndent (sample_nats ()))
          (fun e => inst indent xs)
      | [] => fail
      end
  end.

Goal exists a b, 2 * a = b + 1.
  inst (Message.of_string "") (sample_nats ()).
Qed.
