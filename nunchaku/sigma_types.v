Inductive word : nat -> Set :=
| WO : word O
| WS : bool -> forall {n : nat}, word n -> word (S n).

Fixpoint wordToNat{sz : nat}(w : word sz) : nat :=
  match w with
    | WO => O
    | WS false w' => (wordToNat w') * 2
    | WS true w' => S (wordToNat w' * 2)
  end.

Inductive sigT {A : Type} (P : A -> Type) : Type :=
    existT : forall x : A, P x -> sigT P.

Lemma existT_wordToNat:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2),
    existT word sz1 w1 = existT word sz2 w2 ->
    wordToNat w1 = wordToNat w2.
Proof.
Abort.
