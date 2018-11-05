Inductive Expr: Set :=
| Cst(x: nat)
| Pair(e1 e2: Expr)
| Fst(e: Expr)
| Snd(e: Expr).

Inductive Interp: forall T: Type, Expr -> T -> Prop :=
| InterpCst: forall x,
    Interp nat (Cst x) x
| InterpPair: forall T1 T2 (e1 e2: Expr) e1' e2 e2',
    Interp T1 e1 e1' ->
    Interp T2 e2 e2' ->
    Interp (T1 * T2) (Pair e1 e2) (e1', e2')
| InterpFst: forall T1 T2 e e1' e2',
    Interp (T1 * T2) e (e1', e2') ->
    Interp T1 (Fst e) e1'
| InterpSnd: forall T1 T2 e e1' e2',
    Interp (T1 * T2) e (e1', e2') ->
    Interp T2 (Snd e) e2'.

Example e := (Fst (Snd (Pair (Pair (Cst 3) (Cst 4)) (Pair (Pair (Cst 5) (Cst 6)) (Cst 7))))).

Goal Interp (nat * nat) e (5, 6).
  repeat econstructor.
Qed.
