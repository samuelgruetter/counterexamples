Fail Inductive context: Type :=
| Empty: context
| Ext(G: context)(t: type G): context
(* Inductive-Inductive types: constructor of one type appears in index of other
   inductive type being defined at the same time.
   This definition cannot be made in Coq. *)
with type: context -> Type :=
| Unit(G: context): type G
| Sigma(G: context)(A: type G)(B: type (Ext G A)): type G.
