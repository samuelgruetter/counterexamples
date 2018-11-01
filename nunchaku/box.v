Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Strings.String. Open Scope string_scope.

Inductive Box: Type :=
| mkBox{T: Type}(x: T).

Definition l: list Box := [mkBox 1; mkBox "hello"; mkBox (2, 3)].
