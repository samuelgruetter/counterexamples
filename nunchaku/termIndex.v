(* Note: n is a parameter, not an index *)
Inductive MemoryBank: nat -> Set :=
| Bit: bool -> MemoryBank 1
| Combine: forall n, MemoryBank n -> MemoryBank n -> MemoryBank (S n).
