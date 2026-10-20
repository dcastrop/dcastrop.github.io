Inductive Ts L A := Leaf (l : L) | Node (a : A).        (* shapes    *)
Inductive Tp := Lbranch | Rbranch.                      (* positions *)

Definition t_dom (x : Ts L A * Tp) : bool :=
  match x with (Node _, _) => true | _ => false end.
Instance TreeF L A : Cont (Ts L A) Tp := { valid := t_dom }.
