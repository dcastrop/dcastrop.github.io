Module DecBool := DecidableEqDep(BoolEq).                  (* Hedberg *)
Definition bool_irrelevance {b1 b2 : bool} (p1 p2 : b1 = b2) : p1 = p2 :=
  DecBool.UIP b1 b2 p1 p2.

Lemma elem_val_eq (e1 e2 : Pos F s) : val e1 = val e2 -> e1 = e2.
Proof.
  destruct e1, e2; simpl; intros ->; f_equal; apply bool_irrelevance.^\tikzmark{uip}^
Qed.
