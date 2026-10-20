Definition knapsack_alg wvs (x : App NatF (Table NatF int)) : int :=
  match x with
  | MkCont (inl tt) _ => 0                                       (* K(0) *)
  | MkCont (inr tt) k => max_int 0 (memo_knapsack (k next) wvs)
  end.        (* memo_knapsack: u + v for each (w, v) with K(c - w) = u *)

Definition knapsack wvs := dyna (knapsack_alg wvs) out_int_c.
