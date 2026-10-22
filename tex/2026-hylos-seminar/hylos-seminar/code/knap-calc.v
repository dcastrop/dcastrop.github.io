Definition knapsack_naive wvs := hylo naive_alg (naive_c wvs).  (* exponential *)

(* Step 1: the algebra reads its subproblems from the table *)
Derive knap_alg_ in (forall g b, naive_alg (fmap g (naive_c wvs b))
                               = knap_alg_ (look_rec out_int_c g b))
  as knap_look.

(* Step 2: the loop's step, from the table *)
Derive knap_step in (knap_alg \o look_with fast_drop_walk \o nat_next
                     =e knap_step) as knap_step_calc.
Proof. finished. Qed.
