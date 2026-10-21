Definition knapsack_naive wvs := hylo naive_alg (naive_c wvs).  (* exponential *)

(* Step 1: the algebra reads its subproblems through a lookup *)
Derive knap_alg_ in (forall g b, naive_alg (fmap g (naive_c wvs b))
                               = knap_alg_ (look_rec out_int_c g b))
  as knap_look.

(* Step 2: recurse on capacities; array tables with O(1) lookups *)
Derive knapsack_arr in (knapsack_naive wvs =e morph_of knapsack_arr)
  as knapsack_arr_calc.
Proof.
  unfold knapsack_naive.
  rewrite (reenumerate (U := ATab int) (alg := knap_alg) knap_look).
  rewrite (look_tbl_with fast_drop_walk).
  rewrite dyna_memo.
  finished.
Qed.
