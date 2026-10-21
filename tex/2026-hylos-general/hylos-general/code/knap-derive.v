Derive knapsack_arr in (knapsack_naive wvs =e morph_of knapsack_arr)
  as knapsack_arr_calc.
Proof.
  unfold knapsack_naive.
  rewrite (reenumerate (U := ATab int) (alg := knap_alg) knap_look).
  rewrite (look_tbl_with fast_drop_walk).
  rewrite dyna_memo.
  finished.
Qed.
