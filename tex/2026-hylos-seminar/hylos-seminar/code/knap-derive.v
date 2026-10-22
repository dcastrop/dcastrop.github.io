Derive knapsack_arr in (knapsack_naive wvs =e morph_of knapsack_arr)
  as knapsack_arr_calc.
Proof.
  unfold knapsack_naive.
  (* Memoise: the subproblems are read from a table *)
  erewrite reenumerate.
  (* The table of a count-down is built by a loop *)
  erewrite dyna_loop.
  (* The loop's step, its first entry, and the algebra on the table *)
  2: exact knap_step_calc.
  2: exact knap_base.
  2: exact knap_look.
  finished.
Qed.
