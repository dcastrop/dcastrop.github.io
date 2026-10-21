  knapsack_naive wvs
=e  (* unfold: the exponential specification *)
  hylo naive_alg (naive_c wvs)
=e  (* reenumerate: recurse on capacities, look results up *)
  dyna (knap_alg wvs \o look_tbl) out_int_c
=e  (* look_tbl_with: jump straight to the entry, O(1) *)
  dyna (knap_alg wvs \o look_with (w:=fast_drop) fast_drop_walk) out_int_c
=e  (* dyna_memo: build each table entry once *)
  (mhead \o l_out) \o
    hylo (memo_alg (knap_alg wvs \o look_with (w:=fast_drop) fast_drop_walk))
      out_int_c
