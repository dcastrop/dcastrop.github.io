  knapsack_naive wvs
=e  (* unfold: the exponential specification *)
  hylo naive_alg (naive_c wvs)
=e  (* reenumerate: recurse on capacities, look results up in O(1) *)
  dyna (knap_alg wvs \o look_with (w:=fast_drop) fast_drop_walk) out_int_c
=e  (* dyna_loop: the table of a count-down is built by a loop *)
  (mhead \o l_out) \o
    (morphism fun n : int =>
       loop n (fun _ : int => memo_step (knap_step wvs))
         (0%uint63, memo_base 0%uint63))
