Derive qsort_times_two
  in (Lmap times_two \o cata merge \o rana tsplit =e morph_of qsort_times_two)
  as qsort_times_two_calc.
Proof.
  rewrite map_merge_fusion, hylo_ana, deforest by apply l_out_in.
  rewrite <- (hylo_cps_hylo _ tsplit_k).
  finished.
Qed.
