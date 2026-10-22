Derive qsort_times_two
  in ^\tikzmark{specl}^(Lmap times_two \o cata merge \o rana tsplit =e morph_of qsort_times_two)^\tikzmark{spec}^
  as qsort_times_two_calc.
Proof.
  ^\tikzmark{lawsl}^rewrite map_merge_fusion, hylo_ana, deforest by apply l_out_in.^\tikzmark{laws}^
  rewrite <- (hylo_cps_hylo _ tsplit_k).^\tikzmark{lawsb}^
  finished.
Qed.
