Derive qsort_times_two
  in (Lmap times_two \o cata merge \o rana tsplit =e qsort_times_two)^\tikzmark{spec}^
  as calc.
Proof.
  rewrite map_merge_fusion, hylo_ana, deforest by apply l_out_in.^\tikzmark{laws}^
  finished.
Qed.
