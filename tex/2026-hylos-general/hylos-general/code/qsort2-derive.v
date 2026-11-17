Derive qsort_double
  in ^\tikzmark{specl}^(map double \o cata conquer \o ana divide =e qsort_double)^\tikzmark{spec}^
  as qsort_double_calc.
Proof.
  ^\tikzmark{lawsl}^rewrite ^\tikzmark{mfl}^map_conquer_fusion^\tikzmark{mfr}^, hylo_ana, deforest by ^\tikzmark{scl}^apply out_in^\tikzmark{scr}^.^\tikzmark{laws}^
  rewrite <- (hylo_cps_hylo _ divide_k).^\tikzmark{lawsb}^
  finished.
Qed.
