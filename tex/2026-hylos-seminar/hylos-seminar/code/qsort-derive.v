Derive qsort in (cata merge \o rana tsplit =e morph_of qsort) as qsort_calc.
Proof.
  rewrite cata_ana_hylo, <- (hylo_cps_hylo merge tsplit_k).
  finished.
Qed.
