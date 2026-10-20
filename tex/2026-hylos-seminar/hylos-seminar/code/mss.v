Definition mss := maximum \o lmap sum \o segs \o lmap some_m.

Derive mss_linear in (mss =e mss_linear) as mss_calc.
Proof.
  unfold mss, segs.
  arewrite (map_promotion sum).
  arewrite (reduce_promotion max_monoid).
  ...                                          (* lmap_comp, twice *)
  rewrite horner_mss.                          (* max-plus semiring *)
  arewrite (scan_lemma odot (Some 0)).
  ...                                          (* tupling *)
  finished.
Qed.
