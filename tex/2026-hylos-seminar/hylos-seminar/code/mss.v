Definition mss := maximum \o lmap sum \o segs \o lmap some_m.

Derive mss_linear in (mss =e morph_of mss_linear) as mss_calc.
Proof.
  unfold mss, segs.
  arewrite (map_promotion sum).
  arewrite (reduce_promotion max_monoid).
  arewrite (lmap_comp maximum (lmap sum)).
  arewrite (lmap_comp (maximum \o lmap sum) inits).
  rewrite horner_mss.                          (* max-plus semiring *)
  arewrite (scan_lemma odot (Some 0)).
  arewrite (scan_tupling max_monoid odot (Some 0)).
  arewrite (foldr_lmap (tup_step max_monoid odot) some_m (Some 0, Some 0)).
  finished.
Qed.
