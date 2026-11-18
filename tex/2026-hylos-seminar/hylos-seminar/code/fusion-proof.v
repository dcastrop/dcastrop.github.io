Lemma hylo_fusion_l (E : h \o a =e b \o fmap h)
  : h \o hylo a c =e hylo b c.
Proof.
  rewrite hylo_uniq, fmap_comp.
  arewrite <- E; arewrite <- (hylo_unr a c).
  reflexivity.
Qed.
