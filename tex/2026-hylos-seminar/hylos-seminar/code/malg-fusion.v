Lemma malg_fusion (Hh : MonoidHom M N h)
  : h \o hylo (malg F M leaf) c =e hylo (malg F N (omap h \o leaf)) c.
Proof. apply hylo_fusion_l, malg_hom. Qed.
