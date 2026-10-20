Lemma ext_inj s (k1 k2 : Pos C s -> X) : MkExt s k1 = MkExt s k2 -> k1 = k2.
Proof. intros H; injection H; intros E.
  (* E : existT _ s k1 = existT _ s k2.  Now what? *)
  apply inj_pair2 in E; exact E. Qed.
