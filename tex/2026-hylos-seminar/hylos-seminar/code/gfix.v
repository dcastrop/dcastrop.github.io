CoInductive GFix F := GFix_in { GFix_out : App F (GFix F) }.
Definition GFixR : GFix F -> GFix F -> Prop := paco2 GFixR_ bot2.

Lemma gfix_ana_univ : f =e gfix_ana h <-> f =e gfix_in \o fmap f \o h.

Definition FinF : GFix F -> Prop := RecF g_out.          (* finite *)
Corollary ana_rec_term : (forall x, FinF (ana h x)) <-> RecP h.

Lemma rana_ana : ana (T := GFix F) f =e ana l_out \o rana f.
