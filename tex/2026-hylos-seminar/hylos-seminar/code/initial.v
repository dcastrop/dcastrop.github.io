Class Initial F T `{setoid T} :=
  { l_in  : App F T ~> T;
    l_out : RCoalg F T;                      (* a recursive coalgebra *)
    l_in_out : l_in \o l_out =e id;
    l_out_in : l_out \o l_in =e id }.

Definition cata (g : Alg F A) : T ~> A := hylo g l_out.
Definition rana (h : RCoalg F A) : A ~> T := hylo l_in h.

Lemma cata_univ : f =e cata g <-> f =e g \o fmap f \o l_out.
Corollary cata_ana_hylo : cata g \o rana h =e hylo g h.
