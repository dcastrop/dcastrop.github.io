Definition rana (c : RCoalg F A) : A ~> LFix F := hylo l_in c.

Corollary cata_ana_hylo : cata a \o rana c =e hylo a c.
