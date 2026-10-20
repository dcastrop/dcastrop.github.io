Instance Memo : Cont (A * Sg) Pg := ...            (* Memo X = A * G X *)
Definition Table := LFix Memo.

Definition dyna (a : App C (Table C A) ~> A) (c : RCoalg C B) : B ~> A
  := headT \o hylo (l_in \o Cons \o pair a id) c.
