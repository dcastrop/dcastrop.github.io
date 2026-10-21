Instance Memo : Cont (A * Sg) Pg := ...                (* Memo X = A * G X *)

Definition dyna `{!Initial (Memo G A) T}
  (a : App G T ~> A) (c : RCoalg G B) : B ~> A
  := mhead \o l_out \o hylo (l_in \o mcons \o pair a id) c.

Theorem dyna_iso : dyna a c =e dyna (a \o fmap (iso U T)) c.  (* any table *)

Instance ATab_initial : Initial (Memo NatF A) (ATab A).    (* arrays *)
