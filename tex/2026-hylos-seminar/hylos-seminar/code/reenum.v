Theorem reenumerate (an : App F A ~> A) (cn : RCoalg F B)
  (e : RCoalg NatF B) (alg : (int -> option A) ~> A)
  (Hlook : forall (g : B ~> A) b,
      an (fmap g (cn b)) =e alg (look_rec e g b))
  : hylo an cn =e dyna (alg \o look_with) e.
