Definition hylo_def (a : Alg F B) (c : Coalg F A)
  : forall (x : A), ^\hlmark{recf}{RecF c x}^ -> B :=
  fix f x H :=
    ^\hlmark{conv}{match c x as cx}^
          return (forall e : Pos F (shape cx), RecF c (cont cx e)) -> B
    with
    | MkCont sx cx =>
        fun H => a (MkCont sx (fun e => let ce := cx e in f ce (^\hlmark{He}{H e}^)))
    end (^\hlmark{inv}{RecF\_inv H}^).

Definition hylo : Alg F B ~> RCoalg F A ~> A ~> B := ...
  (* a c x |-> hylo_def a c x (terminating c x) *)
