Definition hylo_def (a : Alg F B) (c : Coalg F A)
  : forall (x : A), ^\hlmark{recf}{RecF c x}^ -> B :=
  fix f x H :=
    match c x with
    | MkCont sx cx => a (MkCont sx (fun e => f (cx e) (^\hlmark{He}{RecF\_inv H e}^)))
    end.
