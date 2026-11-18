#[mode = "!"]                                (* never search setoid ?A *)
Class setoid A := MkSetoid
  { eqRel : A -> A -> Prop;                  (* x =e y *)
    e_refl : ...; e_sym : ...; e_trans : ... }.

Structure morph `{setoid A} `{setoid B} := MkMorph       (* A ~> B *)
  { app :> A -> B;
    app_eq : forall x y, x =e y -> app x =e app y }.

Inductive AppR `{setoid X} (x y : App F X) : Prop :=    (* x =e y *)
| AppR_ext (Es : shape x =e shape y)
    (Ek : forall e1 e2, val e1 = val e2 -> cont x e1 =e cont y e2).
