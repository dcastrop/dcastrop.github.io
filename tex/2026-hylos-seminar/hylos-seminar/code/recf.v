Inductive RecF (c : Coalg F A) : A -> Prop :=
| RecF_fold x : (forall e, RecF c (cont (c x) e)) -> RecF c x.

Structure RCoalg F A :=
  Rec { coalg :> Coalg F A; recP : forall x, RecF coalg x }.
