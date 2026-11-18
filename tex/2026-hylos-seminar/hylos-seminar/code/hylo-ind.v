Lemma hylo_ind (P : A -> B -> Prop) (a : Alg F B) (c : RCoalg F A)
  : (forall x, (forall e, P (cont (c x) e) (hylo a c (cont (c x) e))) ->
        P x (hylo a c x)) ->
    forall x, P x (hylo a c x).
Proof. intros H x; induction (recP c x) as [x _ Ih]; apply H, Ih. Qed.

Lemma hylo_correct : forall l : list int,
  Sorted leb (hylo merge tsplit l) /\ Permutation l (hylo merge tsplit l).
Proof.
  intros l; induction (recP tsplit l) as [x _ Ih]; rewrite hylo_unr.
  ...
