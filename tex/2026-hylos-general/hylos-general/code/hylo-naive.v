Fixpoint hylo {F : Type -> Type} {A B : Type}
    (fmap : forall X Y, (X -> Y) -> F X -> F Y)
    (conquer : F B -> B) (divide : A -> F A) (x : A) : B :=
  conquer (fmap A B (hylo fmap conquer divide) (divide x)).
