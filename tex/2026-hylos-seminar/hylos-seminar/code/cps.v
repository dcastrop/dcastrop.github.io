Record CCoalg (c : RCoalg F A) := MkCCoalg
  { ccoalg : forall R (x : A), (forall y, y = c x -> R) -> R;
    ccoalg_law : forall R x k, ccoalg R x k = k (c x) eq_refl }.

Definition hylo_cps_def (a : Alg F B) (cc : CCoalg c)
  : forall x, RecF c x -> B :=
  fix f x H := ccoalg cc B x (fun y E =>
    a (MkCont (shape y) (fun e => f (cont y e) (RecF_inv_eq E H e)))).

Theorem hylo_cps_hylo : hylo_cps a cc =e hylo a c.
