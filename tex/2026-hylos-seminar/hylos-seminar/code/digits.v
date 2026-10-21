Definition digits_ (b n : int) : App (ListF int) int :=
  MkCont (if n =? 0 then s_nil else s_cons (n mod b)) (fun _ => n / b).

Definition power (x : int) : int ~> int :=
  cata (pow_alg x) \o rana (digits 2 eq_refl).

Derive fast_power in (power x =e fast_power) as fast_power_calc.
