Definition digits_ (b n : int) : App (ListF int) int :=
  MkCont (if n =? 0 then s_nil else s_cons (n mod b)) (fun _ => n / b).

Derive fast_power in (cata (pow_alg x) \o rana (digits 2) =e fast_power).
