let rec fast_power x x0 =
  if Uint63.equal x0 (Uint63.of_int (0))
  then (Uint63.of_int (1))
  else Uint63.mul (digit_pow x (Uint63.rem x0 (Uint63.of_int (2))))
         (sq (fast_power x (Uint63.div x0 (Uint63.of_int (2)))))
