let rec fast_power_code x n =
  if eqb n (Uint63.of_int (0)) then (Uint63.of_int (1))
  else mul (digit_pow x (mod0 n (Uint63.of_int (2))))
           (sq (fast_power_code x (div n (Uint63.of_int (2)))))
