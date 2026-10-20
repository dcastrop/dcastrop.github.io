let rec memo_arr t c = function
| [] -> []
| (w, v) :: wvs ->
  if 0 < w && w <= c then (Parray.get t (c - w) + v) :: memo_arr t c wvs
  else memo_arr t c wvs

(* the loop, for c = 1 .. n: *)
  Parray.set t c (max_int 0 (memo_arr t c wvs))
