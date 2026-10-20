let rec memo t c = function
  | [] -> []
  | (w, v) :: wvs ->
    if 0 < w && w <= c then (get t (c - w) + v) :: memo t c wvs
    else memo t c wvs
let rec table wvs c =
  if c = 0 then make 1 0
  else let t = table wvs (c - 1) in
       push t (max_int 0 (memo t c wvs))
let knapsack wvs c = newest (table wvs c)
