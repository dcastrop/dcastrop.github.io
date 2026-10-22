let rec qsort_times_two = function
| [] -> []
| i :: l ->
  let (l0, l1) = partition (fun x0 -> Uint63.lt x0 i) l in
  app (qsort_times_two l0)
    ((Uint63.mul (Uint63.of_int (2)) i) :: (qsort_times_two l1))
