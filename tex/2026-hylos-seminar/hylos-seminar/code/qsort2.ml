let rec qsort_times_two_code = function
| [] -> []
| h :: t ->
  let (l, r) = partition (fun x0 -> Uint63.lt x0 h) t in
  let x0 = fun p ->
    qsort_times_two_code (match p with
                          | Lbranch -> l
                          | Rbranch -> r)
  in
  app (x0 Lbranch) ((Uint63.mul (Uint63.of_int (2)) h) :: (x0 Rbranch))
