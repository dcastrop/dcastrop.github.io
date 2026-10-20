let rec qsort_code = function
| [] -> []
| h :: t ->
  let (l, r) = partition (fun x0 -> ltb x0 h) t in
  let x0 = fun e -> qsort_code (match e with Lbranch -> l | Rbranch -> r) in
  app (x0 Lbranch) (h :: (x0 Rbranch))
