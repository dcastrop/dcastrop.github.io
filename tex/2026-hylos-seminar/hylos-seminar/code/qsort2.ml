let rec qsort_times_two_code = function
| [] -> []
| h :: t -> ...                                        (* as qsort_code *)
  app (x0 Lbranch) ((mul (Uint63.of_int (2)) h) :: (x0 Rbranch))
