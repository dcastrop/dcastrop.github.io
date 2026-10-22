let mss_linear x =
  let (y, _) =
    let rec f = function
    | [] -> ((Some Bigint.zero), (Some Bigint.zero))
    | h :: t ->
      let p = f t in
      let z0 = omax (Some Bigint.zero) (oplus (Some h) (snd p)) in
      ((omax z0 (fst p)), z0)
    in f x
  in
  y
