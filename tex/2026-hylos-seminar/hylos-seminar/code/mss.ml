let mss_code xs =
  let (y, _) =
    let rec f = function
    | [] -> ((Some Bigint.zero), (Some Bigint.zero))
    | h :: t ->
      let p = f t in
      let z0 =
        match snd p with
        | Some b -> Some (Bigint.max Bigint.zero (Bigint.add h b))
        | None -> Some Bigint.zero
      in
      ((omax z0 (fst p)), z0)
    in f xs
  in
  y
