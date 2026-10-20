let mss_code xs =
  let rec f = function
  | [] -> (Some 0, Some 0)
  | h :: t ->
    let (m, s) = f t in
    let s' = match s with
      | Some b -> Some (max 0 (h + b))
      | None -> Some 0 in
    (omax s' m, s')
  in fst (f xs)
