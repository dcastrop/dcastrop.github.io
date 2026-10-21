let rec jump n t =
  let { blk = b; top = i; prev = p } = t in
  if Uint63.le n i
  then Some { blk = b; top = (Uint63.sub i n); prev = p }
  else (match p with
        | Some q -> jump (Uint63.sub (Uint63.sub n i) (Uint63.of_int (1))) q
        | None -> None)

let fast_drop j t =
  if Uint63.equal j (Uint63.of_int (0))
  then None
  else jump (Uint63.sub j (Uint63.of_int (1))) t
