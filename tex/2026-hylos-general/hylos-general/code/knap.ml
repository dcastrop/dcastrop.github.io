let rec look t j =                         (* j steps down the table *)
  if j = 0 then Some (head t)
  else if is_last t then None else look (rest t) (j - 1)
let best wvs t =                           (* t: results for c-1, c-2, ... *)
  max_int 0 (map_some (fun (w, v) ->
    if w = 0 then None else Option.map (fun u -> u + v) (look t (w - 1))) wvs)
let rec table wvs c =
  if c = 0 then single 0
  else let t = table wvs (c - 1) in push (best wvs t) t
let knapsack wvs c = head (table wvs c)
