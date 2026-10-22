let knap_step items t =                    (* best over the items *)
  max 0 (max_list (List.map (fun (w, v) ->
    match fast_drop w t with               (* jump into the array: O(1) *)
    | Some a -> head a + v
    | None -> min_int) items))

let knapsack items c =                     (* a loop over the capacities *)
  let rec loop i t =
    if i < c then loop (i + 1) (push (knap_step items t) t) else t
  in head (loop 0 (single 0))
