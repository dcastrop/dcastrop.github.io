let knap_step wvs x =
  imax (Uint63.of_int (0))
    (let rec f = function
     | [] -> min_int
     | h :: t ->
       imax
         (match fast_drop (fst h) x with
          | Some a -> Uint63.add (head a) (snd h)
          | None -> min_int)
         (f t)
     in f wvs)

let knapsack_arr wvs x =
  head
    (let rec f = function
     | (i, s) ->
       if Uint63.lt i x
       then f ((Uint63.add i (Uint63.of_int (1))), (push (knap_step wvs s) s))
       else s
     in f ((Uint63.of_int (0)), (single (Uint63.of_int (0)))))
