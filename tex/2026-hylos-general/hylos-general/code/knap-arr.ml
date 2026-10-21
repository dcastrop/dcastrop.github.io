let knapsack_arr wvs x =
  head
    (let rec f x0 =
       if Uint63.equal x0 (Uint63.of_int (0))
       then single
              (imax (Uint63.of_int (0))
                (let rec f0 = function
                 | [] -> min_int
                 | _ :: t -> imax min_int (f0 t)
                 in f0 wvs))
       else let r = f (Uint63.sub x0 (Uint63.of_int (1))) in
            push
              (imax (Uint63.of_int (0))
                (let rec f0 = function
                 | [] -> min_int
                 | h :: t ->
                   imax
                     (match fast_drop (fst h) r with
                      | Some a -> Uint63.add (head a) (snd h)
                      | None -> min_int)
                     (f0 t)
                 in f0 wvs))
              r
     in f x)
