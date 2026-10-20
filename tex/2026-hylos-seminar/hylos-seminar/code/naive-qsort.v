Fixpoint qsort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => qsort (filter (fun x => x <? h) t)
              ++ h :: qsort (filter (fun x => negb (x <? h)) t)
  end.
