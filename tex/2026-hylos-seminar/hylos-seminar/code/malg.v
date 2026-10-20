Definition malg_ (leaf : Sh ~> option W) (x : App F W) : W :=
  let (s, k) := x in mconcat M (opt_cons (leaf s) (map k (members F s))).

Definition reduce (w : A ~> W) : list A ~> W :=
  hylo (malg (ListF A) M (cons_leaf w)) ilist_coalg.
