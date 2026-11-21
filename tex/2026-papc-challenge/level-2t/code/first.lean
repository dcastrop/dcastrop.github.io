-- Inside namespace Sets: a selection never adds rows
theorem select_sub {α : Type} (p : α → Prop) (R : Table α) (t : α) :
    select p R t → R t :=
  fun h => h.1
