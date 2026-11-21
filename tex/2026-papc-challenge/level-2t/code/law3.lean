-- Inside namespace Sets: law 3
theorem select_union {α : Type} (p : α → Prop) (R S : Table α) (t : α) :
    select p (union R S) t ↔ union (select p R) (select p S) t :=
  sorry
