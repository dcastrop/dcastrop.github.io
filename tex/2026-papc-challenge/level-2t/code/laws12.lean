-- Inside namespace Sets: law 1
theorem select_select {α : Type} (p q : α → Prop) (R : Table α) (t : α) :
    select p (select q R) t ↔ select (fun r => p r ∧ q r) R t :=
  sorry

-- Law 2
theorem select_comm {α : Type} (p q : α → Prop) (R : Table α) (t : α) :
    select p (select q R) t ↔ select q (select p R) t :=
  sorry
