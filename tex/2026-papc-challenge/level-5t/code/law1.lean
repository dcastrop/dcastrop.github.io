-- Fact 5T.4: law 1, for lists
theorem select_select {α : Type} (p q : α → Bool) (l : List α) :
    select p (select q l) = select (fun r => p r && q r) l := by
  sorry
