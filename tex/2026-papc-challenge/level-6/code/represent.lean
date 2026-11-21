-- select computes Sets.select, with the condition "p r = true"
theorem toTable_select {α : Type} (p : α → Bool) (l : List α) (t : α) :
    toTable (select p l) t ↔
      Sets.select (fun r => p r = true) (toTable l) t := by
  sorry
