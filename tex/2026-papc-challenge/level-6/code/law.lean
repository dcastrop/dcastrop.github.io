-- Law 1 for lists, as tables (Corollary 6.3): no new induction
theorem toTable_select_select {α : Type} (p q : α → Bool)
    (l : List α) (t : α) :
    toTable (select p (select q l)) t ↔
      toTable (select (fun r => p r && q r) l) t := by
  sorry
