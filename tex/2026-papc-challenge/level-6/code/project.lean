-- project computes Sets.image
theorem toTable_project {α β : Type} (f : α → β) (l : List α) (s : β) :
    toTable (project f l) s ↔ Sets.image f (toTable l) s := by
  sorry
