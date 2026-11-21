theorem project_length {α β : Type} (f : α → β) (t : List α) :
    (project f t).length = t.length := by
  induction t with
  | nil => rfl
  | cons row rest ih => simp [project, ih]
