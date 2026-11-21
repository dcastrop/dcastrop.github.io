-- Fact 5T.3: projections compose
theorem project_project {α β γ : Type} (f : β → γ) (g : α → β)
    (l : List α) :
    project f (project g l) = project (fun r => f (g r)) l := by
  sorry
