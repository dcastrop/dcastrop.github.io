-- Inside namespace Sets: each row t of R gives the row f t of f[R]
theorem image_of {α β : Type} (f : α → β) (R : Table α) (t : α)
    (h : R t) : image f R (f t) := by
  exact ⟨t, h, rfl⟩
