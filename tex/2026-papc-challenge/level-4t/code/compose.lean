-- Inside namespace Sets: images compose (Fact 4T.3)
theorem image_image {α β γ : Type} (f : α → β) (g : β → γ)
    (R : Table α) (u : γ) :
    image g (image f R) u ↔ image (fun t => g (f t)) R u := by
  sorry
