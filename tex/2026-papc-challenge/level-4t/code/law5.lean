-- Inside namespace Sets: law 5, with its side condition h
theorem select_product {α β : Type} (p : α × β → Prop) (p' : α → Prop)
    (h : ∀ t s, p (t, s) ↔ p' t) (R : Table α) (S : Table β)
    (t : α) (s : β) :
    select p (product R S) (t, s) ↔ product (select p' R) S (t, s) := by
  sorry
