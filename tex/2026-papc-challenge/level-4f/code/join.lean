def joinOn {α β κ : Type} [BEq κ] (k₁ : α → κ) (k₂ : β → κ)
    (r : List α) (s : List β) : List (α × β) :=
  sorry

-- Attended ⋈ Session, on the week
example : (joinOn (fun a => a.2) (fun s => s.1) attended session).length = 4 :=
  rfl
