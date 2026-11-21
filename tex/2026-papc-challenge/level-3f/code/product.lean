def product {α β : Type} : List α → List β → List (α × β)
  | [], _ => sorry
  | a :: rest, s => sorry

example : (product member session).length = 12 := rfl
