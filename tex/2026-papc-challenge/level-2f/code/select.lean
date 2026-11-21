def select {α : Type} (p : α → Bool) : List α → List α
  | [] => sorry
  | row :: rest => sorry

-- Test: should print [("Ada", 1), ("Alan", 1)]
#eval select (fun row => row.2 == 1) attended
