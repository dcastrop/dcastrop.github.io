def dedup {α : Type} [BEq α] : List α → List α
  | [] => sorry
  | row :: rest => sorry   -- hint: rest.contains row

example : dedup (project (fun row => row.2) attended) = [1, 2, 3] := rfl
