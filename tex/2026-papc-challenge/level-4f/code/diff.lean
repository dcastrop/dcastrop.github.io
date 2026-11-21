def diff {α : Type} [BEq α] (r s : List α) : List α := sorry
def inter {α : Type} [BEq α] (r s : List α) : List α := sorry

-- Which sessions had nobody?
example : diff (project (fun s => s.1) session)
               (project (fun a => a.2) attended) = [4] := rfl
