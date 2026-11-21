-- The table a list represents (Definition 1.2)
def toTable {α : Type} (l : List α) : Sets.Table α :=
  fun t => t ∈ l

-- Union is appending: your union (3F) computes Sets.union (2T)
theorem toTable_union {α : Type} (l m : List α) (t : α) :
    toTable (union l m) t ↔ Sets.union (toTable l) (toTable m) t := by
  simp [toTable, union, Sets.union]
