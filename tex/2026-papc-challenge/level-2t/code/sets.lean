namespace Sets
-- A table, given by its rows: R t says that t is a row of R
abbrev Table (α : Type) := α → Prop

def select {α : Type} (p : α → Prop) (R : Table α) : Table α :=
  fun t => R t ∧ p t

def union {α : Type} (R S : Table α) : Table α :=
  fun t => R t ∨ S t
end Sets
