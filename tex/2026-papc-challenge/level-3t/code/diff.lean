namespace Sets
def diff {α : Type} (R S : Table α) : Table α :=
  fun t => R t ∧ ¬ S t

def inter {α : Type} (R S : Table α) : Table α :=
  fun t => R t ∧ S t
end Sets
