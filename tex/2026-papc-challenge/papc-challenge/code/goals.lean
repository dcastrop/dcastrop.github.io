-- Level 3: a law; its side condition is a hypothesis
theorem select_product (db : Database) (p : Cond) (q₁ q₂ : Query)
    (h : p.attrs ⊆ q₁.schema) :
    eval db (.select p (.product q₁ q₂)) =
      eval db (.product (.select p q₁) q₂) := by sorry

-- Level 4: the optimiser never changes an answer
theorem optimise_correct (db : Database) (q : Query) :
    eval db (optimise q) = eval db q := by sorry

-- Level 5: the hash join computes the join
theorem hashJoin_correct (r s : Table) :
    (hashJoin r s).toRelation = join r.toRelation s.toRelation := by sorry
