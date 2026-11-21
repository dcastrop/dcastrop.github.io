-- The hash join computes the join
theorem hashJoin_correct (r s : Table) :
    (hashJoin r s).toRelation = join r.toRelation s.toRelation := by sorry
