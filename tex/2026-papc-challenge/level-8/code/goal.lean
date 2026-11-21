-- The optimiser never changes an answer
theorem optimise_correct (db : Database) (q : Query) :
    eval db (optimise q) = eval db q := by sorry
