-- Law 5, with its side condition as the hypothesis h
theorem select_product (db : Database) (p : Cond) (q₁ q₂ : Query)
    (h : p.attrs ⊆ q₁.schema) :
    eval db (.select p (.product q₁ q₂)) =
      eval db (.product (.select p q₁) q₂) := by sorry
