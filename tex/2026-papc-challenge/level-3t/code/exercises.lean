-- Inside namespace Sets: law 4
theorem select_diff {α : Type} (p : α → Prop) (R S : Table α) (t : α) :
    select p (diff R S) t ↔ diff (select p R) S t :=
  sorry

-- The other half of Fact 3T.3: this one needs classical logic
theorem diff_diff_sub {α : Type} (R S : Table α) (t : α) :
    diff R (diff R S) t → inter R S t :=
  sorry
