-- Inside namespace Sets: one half of Fact 3T.3
theorem inter_sub {α : Type} (R S : Table α) (t : α) :
    inter R S t → diff R (diff R S) t :=
  fun ⟨hr, hs⟩ => ⟨hr, fun ⟨_, hns⟩ => hns hs⟩
