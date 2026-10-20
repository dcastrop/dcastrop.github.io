(* Arrays are one more memo table: an initial algebra of Memo *)
Instance ATab_initial : Initial (Memo NatF A) (ATab A).

(* dyna does not depend on the memo table *)
Theorem dyna_iso : dyna (T := T) a c =e dyna (T := U) (a \o fmap (iso U T)) c.

Derive knapsack_arr in (knapsack_naive wvs =e knapsack_arr) as calc.
Proof.
  rewrite <- (knapsack_correct (T := ATab int)).  (* naive hylo = dyna *)
  unfold knapsack; rewrite dyna_memo. finished.   (* share the table *)
Qed.
