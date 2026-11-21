def project {α β : Type} (f : α → β) : List α → List β
  | [] => sorry
  | row :: rest => sorry

-- Test: should print ["Ada", "Alan", "Alan", "Grace"]
#eval project (fun row => row.1) attended
