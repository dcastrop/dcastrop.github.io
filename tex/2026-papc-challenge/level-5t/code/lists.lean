def select {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | row :: rest => if p row then row :: select p rest else select p rest

def project {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | row :: rest => f row :: project f rest

def product {α β : Type} : List α → List β → List (α × β)
  | [], _ => []
  | a :: rest, s => project (fun b => (a, b)) s ++ product rest s
