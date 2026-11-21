def member : List (String × String) :=
  [("Ada", "Maths"), ("Alan", "CS"), ("Grace", "CS")]

def attended : List (String × Nat) :=
  [("Ada", 1), ("Alan", 1), ("Alan", 2), ("Grace", 3)]

#eval member            -- prints the table
#eval attended.length   -- 4
