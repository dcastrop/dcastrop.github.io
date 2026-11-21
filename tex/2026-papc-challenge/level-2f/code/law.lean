-- Law 1, on one example: two selections are one, with both conditions
example : select (fun r => r.2 ≤ 2) (select (fun r => r.2 ≥ 2) attended)
        = select (fun r => r.2 ≥ 2 && r.2 ≤ 2) attended := rfl
