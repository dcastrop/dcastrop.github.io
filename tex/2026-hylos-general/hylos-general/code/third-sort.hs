sort = foldr insert []                    -- insertion sort, from the right
sort = foldl (\acc x -> insert x acc) []  -- insertion sort, from the left
-- g = id works; then calculate:  sort (a ++ b) = merge a b
