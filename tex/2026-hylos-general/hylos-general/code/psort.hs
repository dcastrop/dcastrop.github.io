msort = hylo merge halves                -- the specification
split n xs | length xs > n = Left (halves xs)  -- halves: fed back
           | otherwise     = Right xs          -- short: passed on
