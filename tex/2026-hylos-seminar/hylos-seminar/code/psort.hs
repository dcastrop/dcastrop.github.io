msort = hylo merge halves                   -- merge: two sorted lists
cutoff n xs | length xs > n = Left (halves xs)  -- halves: fed back
            | otherwise     = Right xs          -- short: passed on
