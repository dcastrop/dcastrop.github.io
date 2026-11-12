msort = hylo merge halves                -- the specification
split n xs | length xs > n = Left (halves xs)  -- halves: fed back
           | otherwise     = Right xs          -- short: passed on
psort =  fb (fun (split n)) || farm k (fun msort) || fb (fun merge)
