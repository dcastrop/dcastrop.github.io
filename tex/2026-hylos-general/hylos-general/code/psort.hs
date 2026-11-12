msort = hylo merge halves                -- the specification
psort =  fb (fun (split n))     -- halve lists longer than n, feed back
      || farm k (fun msort)     -- sort the short lists, k at a time
      || fb (fun merge)         -- merge sorted lists, feed back
