splitSort n = fmap msort . split n         -- sort what leaves the loop
psort' =  fb (farm k  (fun (splitSort n)))  -- k splitters
       || fb (farm k' (fun merge))          -- k' mergers, fed back
