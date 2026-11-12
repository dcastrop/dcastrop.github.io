psort' =  fb (farm k  (fun (splitSort n)))  -- halve long, sort short lists
       || fb (farm k' (fun merge))          -- merge sorted lists, fed back
