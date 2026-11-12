data Split x = Empty | One Int | Two x x  deriving Functor

splitBy cut []  = Empty                    -- leaves: no element, or one
splitBy cut [x] = One x
splitBy cut xs  = Two l r  where (l, r) = cut xs     -- l ++ r == xs

hom cut = hylo conquer (splitBy cut)       -- the cut is a parameter
  where conquer Empty     = e
        conquer (One x)   = f x
        conquer (Two a b) = combine a b

halves xs = splitAt (length xs `div` 2) xs  -- balanced: parallel
heads  xs = splitAt 1 xs                    -- one at a time: a loop
