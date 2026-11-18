data SplitF x = Empty | One Int | Two x x  deriving Functor

splitBy cut []  = Empty
splitBy cut [x] = One x
splitBy cut xs  = Two l r  where (l, r) = cut xs  -- l ++ r == xs, l, r /= []

hom e f op cut = hylo alg (splitBy cut)           -- the cut is a parameter
  where alg Empty     = e
        alg (One x)   = f x
        alg (Two a b) = op a b                     -- op associative

halves xs = splitAt (length xs `div` 2) xs         -- depth log n: parallel
heads  xs = splitAt 1 xs                           -- depth n: a loop
