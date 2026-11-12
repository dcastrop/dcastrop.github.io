data Split x = Empty | One Int | Two x x  deriving Functor

halves []  = Empty
halves [x] = One x
halves xs  = Two l r  where (l, r) = splitAt (length xs `div` 2) xs

hom f combine e = hylo conquer halves
  where conquer Empty     = e
        conquer (One x)   = f x
        conquer (Two a b) = combine a b
