hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo a c = a . fmap (hylo a c) . c

data TreeF x = Leaf | Node x Int x  deriving Functor   -- one layer

split []      = Leaf                                   -- coalgebra
split (p : t) = Node [x | x <- t, x < p] p [x | x <- t, x >= p]

merge Leaf         = []                                -- algebra
merge (Node l p r) = l ++ [p] ++ r

qsort = hylo merge split
