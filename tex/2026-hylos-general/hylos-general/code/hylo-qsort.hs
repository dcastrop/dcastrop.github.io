hylo conquer divide = conquer . fmap (hylo conquer divide) . divide

data Layer x = Leaf | Node x Int x  deriving Functor   -- one layer

divide []       = Leaf
divide (p : xs) = Node [x | x <- xs, x < p] p [x | x <- xs, x >= p]

conquer Leaf         = []
conquer (Node l p r) = l ++ [p] ++ r

qsort = hylo conquer divide
