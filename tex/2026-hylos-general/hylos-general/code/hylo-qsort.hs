hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo conquer divide = conquer . fmap (hylo conquer divide) . divide

data Layer x = Leaf | Node x Int x  deriving Functor   -- one layer

divide :: [Int] -> Layer [Int]
divide []       = Leaf
divide (p : xs) = Node [x | x <- xs, x < p] p [x | x <- xs, x >= p]

conquer :: Layer [Int] -> [Int]
conquer Leaf         = []
conquer (Node l p r) = l ++ [p] ++ r

qsort :: [Int] -> [Int]
qsort = hylo conquer divide
