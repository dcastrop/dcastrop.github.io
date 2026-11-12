  map double . qsort
=   { qsort is divide and conquer }
  map double . hylo conquer divide
=   { fusion: doubling moves into conquer }
  hylo conquer2 divide

conquer2 Leaf         = []
conquer2 (Node l p r) = l ++ [double p] ++ r
