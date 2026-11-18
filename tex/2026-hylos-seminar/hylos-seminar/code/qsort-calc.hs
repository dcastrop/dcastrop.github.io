  map double . qsort
=   { definition }
  map double . hylo merge split
=   { fusion, left: map double . merge = merge2 . fmap (map double) }
  hylo merge2 split

merge2 = merge . double_pivot   -- double_pivot (Node l p r) = Node l (2*p) r
