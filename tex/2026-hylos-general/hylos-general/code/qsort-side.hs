map double (conquer (Node l p r))
  ==  map double l ++ [double p] ++ map double r
  ==  conquer2 (fmap (map double) (Node l p r))
