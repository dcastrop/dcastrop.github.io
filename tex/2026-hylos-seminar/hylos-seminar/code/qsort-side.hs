map double (merge (Node l p r))
  ==  map double l ++ [double p] ++ map double r
  ==  merge2 (fmap (map double) (Node l p r))
