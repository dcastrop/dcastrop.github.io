-- If h is a loop from the left and also a loop from the right
-- (stepL, stepR take one element at a time: not associative),
h = foldl stepL e
h = foldr stepR e
-- then there is an associative combine, built from h itself:
h (xs ++ ys) = combine (h xs) (h ys)
  where combine a b = h (g a ++ g b)  -- g a: any input with h (g a) = a
