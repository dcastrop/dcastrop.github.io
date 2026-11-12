-- h is a list homomorphism if, wherever we split the list,
h (xs ++ ys) = combine (h xs) (h ys)      -- combine: associative
