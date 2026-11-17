fold(step, e, map(f, xs)) == fold(lambda acc, x: step(acc, f(x)), e, xs)
