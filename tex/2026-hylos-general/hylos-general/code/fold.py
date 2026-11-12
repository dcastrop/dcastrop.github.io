def fold(step, acc, xs):                # a.k.a. reduce
    for x in xs:
        acc = step(acc, x)
    return acc

total   = fold(lambda acc, x: acc + x, 0, xs)
count   = fold(lambda acc, x: acc + 1, 0, xs)
largest = fold(max, float("-inf"), xs)
