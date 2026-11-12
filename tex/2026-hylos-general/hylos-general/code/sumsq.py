# Specification: clear, but builds a temporary list
def sum_squares(xs):
    return sum([x * x for x in xs])

# Program: one pass, no temporary list
def sum_squares(xs):
    total = 0
    for x in xs:
        total = total + x * x
    return total
