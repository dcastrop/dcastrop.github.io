def qsort(xs):
    if not xs:
        return []
    ^\tikzmark{dl}^^\tikzmark{pa}^p^\tikzmark{pb}^, rest = xs[0], xs[1:]
    left  = [x for x in rest if x < p]
    right = [x for x in rest if x >= p]^\tikzmark{dr}^
    return ^\tikzmark{ra}^qsort(left)^\tikzmark{rb}^ ^\tikzmark{cl}^+ ^\tikzmark{pc}^[p]^\tikzmark{pd}^ +^\tikzmark{cr}^ ^\tikzmark{rc}^qsort(right)^\tikzmark{rd}^
