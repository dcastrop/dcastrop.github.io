def sum_tree(t):                        # t: a tree of heap objects
    if t.is_leaf: return t.value
    return sum_tree(t.left) + sum_tree(t.right)
