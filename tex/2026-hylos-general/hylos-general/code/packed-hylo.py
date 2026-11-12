def sum_packed(buf):                    # specification:
    tree, _ = unpack(buf, 0)            #   rebuild the tree (divide)
    return sum_tree(tree)               #   then fold it (conquer)

# program: one pass over the buffer, never building the tree
