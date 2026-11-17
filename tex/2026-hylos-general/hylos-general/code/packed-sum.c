/* the tree, serialised in preorder:  N  N  L 1  L 2  L 3 */
char *sum(char *p, int *out) {         /* returns the end of the subtree */
  if (*p == LEAF) { memcpy(out, p + 1, sizeof(int)); return p + 1 + sizeof(int); }
  int a, b;
  char *q = sum(p + 1, &a);            /* left: right after the tag      */
  char *r = sum(q, &b);                /* right: where the left one ends */
  *out = a + b;
  return r;
}
