for (int i = 0; i < n; i++) {          /* outer loop: rows       */
  R r = start(s);
  for (int j = 0; j < m; j++)          /* inner loop: may read s */
    r = inner(s, r, a[i][j]);
  s = outer(s, r);
}
