Lemma Lmap_merge (f : int ~> int)
  : Lmap f \o merge =e merge \o natural (nt_shape id f) \o fmap (Lmap f).
