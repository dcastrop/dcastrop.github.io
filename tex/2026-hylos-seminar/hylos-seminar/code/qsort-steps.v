  (Lmap times_two \o cata merge) \o rana tsplit
=e  (* map_merge_fusion: double inside merge *)
  hylo (merge \o natural (nt_shape id times_two)) l_out \o rana tsplit
=e  (* hylo_ana, deforest: unfold then fold, with no tree in between *)
  hylo (merge \o natural (nt_shape id times_two)) tsplit
=e  (* hylo_cps_hylo: continuation-passing, for clean extraction *)
  hylo_cps (merge \o natural (nt_shape id times_two)) tsplit_k
