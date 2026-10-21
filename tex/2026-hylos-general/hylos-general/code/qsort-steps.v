  (Lmap times_two \o cata merge) \o rana tsplit
=e  (* map_merge_fusion: double inside merge *)
  hylo (merge \o natural (nt_shape id times_two)) l_out \o rana tsplit
=e  (* hylo_ana: the unfold is a hylo *)
  hylo (merge \o natural (nt_shape id times_two)) l_out \o hylo l_in tsplit
=e  (* deforest: build, then take apart, cancel out *)
  hylo (merge \o natural (nt_shape id times_two)) tsplit
