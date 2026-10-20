Lemma table_to_list                                  (* by hylo_fusion_l *)
  : to_list \o hylo (l_in \o Cons \o pair a id) c =e hylo (list_alg a') c.

Lemma dyna_array : to_Z n < to_Z max_length ->
  hd d (int_hylo (list_alg a') n)
  = (fst (int_hylo (arr_alg (n + 1) a'') n)).[n].
