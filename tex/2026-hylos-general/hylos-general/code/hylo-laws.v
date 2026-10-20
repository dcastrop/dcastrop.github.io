Lemma hylo_uniq : f =e hylo a c <-> f =e a \o fmap f \o c.

Lemma hylo_fusion_l : h \o a =e b \o fmap h -> h \o hylo a c =e hylo b c.
Lemma hylo_fusion_r : c \o h =e fmap h \o d -> hylo a c \o h =e hylo a d.
Lemma deforest      : d \o b =e id -> hylo a d \o hylo b c =e hylo a c.
