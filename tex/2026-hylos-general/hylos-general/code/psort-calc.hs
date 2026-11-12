  hylo merge halves
=   { reforestation: put the tree back }
  cata merge . ana halves
=   { stop dividing at size n: the leaves run the same hylo }
  cata merge . mapLeaves (hylo merge halves) . ana (halvesUntil n)
