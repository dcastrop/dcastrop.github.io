type ('sh, 'p, 'x) app0 = { shape : 'sh; cont0 : (('sh, 'p) pos -> 'x) }

let rec hylo esh f eA eB^\tikzmark{dict}^ g h x =
  let { shape = sx; cont0 = cx } = h x in
  g { shape = sx; cont0 = (fun e -> hylo esh f eA eB g h (cx e)) }^\tikzmark{rec}^

let qsort_spec =
  hylo def_eq treeF (list_eq def_eq) (list_eq def_eq) merge tsplit
