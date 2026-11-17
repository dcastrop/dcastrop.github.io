# Live demo: sort-then-double in Rocq

`Demo.v` repeats the quicksort calculation of the talk (the library's
`examples/QSort.v`), so it can be stepped through live:

1. the coalgebra (`c_split`, with its termination proof) and the algebra
   (`merge`);
2. the fusion law for doubling (`map_merge_fusion`);
3. the `Derive`: one rewrite at a time, with the goal after each; the
   `Fail rewrite deforest` line is the "wrong step": delete `Fail` live and
   Rocq answers `Found no subterm matching "hylo ?g2 ?h2 \o hylo ?g1 ?h1"`;
4. `Extraction qsort_times_two` and `Print Assumptions`;
5. a law with a false side condition: fusing `map negate` into the divide
   step. Rocq applies `hylo_fusion_r` but leaves its premise,
   `tsplit \o Lmap negate =e fmap (Lmap negate) \o tsplit`, as goal 2,
   which is false; the main goal would have become plain quicksort. The
   proof ends in `Abort`.

It needs the post-ITP library (`Derive`, `arewrite`, `finished`,
`hylo_cps_hylo`), built with `dune build`. By default the Makefile uses the
copy in `arrays-as-hylos/deps/rocq-hylomorphisms`; override with
`make HYLO=<checkout>/_build/default`.

    make              # writes _RocqProject, compiles Demo.v (capped at 3G)

Then open `Demo.v` in VS Code (VsRocq reads `_RocqProject`). If the demo
fails during the talk, the slide "Quicksort, Step by Step" shows the same
steps.
