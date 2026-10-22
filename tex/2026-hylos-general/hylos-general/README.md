# Talk: Calculating Correct and Efficient Programs in Rocq

A general-CS version of the hylomorphisms seminar (`../../2026-hylos-seminar`),
for an audience outside programming languages (machine learning, security,
systems). Diagrams over code, intuition over category theory; a few real Rocq
and OCaml snippets. It ends with work in progress towards low-level
correct-by-construction code extracted from high-level calculation steps,
possibly guided by a cost model.

## Build

    make                  # highlight code/, then latexmk -lualatex
    make clean

Same toolchain and style as the seminar (`../template/dcptalk.sty`, TeX Live
2026, LuaLaTeX, `pygmentize`). `make` also writes `main.pdfpc` and
`main-notes.md` from the `\speakernote`s (55-minute timer). Notes are
terse cues, not a script: `\\` separates bullet points (this deck's copy of
`make-notes.py` turns them into a Markdown list). They are reminders and
pointers only, with no click markers.

## Slides with notes

    make presenter        # main-presenter.pdf
    make publish          # ../slides.pdf and ../slides_notes.pdf

`main-presenter.pdf` puts each slide on the left half of a double-width page
and its notes on the right (`../template/make-presenter.py`, from
`main.notes`). On frames with overlays, the header shows the step
("step 2 of 3"). Present with `pdfpc -n right main-presenter.pdf`, or
read it in any viewer. It is tagged, with each slide image's alt text naming
the slide.

`../slides.pdf` is linked from the talks page (through `latex:` in
`_talks/`); `../slides_notes.pdf` is published next to it but not linked.

## Code snippets

Code is kept to calculations and their output: the opening example
(`sort-times-two.ml`, hand-written), the quicksort `Derive`
(`qsort2-derive.v`, library source plus two `\tikzmark`s) with its steps and
extracted code, and the knapsack `Derive` (`knap-derive.v`) with its steps and
extracted code, simplified for this audience (`knap-simple.ml`, tagged
"(simplified)"; the seminar shows the real extraction). Everything else is a
diagram. A block that is not verbatim gets `\simplified` (a grey
"(simplified)" tag, `preamble.tex`).

Shared with the other hylomorphism talk, and kept identical (check with
`python3 ../../check-hylos-sync.py` from `tex/`): `template/dcptalk.sty`, the
code files `sort-times-two.ml`, `qsort2.ml`, `qsort-steps.v`, `knap-steps.v`,
`knap-derive.v`, the quicksort `Derive`, and the frames "Quicksort, Step by
Step" and "Knapsack, Step by Step". "Knapsack: What Comes Out" differs on
purpose: simplified here, the real extraction in the seminar.

All checked against rocq-hylomorphisms 0bd54f8 (2026-10-22, pushed; the
local changes on top are build and warning settings only), in
`arrays-as-hylos/deps/rocq-hylomorphisms`:

- `qsort-steps.v`, `knap-steps.v`: the goal Rocq prints after each rewrite of
  the `Derive` (replayed against the compiled library), with the name of the
  rewrite and a gloss as a comment; only line breaks are ours. Each step of
  the slide shows the derivation up to that rewrite (`\fvset{lastline = n}`).
- `qsort2.ml`: extracted code, verbatim. `knap-simple.ml`: the extracted
  `knap_step` and loop `knapsack_arr`, simplified (`max_list`, plain
  arithmetic, no `Uint63`); `fast_drop` is the O(1) lookup.
- The knapsack `Derive` (`knap-derive.v`): `reenumerate` (items to
  capacities, with a table whose lookups jump into the array block, O(1)),
  then `dyna_loop` (the table of a count-down is built by a loop); the side
  goals are the loop's step, its first entry and the lookup algebra.
- The quicksort `Derive`s end with `hylo_cps_hylo` (a continuation-passing
  coalgebra), and `finished` reduces the result, so a plain `Extraction`
  gives clean code.

`images/mpst.pdf` is `../../2024-synthetic-mpst/figures/MPST5.pdf`.

## Structure and timing (about 55 min of talk, then questions)

| File                         | Content                                                     | Min |
|------------------------------|-------------------------------------------------------------|-----|
| `00-title.tex`               | title, research in one slide, the talk in one picture | 3 |
| `01-problem.tex`             | sort-then-double, three routes to fast+correct, rewrite rules in ML compilers/DBs | 6 |
| `02-divide-and-conquer.tex`  | split/combine, call tree, producers/consumers, fusion and deforestation, the example derived | 10 |
| `03-proofs.tex`              | trusted base, three obstacles, shapes and positions, termination proofs, no axioms | 8 |
| `04-results.tex`             | a calculation in Rocq, its steps and extracted code; knapsack as a dynamorphism, its steps and extracted code (exponential to O(1) array lookups); gallery (power, MSS); summary | 16 |
| `05-goal.tex`                | work in progress: two ways out of Rocq (OCaml today, direct low-level print as the goal), the goal, representation-changing laws, a closed low-level target, cost model, untrusted search / trusted checking, current status | 10 |

If running long: skip "You Already Trust Rewrite Rules", "Maximum Segment
Sum: Spec and Result", or
"Remember, Don't Recompute" (go straight from the call tree to the lookups).
