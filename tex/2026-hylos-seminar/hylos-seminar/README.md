# Seminar: Program Calculation with Hylomorphisms in Rocq

A 1-hour talk on the ITP 2025 paper (`deps/rocq-hylomorphisms/paper`),
updated to the current library, in the style of the 2025-ITP and 2026
seminar decks (`../template/dcptalk.sty`), ending with open questions.

## Build

    make                  # highlight code/, then latexmk -lualatex
    make STYLE=tango      # another Pygments colour scheme
    make clean

Needs TeX Live 2026 (ltx-talk 0.6 or newer: lists reveal with
`\begin{itemize}[<+->]`, not the 0.3 `action-spec` key), LuaLaTeX and
`pygmentize`. Fonts as in the paper (`fonts = paper`): Latin Modern Roman text,
Latin Modern Sans titles, Latin Modern Math; JetBrains Mono for code.
`fonts = lm` in `preamble.tex` gives the sans look of the old decks. No footer (`footer = true` in
`preamble.tex` adds it). The Makefile puts `../template` on `TEXINPUTS`. Tagging is on
(`pdfstandard = ua-2`); every picture has alt text.

## Speaker notes

Every frame has a `\speakernote`. `make` also writes `main.pdfpc` (open the
talk with `pdfpc main.pdf`: notes on the presenter screen, 50-minute timer)
and `main-notes.md` (a printable sheet). `[click]` marks where to advance
an overlay.

## Code snippets

Each listing is a file in `code/` (`.v`, `.ml`, `.txt` for Rocq output),
highlighted into `gen/` by Pygments. Slides include them with
`\rocqblock{name.v}` (blue), `\ocamlblock{name.ml}` (green),
`\badblock{name.txt}` (red) or `\outblock{name.txt}` (grey). Callouts point
at `^\tikzmark{name}^` marks inside snippets. `code/rocqlexer.py` adds
`Derive`, `arewrite`, `finished` to Pygments' Coq lexer. Keep lines under
about 76 characters.

Snippets come from the library sources and its extracted OCaml, except:
`naive-*` (a small direct encoding with dependent positions, run through
Rocq 9.3 and extraction) and `raw-extr.*` (`Recursive Extraction qsort`
without `Eval simpl` or inlining flags). Both are real outputs.

Shortened or rewritten, and said so on the slide or in the notes:
`hylo-def.v` (no dependent match), `memo.v` and `reenum.v` (implicit
arguments dropped), `knap-calc.v` (steps 1 and 2; step 1's proof left out).
`raw-extr.ml` is regenerated against the current library: `Recursive
Extraction` of the unreduced `hylo merge tsplit`.

Shared with the other hylomorphism talk, and kept identical (check with
`python3 ../../check-hylos-sync.py` from `tex/`): `template/dcptalk.sty`, the
code files `sort-times-two.ml`, `qsort2.ml`, `qsort-steps.v`, `knap-steps.v`,
`knap-arr.ml`, `knap-jump.ml`, `knap-derive.v`, the quicksort `Derive`, and the
frames "Quicksort, Step by Step", "Knapsack, Step by Step" and "Knapsack: What
Comes Out".

All checked against rocq-hylomorphisms 0bd54f8 (2026-10-22, pushed; the
local changes on top are build and warning settings only), in
`arrays-as-hylos/deps/rocq-hylomorphisms`:

- `qsort-steps.v`, `knap-steps.v`: the goal Rocq prints after each rewrite of
  the `Derive` (replayed against the compiled library), with the name of the
  rewrite and a gloss as a comment; only line breaks are ours. Each step of
  the slide shows the derivation up to that rewrite (`\fvset{lastline = n}`).
- `qsort2.ml`, `knap-arr.ml`, `knap-jump.ml`: extracted code, verbatim
  (`knap-arr.ml`: `knap_step` and the loop `knapsack_arr`; `knap-jump.ml`:
  `jump` and `fast_drop`, the O(1) lookup into the array table).
- The knapsack `Derive` (`knap-derive.v`): `reenumerate` (items to
  capacities, with a table whose lookups jump into the array block, O(1)),
  then `dyna_loop` (the table of a count-down is built by a loop); the side
  goals are the loop's step, its first entry and the lookup algebra.
- The quicksort `Derive`s end with `hylo_cps_hylo` (a continuation-passing
  coalgebra), and `finished` reduces the result, so a plain `Extraction`
  gives clean code.

## Structure and timing (about 55 min of talk, then questions)

| File                       | Content                                                   | Min |
|----------------------------|-----------------------------------------------------------|-----|
| `00-title.tex`             | title, problem / our work                                 | 2   |
| `01-motivation.tex`        | sort-then-double, program calculation                     | 3   |
| `02-recursion-schemes.tex` | Background: squares, quicksort tree, laws, conjugate hylos | 7  |
| `03-challenges.tex`        | why Rocq, challenges and solutions, roadmap               | 3   |
| `04-containers.tex`        | Part I: containers, a bad attempt, decidable UIP, `Cont`  | 7   |
| `05-hylos-in-rocq.tex`     | Part II: recursive coalgebras, `hylo`, laws, no axioms    | 7   |
| `06-calculation.tex`       | Part III: `Derive`, fusion and its steps, digits, inlining, usability | 7 |
| `07-dynamorphisms.tex`     | Part IV: memo tables, `dyna_iso`, `reenumerate`, knapsack from the naive hylo: calculation, steps, extracted code | 9 |
| `08-monoid-algebras.tex`   | Part V: `malg`, `malg_fusion`, MSS                        | 3   |
| `09-wrapup.tex`            | summary, changes, open questions                          | 7   |

If running long: skip "Conjugate Hylomorphisms", "Setoids and Morphisms",
"What Changed Since the Paper", or "Coalgebras and Anamorphisms".

Listings are trimmed to the lines that make the point (at most about 10).
Where real output is shortened or rewritten, the slide says what changed.
