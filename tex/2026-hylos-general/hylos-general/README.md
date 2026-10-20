# Talk: Calculating Correct and Efficient Programs

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
`main-notes.md` from the `\speakernote`s (50-minute timer). Notes are
terse cues, not a script: `\\` separates bullet points (this deck's copy of
`make-notes.py` turns them into a Markdown list), and `[click]` marks each
overlay step.

## Slides with notes

    make presenter        # main-presenter.pdf
    make publish          # ../slides.pdf and ../slides_notes.pdf

`main-presenter.pdf` puts each slide on the left half of a double-width page
and its notes on the right (`../template/make-presenter.py`, from
`main.notes`). On frames with overlays, the current step's bullets are bold
and later ones grey. Present with `pdfpc -n right main-presenter.pdf`, or
read it in any viewer. It is tagged, with each slide image's alt text naming
the slide.

`../slides.pdf` is linked from the talks page (through `latex:` in
`_talks/`); `../slides_notes.pdf` is published next to it but not linked.

## Code snippets

As in the seminar: files in `code/`, included with `\rocqblock`,
`\ocamlblock`, `\badblock`, `\outblock`. Any block that is not verbatim
tool output or library source is followed by `\simplified` (a grey
"(simplified)" tag, defined in `preamble.tex`):

- verbatim: `qsort2-derive.v` (library source, plus two `\tikzmark`s),
  `sort-times-two.ml` (hand-written, labelled so on the slide);
- simplified: `naive-extr.ml` (trimmed), `assumptions.txt` (condensed),
  `qsort2.ml` (rebuilt from the seminar's `qsort_code`), `mss.ml`,
  `knap-calc.v` and `knap.ml`.

`knap-calc.v` follows the ongoing library work (`deps/rocq-hylomorphisms` in
arrays-as-hylos, uncommitted as of 2026-10-20): arrays are one more initial
algebra of `Memo` (`ATab_initial`), `dyna_iso` swaps memo tables, and a
`Derive` goes from the naive exponential hylo to the array dyna.

## Structure and timing (about 50 min of talk, then questions)

| File                         | Content                                                     | Min |
|------------------------------|-------------------------------------------------------------|-----|
| `00-title.tex`               | title, the talk in one picture                              | 2   |
| `01-problem.tex`             | sort-then-double, three routes to fast+correct, rewrite rules in ML compilers/DBs | 6 |
| `02-divide-and-conquer.tex`  | split/combine, call tree, producers/consumers, fusion and deforestation, the example derived | 10 |
| `03-proofs.tex`              | trusted base, three obstacles, `Obj.magic`, shapes and positions, termination proofs, no axioms | 9 |
| `04-results.tex`             | a calculation in Rocq, extracted OCaml, knapsack as a dynamorphism (exponential, list table, O(1) array lookups), gallery (power, MSS), summary | 12 |
| `05-goal.tex`                | work in progress: two ways out of Rocq (OCaml today, direct low-level print as the goal), the goal, representation-changing laws, a closed low-level target, cost model, untrusted search / trusted checking, current status | 10 |

If running long: skip "You Already Trust Rewrite Rules", "What the Textbook
Encoding Extracts To", "Maximum Segment Sum: Spec and Result", or
"Remember, Don't Recompute" (go straight from the call tree to the lookups).
