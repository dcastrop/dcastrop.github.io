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
`main-notes.md` from the `\speakernote`s (50-minute timer).

## Code snippets

As in the seminar: files in `code/`, included with `\rocqblock`,
`\ocamlblock`, `\badblock`, `\outblock`. All are copied from the seminar
deck, except: `qsort2-derive.v` gains two `\tikzmark`s for callouts, and
`qsort2.ml` is the full extracted function (the seminar elides the lines
shared with `qsort_code`).

## Structure and timing (about 45 min of talk, then questions)

| File                         | Content                                                     | Min |
|------------------------------|-------------------------------------------------------------|-----|
| `00-title.tex`               | title, the talk in one picture                              | 2   |
| `01-problem.tex`             | sort-then-double, three routes to fast+correct, rewrite rules in ML compilers/DBs | 6 |
| `02-divide-and-conquer.tex`  | split/combine, call tree, producers/consumers, fusion and deforestation, the example derived | 10 |
| `03-proofs.tex`              | trusted base, three obstacles, `Obj.magic`, shapes and positions, termination proofs, no axioms | 9 |
| `04-results.tex`             | a calculation in Rocq, extracted OCaml, gallery (power, knapsack, MSS), summary | 8 |
| `05-goal.tex`                | work in progress: two ways out of Rocq (OCaml today, direct low-level print as the goal), the goal, representation-changing laws, a closed low-level target, cost model, untrusted search / trusted checking, current status | 10 |

If running long: skip "You Already Trust Rewrite Rules", "What the Textbook
Encoding Extracts To", or "Maximum Segment Sum: Spec and Result".
