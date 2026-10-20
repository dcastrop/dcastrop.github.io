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

## Structure and timing (about 50 min of talk, then questions)

| File                       | Content                                                   | Min |
|----------------------------|-----------------------------------------------------------|-----|
| `00-title.tex`             | title, problem / our work                                 | 2   |
| `01-motivation.tex`        | sort-then-double, program calculation                     | 3   |
| `02-recursion-schemes.tex` | Background: squares, quicksort tree, laws, conjugate hylos | 7  |
| `03-challenges.tex`        | why Rocq, challenges and solutions, roadmap               | 3   |
| `04-containers.tex`        | Part I: containers, a bad attempt, decidable UIP, `Cont`  | 7   |
| `05-hylos-in-rocq.tex`     | Part II: recursive coalgebras, `hylo`, laws, no axioms    | 7   |
| `06-calculation.tex`       | Part III: `Derive`, fusion, digits, inlining, usability   | 6   |
| `07-dynamorphisms.tex`     | Part IV: memo tables, knapsack to native arrays           | 5   |
| `08-monoid-algebras.tex`   | Part V: `malg`, `malg_fusion`, MSS                        | 3   |
| `09-wrapup.tex`            | summary, changes, open questions                          | 7   |

If running long: skip "Conjugate Hylomorphisms", "Setoids and Morphisms",
"What Changed Since the Paper", or "Coalgebras and Anamorphisms".

Listings are trimmed to the lines that make the point (at most about 10).
Where real output is shortened or rewritten, the slide says what changed.
