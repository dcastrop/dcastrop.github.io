# Talk: Hylomorphisms: From the Algebra of Programming to Certified Code

A one-hour seminar for computer scientists outside programming languages
(machine learning, logic, security, AI): 50 minutes of talk, 10 of buffer
for questions and slower explanations. It presents the ITP 2025 paper
(rocq-hylomorphisms) inside a longer story: programs as algebra, divide and
conquer (hylomorphisms) and the third homomorphism theorem; laws for
parallelism (ICFP 2016); the gap in mechanised program calculation;
hylomorphisms in Rocq (ITP 2025, then what came after); and the ongoing move
to low-level code.

Code over diagrams, but code this audience reads: each idea first in Python
(plus SQL, Java, C), then Haskell, introduced gently ("The Same Fold, in
Haskell", with a Python-to-Haskell phrasebook; "The Same, in Haskell", which
adds only `.` and `fmap`) and used for the calculations; Rocq and OCaml for
the mechanisation.
No functional-programming notation on the slides: "divide" and "conquer"
(coalgebra, algebra, named once), "associative combiner" (monoid), "same
results" equality (setoids), "generic trees" (containers); the jargon is in
the speaker notes.

## Build

    make                  # highlight code/, then latexmk -lualatex
    make clean
    make demo             # check demo/Demo.v against the library (see below)

VS Code (LaTeX Workshop): the first line of `main.tex`, `% !LW recipe =
make-deck`, makes it build with `make` instead of its default `latexmk -pdf`
(which uses pdfLaTeX, has no `TEXINPUTS`, and skips the highlighting). The
`make-deck` recipe is defined in the workspace's `.vscode/settings.json`
(gitignored): a tool running `systemd-run --user --scope --quiet -p
MemoryMax=2G -p MemorySwapMax=0 make -C %DIR%`, appended to the default
tools and recipes. Edits under `code/` rebuild on the next save of a `.tex`
file, or with "Build LaTeX project".

Same toolchain and style as the seminar (`../template/dcptalk.sty`, TeX Live
2026, LuaLaTeX, `pygmentize`). `make` also writes `main.pdfpc` and
`main-notes.md` from the `\speakernote`s (60-minute timer). Notes are
terse cues, not a script: `\\` separates bullet points. They are reminders
and pointers only, with no click markers.

## Slides with notes

    make presenter        # main-presenter.pdf
    make publish          # ../slides.pdf and ../slides_notes.pdf

`main-presenter.pdf` puts each slide on the left half of a double-width page
and its notes on the right (`../template/make-presenter.py`, from
`main.notes`). Present with `pdfpc -n right main-presenter.pdf`, or read it
in any viewer.

`../slides.pdf` is linked from the talks page (through `latex:` in
`_talks/`); `../slides_notes.pdf` is published next to it but not linked.

## Structure and timing (50 min of talk, 10 min buffer)

Three parts, as in the abstract: program calculation; mechanising it (the
ITP 2025 library and what followed); mechanising *low-level* program
calculation (ongoing). The ICFP 2016 work is the end of Part I, not a
separate interlude.

| File                     | Content                                                                 | Min |
|--------------------------|-------------------------------------------------------------------------|-----|
| `00-title.tex`           | title, this talk                                                        | 1   |
| `01-aop.tex`             | Part I: rewrite rules you already trust, programs as algebra (timeline with short citations; Backus's abstract), a specification and a program, the law behind it (fold fusion) | 4 |
| `02-hylos.tex`           | divide and conquer (Python, highlighted, then the generic `hylo` and the role of `tag`), the pattern in Haskell, call tree, where hylomorphisms come from, why they matter, fusion (after and before) and deforestation, sort-then-double calculated | 6 |
| `03-homomorphisms.tex`   | list homomorphisms and scheduling, the Java combiner, the third homomorphism theorem, homomorphisms as divide and conquer, changing the divide step, extensions | 5 |
| `04-interlude.tex`       | ICFP 2016: a three-stage parallel sort (feedback, farm, feedback), skeletons and their types, reforestation and cost, what was missing (other unverified tools) | 5 |
| `05-mechanising.tex`     | Part II: program calculation in proof assistants, the gap               | 4   |
| `06-rocq.tex`            | why not just write `hylo`, obstacles; ITP 2025 (generic trees, termination, laws, proofs vs code, generic and ITP extraction, the price of our choices); since ITP 2025 (demo and the slides it covers, knapsack, associative combiners) | 15 |
| `07-lowlevel.tex`        | Part III: two ways out of Rocq, Gibbon and packed traversals, Farzan and Nicolet's nested loops, the same story with hylos, why mechanised, representation-changing laws, untrusted search, where we are | 10 |
| `08-wrapup.tex`          | summary, thanks                                                         | 1   |

Frames that belong to one piece of work carry a tag in the top-right
corner: "ICFP 2016", "ITP 2025", "since ITP 2025", or "ongoing"
(`\icfptag`, `\itptag`, `\sincetag`, `\ongoingtag` in `preamble.tex`). The
"Proofs or Code?" table marks in orange the code costs fixed since ITP 2025.

References are a small line at the bottom of the slide (`\slideref`).
`\excerpt<n>{quote}{source}` shows a quotation over the slide on step `n`
(Backus's abstract on "Programs as Algebra", verbatim from the CACM
printing, with "[...]" for cuts and the bold marked as added); `\tlcite` adds a short grey citation inside a timeline box.

Slides the live demo covers ("A Calculation in Rocq", "Quicksort, Step by
Step", "Quicksort: What Comes Out") carry a red "DEMO" tag in the top-right
corner instead of a work tag (`\demotag`); skip them after a good demo.

If running long, skip: "Extensions", "Where Hylomorphisms Come From",
"Generic Code Is Not (Always) Clean Code", "Dynamic Programming: Knapsack", "Laws
That Change Representation", "Untrusted Search, Trusted Checking".

## Code snippets

Boxes by language: Rocq blue, OCaml green, Rocq errors red, Rocq output
grey (`dcptalk.sty`); mainstream languages orange and Haskell violet
(`\mainblock`, `\hsblock` in `preamble.tex`). A block that is not verbatim
gets `\simplified` (a grey "(simplified)" tag). Python up to the divide and
conquer slide, then one switch to Haskell.

- Python (`*.py`, except the lexer `rocqlexer.py`): `sumsq.py`, `fold.py`,
  `fold-fusion.py`, `qsort-direct.py` (with `\tikzmark`s for the
  highlights), `hylo.py`, `packed-tree.py`, `packed-hylo.py` run as shown
  and were tested (quicksort against `sorted` on random lists, fold fusion,
  the packed sum). `hylo` takes `conquer` first, as in Haskell and Rocq.
  `torch-fusion.py` is PyTorch (not run). `packed-hylo.py` is our reading of
  packed traversals, not Gibbon's formulation.
- Haskell (`*.hs`): `hylo-qsort.hs`, `hom.hs` and `conquer2` in
  `qsort-calc.hs` typecheck with GHC and were tested (qsort sorts, the
  fused doubling equals sort-then-double, `hom` sums and keeps order).
  `qsort-calc.hs` and `psort-calc.hs` are Bird-style calculations
  (`=  { law }` between terms); `listhom.hs` states an equation;
  `psort.hs` and `psort2.hs` are skeleton pseudo-code. The third
  homomorphism theorem is shown as a diagram, with the precise statement
  in the speaker notes. The calculation in `psort-calc.hs` was checked on small inputs
  (folding the sorted chunks of the cut tree with `merge` equals mergesort
  for several chunk sizes); it relies on `merge` being associative and
  commutative on sorted lists.
- `sql-pushdown.sql`: predicate pushdown, a standard optimiser rewrite.
- `digits.java`: a Java parallel-stream reduction (a local `record`: Java
  16+); the combiner obeys the `Stream.reduce` contract (associative,
  identity, compatible with the accumulator). Checked on JDK 21: the
  parallel result equals the loop's.
- `packed-sum.c`: a hand-written sketch of a traversal over a serialised
  tree, not Gibbon's output. `nested-loop.c`: the shape of the loop nests in
  Farzan and Nicolet (PLDI 2019).
- `itp-qsort.ml`: verbatim extraction of `qsort_times_two` from the ITP
  version of the library (rocq-hylomorphisms 3aaf9ce, the Rocq 9 port of
  the camera-ready).
- `assumptions-itp.txt`: the first line of the seminar's `assumptions.txt`
  (`Print Assumptions hylo_fusion_l`).
- `naive-eq.v`: the seminar's, without its "Now what?" comment.
- `hylo-naive.v`, `hylo-naive-err.txt`: the generic `hylo` as a plain
  `Fixpoint`, and Rocq 9.3's verbatim error.
- The other Rocq and OCaml snippets are shared with the seminar (below), and
  checked as described in its README; `knap-simple.ml` is the extracted
  knapsack loop, simplified (`max_list`, plain arithmetic, no `Uint63`).

Shared with the seminar, and kept identical (check with
`python3 check-hylos-sync.py` in `tex/`): `template/dcptalk.sty`, the code
files `rocqlexer.py`, `qsort2.ml`, `qsort-steps.v`, `knap-steps.v`,
`naive-cont.v`, `naive-extr.ml`,
`naive-eq.txt`, `cont-class.v`, `recf.v`, `hylo-def.v`, `hylo-laws.v`,
`raw-extr.ml`, `malg.v`, `malg-fusion.v`, the quicksort `Derive`
(`qsort2-derive.v`, plus two `\tikzmark`s here), and the frames "Quicksort,
Step by Step" (plus a `\demotag` here) and "Knapsack, Step by Step".

## Demo

`demo/Demo.v` repeats the quicksort calculation (the library's
`examples/QSort.v`) for stepping through live, with a wrong step that Rocq
rejects, `Extraction` and `Print Assumptions`. See `demo/README.md`.
`make demo` compiles it against the post-ITP library under a memory cap.

## Sources for the survey slides

- Third homomorphism theorem: J. Gibbons, JFP 6(4), 1996 (conjectured by
  Bird, proved by Meertens in 1989, as the paper says).
- ICFP 2016 numbers ("Reforestation, Then Choose by Cost"): the paper's cost
  model estimates for quicksort on 1000 lists of 3,000,000 elements, 24
  cores (42602.72, 32179.77 and 27846.13 ms), not measurements.
- Gibbon / LoCal: Vollmer et al. ECOOP 2017, PLDI 2019; Koparkar et al. ICFP
  2021; Singhal et al. (Marmoset) ECOOP 2024.
- Farzan and Nicolet, PLDI 2019 (extended version: arXiv 1904.01031): Thm
  4.7 (modularity), Thm 5.3 (lifting), ParSynt; joins bounded-checked with
  Rosette, most also proved in Dafny; the loop-to-recurrence translation is
  not verified.
- Proof-assistant survey and its "But" column: the related work of the ITP
  2025 paper, plus Emoto et al. ITP 2014 and Loulergue et al. IJPP 2017
  (SyDPaCC).
- "Where We Are": arrays-as-hylos at 9009e80 (2026-10-29). Materialising
  writes into a buffer is defined, with no laws yet; the exactly-once section
  is empty. Never name the array representations on the slides.
