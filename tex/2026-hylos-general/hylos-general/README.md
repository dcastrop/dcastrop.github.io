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
| `00-title.tex`           | title; the hook (rewrite rules you already trust: SQL pushdown, and PyTorch's attention rewrite, whose code matches the bug; then the bug, then the moral, one layer at a time); this talk (the three parts as questions, each saying whose work it is: ICFP 2016 ours, the Rocq library joint with Paviotti and Vollmer; the third promises untrusted search, checked by Rocq) | 2 |
| `01-aop.tex`             | Part I: programs as algebra (timeline with short citations; Backus's abstract), a specification and a program, the law behind it (fold fusion) | 3 |
| `02-hylos.tex`           | divide and conquer (Python, highlighted, then the generic `hylo` and the role of `tag`), the pattern in Haskell, call tree (the least fixed point of `Layer`), fusion and deforestation (the side condition named; `ana` and `cata` labelled; why such rewrites make programs faster), sort-then-double calculated (its side condition on the slide) | 5 |
| `03-homomorphisms.tex`   | list homomorphisms and scheduling, the Java combiner, the third homomorphism theorem, changing the divide step (a loop or a parallel tree) | 4 |
| `04-interlude.tex`       | ICFP 2016: a three-stage parallel sort (feedback, farm, feedback; types carry the structure, a cost model picks it), what was missing (other unverified tools, in the reference line) | 3 |
| `05-mechanising.tex`     | Part II (the divider names the joint work with Paviotti and Vollmer, and the ITP 2025 paper): the gap, and our answer, with the citation | 2   |
| `06-rocq.tex`            | Rocq in a nutshell (CompCert, fiat-crypto); why not just write `hylo`, obstacles; ITP 2025 (generic trees, with `Obj.magic` and foreign code, and why no axioms; termination as recursive coalgebras (recursion on a proof is standard, Bove and Capretta; the proof is about `divide` alone, so well-founded, hence recursive: Capretta, Uustalu, Vene; Adámek, Milius, Moss), first as a picture: a proof tree shaped like the call tree; laws, generic extraction, the price of our choices); since ITP 2025 (what changed, told once; the quicksort calculation with its side conditions, a step that does not apply, the calculation by hand and in Rocq, side by side; the extracted code; then, on its own frame, a law whose false side condition is left as an unprovable goal (`map negate` fused into the divide step with the wrong new divide, `divide` itself, with a counterexample for each goal: the PyTorch failure mode, caught); knapsack, crediting dynamorphisms (Kabanov and Vene; Hinze, Wu, Gibbons) and saying what we add (the memo table as an array, an initial algebra of the table's functor)). Chips (`\obstacle`) say which of the three obstacles a frame raises or solves | 15 | Small chips under the work tag (`\obstacle`) say which of the three obstacles a frame raises or solves | 15 |
| `07-lowlevel.tex`        | Part III: from Rocq to code (today, and the goal: "are we calculating the right programs for real hardware?"); the three open questions first (layout laws, scheduling laws, search for derivations); then the literature on each, each frame with a chip naming its question (`\openquestion`): trees without pointers (Gibbon; the sum on the buffer), packed traversals as hylos, Farzan and Nicolet's nested loops (then the same with hylos), untrusted search (with the PyTorch callback); where we are (laws that add or remove a buffer are under "not yet", without committing to one design) | 10 |
| `08-wrapup.tex`          | summary, ending on the thesis (optimisation as a verified calculation, not an untrusted compiler transformation); thanks | 1 |
| `09-backup.tex`          | backup, after the thanks (B1 to B16, not in the count): why hylomorphisms matter, where they come from, the third theorem and after, homomorphisms as divide and conquer, ICFP 2016 in full (skeletons and their types, reforestation and cost, splitter and merger farms), the survey of program calculation in proof assistants (approach and limits), generic definitions and clean code (genericity proves the laws once; its run-time cost is removed, not traded), ITP 2025's extraction, the quicksort and knapsack steps (shared with the seminar) and knapsack's laws, associative combiners, what each approach trusts, packed traversals; written for specialists | -- |

The thread through the talk: a rewrite is only as trustworthy as its side
condition. PyTorch's attention rewrite bug (an unchecked side condition)
opens; Part I names the side condition of fusion and shows
sort-then-double's, checked by hand; Part II shows it proved in Rocq, and a
false one caught ("A False Side Condition, Caught"); "Untrusted Search,
Trusted Checking" comes back to it as the same failure mode (not a claim
that our framework handles tensors).
Speedups are argued, not measured: fewer passes, no intermediate data, as
in compilers (GHC's fusion rules, kernel fusion, database pushdown).

The footer shows "frame/total", counting frames, not overlays. The title,
Part dividers, "Thank you!" and the backup divider are not numbered or
counted; backup frames are B1, B2, ... (`preamble.tex`: `\titleframe` and
`\partframe` wrappers, `talknofooter`, `\backuppart`).

Frames of the ICFP 2016 work and of the ongoing work carry a tag in the
top-right corner: "ICFP 2016" or "ongoing" (`\icfptag`, `\ongoingtag` in
`preamble.tex`). The Rocq library frames have none: the joint work (ITP
2025, with Paviotti and Vollmer) is credited on the Part II divider and on
"The Gap". The chips (`\obstacle`, `\openquestion`) sit in the corner, or
under the tag when there is one. What changed since ITP 2025 is told once,
on "Since ITP 2025" (ITP 2025's extracted quicksort is in the backup).

References are a small line at the bottom of the slide (`\slideref`).
`\excerpt<n>{quote}{source}` shows a quotation over the slide on step `n`
(Backus's abstract on "Programs as Algebra", verbatim from the CACM
printing, with "[...]" for cuts and the bold marked as added); `\tlcite` adds a short grey citation inside a timeline box.

The talk has no live demo (since 2026-11-17): "A Calculation in Rocq",
"Quicksort, Step by Step" and "Quicksort: What Comes Out" show the steps.
`\demotag` (a red "DEMO" tag) is still in `preamble.tex`, and the backup
slide "Demo: Supporting Material" says how to run it, in case.

If running long, skip: "Where Hylomorphisms Come From",
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
files `rocqlexer.py`, `qsort-steps.v`, `knap-steps.v`, `naive-cont.v`,
`naive-eq.txt`, `cont-class.v`, `recf.v`, `hylo-def.v`, `hylo-laws.v`,
`malg.v`, `malg-fusion.v`, and the frames "Quicksort, Step by Step" and
"Knapsack, Step by Step" (both in `09-backup.tex`, with the library's real
names). Elsewhere the general deck uses the talk's names, not the library's
(`conquer` for `merge`, `divide` for `tsplit`, `double` for `times_two`,
`double_pivot` for `natural (nt_shape id times_two)`): `qsort2-derive.v`,
`qsort2.ml`, `raw-extr.ml`, `naive-extr.ml` and `itp-qsort.ml` differ from
the seminar's. Extracted listings are real output with identifiers renamed
(their speaker notes say so); the calculation slides say "(simplified)".

`code/qsort-wrong.txt` is real Rocq output: `demo/Demo.v` with its `Fail`
removed, compiled against the post-ITP library (2026-11-17).
`code/qsort-negate.txt` is the goals Rocq prints in part 5 of `demo/Demo.v`
(a false side condition), renamed to the talk's names, labelled "goal 1"
and "goal 2", with the `rewrite` moved into the slide's sentence.

`images/pytorch-196468.png`: a screenshot (headless Chrome, 2026-11-17) of
the public issue https://github.com/pytorch/pytorch/issues/196468, cropped
to its title, labels and description; shown on "Rewrite Rules You Already
Trust" as a real case of a fusion rule missing its side condition (the
softmax axis). The issue was open, with a fix PR (#200011) pending.

## Demo

Not part of the talk; kept in case. `demo/Demo.v` repeats the quicksort
calculation (the library's `examples/QSort.v`) for stepping through live,
with a wrong step that Rocq rejects, `Extraction` and `Print Assumptions`.
See `demo/README.md`.
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
