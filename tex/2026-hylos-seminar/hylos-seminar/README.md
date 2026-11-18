# Seminar: Program Calculation with Hylomorphisms in Rocq

A one-hour talk for a specialised audience (programming languages, type
theory, proof assistants): about 53 minutes of slides, the rest for
questions. Technical throughout: categorical notation, Haskell for the
calculations by hand, Rocq and OCaml for the mechanisation. It combines this
deck's earlier version (ITP 2025 paper plus the newer library), the general
deck (`../../2026-hylos-general`: the story, the PyTorch hook, the third
homomorphism theorem, ICFP 2016, the false side condition) and the ITP 2025
deck (`../../2025-ITP`: containers, `RecF`, `hylo_def`, the laws).

Three parts: (I) program calculation, the theory and our ICFP 2016 work;
(II) hylomorphisms in Rocq, the ITP 2025 library (joint work with Paviotti
and Vollmer, credited on the title and the Part II divider); (III)
calculating in Rocq, since ITP 2025 (the user's own commits; not credited
as joint). Then **one** slide on ongoing work.

**Ongoing work: one slide, on purpose.** No details or hints about it on
the slides, in the notes or in the backup (no open questions, no "where we
are", no array representations). Do not add any.

## Build

    make                  # highlight code/, then latexmk -lualatex
    make presenter        # main-presenter.pdf: slides left, notes right
    make publish          # ../slides.pdf and ../slides_notes.pdf
    make clean

Same toolchain and style as the general deck: `../template/dcptalk.sty`,
TeX Live 2026 (ltx-talk 0.6+), LuaLaTeX, `pygmentize`; `preamble.tex` is the
general deck's (footer "frame/total", B1, B2, ... for backup frames,
`\slideref`, `\mainblock`, `\hsblock`, `\icfptag`, `\ongoingtag`,
`\excerpt`, `\simplified`), with `\obstacle` renamed `\challenge` (a chip
naming one of the "Three Challenges") and without the demo tag. Run builds
under a memory cap (`systemd-run --user --scope -p MemoryMax=2G -p
MemorySwapMax=0 make`); the `% !LW recipe = make-deck` line in `main.tex`
does this in VS Code.

`make` also writes `main.pdfpc` and `main-notes.md` (60-minute timer).
Present with `pdfpc -n right main-presenter.pdf`, or `pdfpc main.pdf`.

## Speaker notes

Every frame has a `\speakernote`: terse reminders, 1 to 3 bullets of a few
words (`\\` separates bullets), at most one "Q:" line for a likely
question. Never a script, and no click or overlay markers.

## Structure and timing (about 57 min, 50 counted frames)

| File                  | Content                                                                 | Min |
|-----------------------|-------------------------------------------------------------------------|-----|
| `00-title.tex`        | title (Part II credited as joint work); rewrite rules you already trust (SQL pushdown, the PyTorch attention bug: an unchecked side condition); this talk | 3 |
| `01-calculation.tex`  | Part I: programs as algebra (timeline, Backus); initial algebras and catamorphisms; fusion; hylomorphisms (Haskell quicksort, with the library's names `merge`, `split`); the call tree; recursive coalgebras and the three laws; sort-then-double by hand, with its side condition; list homomorphisms as hylos (the cut is a parameter); the third homomorphism theorem; ICFP 2016 (one specification, many parallel programs; what was missing) | 13 |
| `02-rocq.tex`         | Part II, ITP 2025: program calculation in proof assistants (survey); why not just write `hylo`; three challenges; containers; a bad attempt (`Obj.magic`; K and funext); extractable containers (Hedberg, `Cont`/`Pos`/`App`); the quicksort functor; setoids and morphisms; recursive coalgebras (no solution or every solution; `RecF`, `Acc`, finite trees); `hylo_def` (recursion on the proof, the convoy); uniqueness and the proof of fusion; `Initial` (cata and rana as hylos); no axioms, and why; generic for the proofs, clean for the code (genericity proves the laws once; its run-time cost is removed in Part III, not traded) | 19 |
| `03-calculating.tex`  | Part III, since ITP 2025: `Derive` quicksort; fusing a map (`Lmap_merge` is Part I's side condition); quicksort step by step; a false side condition, caught; generic code is not clean code (inlining); closures in the extracted code (the generic `hylo` as a stuck case of a case); the CPS transform of a coalgebra ($\overline{c}$, defined on the syntax of `c`: cases kept, each layer `L` becomes `k L E`; the CPS law as a lemma); CPS hylomorphisms (`⟦a, c⟧^cps`, by recursion on `RecF`, through $\overline{c}$; the theorem `hylo_cps_hylo`, proved by a two-step calculation with the CPS law, then uniqueness); CPS is case-of-case (the commuting conversion, done once in the coalgebra, then reduced by Rocq); quicksort in CPS; usability; knapsack (the problem, dynamorphisms, `reenumerate`, step by step, extracted code); monoid algebras; MSS | 20 |
| `04-wrapup.tex`       | ongoing (one slide); summary; thanks                                    | 2 |
| `05-backup.tex`       | conjugate hylomorphisms; proving hylos correct; terminal coalgebras and finite trees; CPS coalgebras in Rocq (`cps.v`); digits and fast power; the knapsack `Derive`; what changed since the paper | -- |

The thread: a rewrite is only as trustworthy as its side condition (PyTorch;
fusion's side condition by hand in Part I; proved once in Rocq, and a false
one caught, in Part III).

If running long, skip: "Programs as Algebra", "The Third Homomorphism
Theorem", "Program Calculation in Proof Assistants", "Example: the
Quicksort Functor", "Since ITP 2025: Usability", "Maximum Segment Sum",
"Closures in the Extracted Code" (start from "The CPS Transform of a
Coalgebra").

The CPS frames follow `theories/Schemes/HyloCPS.v`. The slides write
$\overline{c}$ (`\cps` in `preamble.tex`) for the CPS coalgebra that
`cps_from_coalg` derives from `c`, so the CPS hylo is indexed by `c`,
`⟦a, c⟧^cps`. The transform `⟨·⟩_k` on the slide is what `cps_build` does:
a `match` becomes a `convoy` (the branch learns its equation), and a layer
`L` becomes `k L E`, with `E : L = c x` proved by `cps_eq`; the CPS law is
`cps_law`. In the library, `hylo_cps` takes any `CCoalg c`, a record whose
CPS law is a field (backup slide "CPS Coalgebras in Rocq"). `hylo_cps_def`
recurses on `RecF`, through `RecF_inv_eq`; `hylo_cps_hylo` is proved there
by induction on `RecF`, and on the slide by the equivalent calculation (the
CPS law, then uniqueness). "Quicksort in CPS" has the shape of the term
`cps_from_coalg` builds for `tsplit` (checked with `Print tsplit_k`,
2026-11-18). Why the ITP code has a closure: the algebra applies the
children function twice, so it is let-bound (`x0`); with the CPS
coalgebra, Rocq's own reduction (`finished`) substitutes it at each known
position before extraction.

## Code snippets

Each listing is a file in `code/`, highlighted into `gen/` by Pygments:
`\rocqblock` (blue), `\ocamlblock` (green), `\badblock` (red: errors and
unsafe code), `\outblock` (grey: Rocq output), `\hsblock` (violet),
`\mainblock` (orange: SQL, Python). Callouts point at
`^\tikzmark{name}^` or `^\hlmark{name}{text}^` marks inside snippets.
`code/rocqlexer.py` adds `Derive`, `arewrite`, `finished` to Pygments' Coq
lexer. A listing that is not verbatim gets `\simplified`.

Haskell (Part I), checked with GHC on 2026-11-18: `hylo-qsort.hs`, `merge2`
of `qsort-calc.hs`, `qsort-side.hs` and `hom.hs` typecheck, and on 300
pseudo-random lists `qsort` sorts, `map double . qsort == hylo merge2
split`, the side condition holds, and `hom` sums with both cuts and rebuilds
the list. `qsort-calc.hs` is a Bird-style calculation; `psort.hs` (ICFP
2016) is skeleton pseudo-code; `third-combiner.hs` an equation.

Rocq, from rocq-hylomorphisms `origin/main` at 72d2303 (2026-10-29; the copy
in `arrays-as-hylos/deps/rocq-hylomorphisms`, built there):

- Verbatim up to dropped implicit binders (section variables shown as
  binders), line breaks and added comments: `cont-class.v`,
  `recf.v`, `hylo-def-full.v` (`hylo_def` verbatim; the body of `hylo`
  elided), `elem-val-eq.v` (with `bool_irrelevance` from
  `Core/Equivalence.v`), `hylo-laws.v`, `map-merge.v`, `qsort-derive.v`,
  `qsort2-derive.v`, `knap-derive.v`, `malg.v`, `malg-fusion.v`,
  `mss.v`, `digits.v`, `qsort-steps.v`, `knap-steps.v` (the goals Rocq
  prints after each rewrite; see the general deck's README).
- `fusion-proof.v`: the proof of `hylo_fusion_l` verbatim, with its
  variables renamed to match `hylo-laws.v`.
- Simplified, and tagged so: `setoid.v`, `initial.v`, `cps.v`, `hylo-ind.v`,
  `gfix.v`. `memo.v` and `reenum.v` drop implicit arguments (said in the
  notes); `qsort-shapes.v` shortens constructor arguments.

Outputs:

- `qsort-extr.ml`, `qsort2.ml`, `knap-arr.ml`, `knap-jump.ml`, `mss.ml`,
  `fastpow.ml`: extracted code, verbatim (`qsort2.ml` re-checked against
  72d2303 on 2026-11-18).
- `itp-qsort.ml`: verbatim extraction of `qsort_times_two` from the ITP
  version of the library (3aaf9ce, `master` of `HYLO/rocq-hylomorphisms`,
  `_build/default/extraction/qsort/qsort.ml`).
- `qsort-negate.txt`: the two goals Rocq 9.3 prints (`Show 1. Show 2.`)
  in part 5 of the general deck's `demo/Demo.v`, compiled against 72d2303
  on 2026-11-18, with the `qsort_negate := ?qsort_negate` context and the
  separators dropped.
- `naive-*` (a direct encoding with dependent positions, Rocq 9.3 and
  extraction), `raw-extr.ml` (`Recursive Extraction` of the unreduced `hylo
  merge tsplit`), `hylo-naive*` and `assumptions.txt` (`Print
  Assumptions`): real outputs.

## Shared with the general deck

Kept identical; check with `python3 check-hylos-sync.py` in `tex/`:
`template/dcptalk.sty`, the code files listed in that script, and the
frames "Rewrite Rules You Already Trust", "Quicksort, Step by Step" and
"Knapsack, Step by Step" (with their speaker notes). The two decks name
things differently: the general deck uses `conquer`, `divide`, `double`;
this one uses the library's `merge`, `tsplit` (`split` in Haskell),
`times_two`.

`images/pytorch-196468.png`: the general deck's screenshot of PyTorch issue
196468 (see its README).
