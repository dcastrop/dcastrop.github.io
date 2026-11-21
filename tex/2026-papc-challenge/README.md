# We Have a Challenge for You! (PaPC)

The first challenge for the Proofs and Programs Club @ RHUL
(<https://papc-rhul.github.io/>): a verified relational algebra library in
Lean, by hand. A gentle presentation (`slides.pdf`), and one PDF per
level, each in its own directory.

A website version, with more theory, questions and exercises, lives in
`/papc-challenge/` at the root of this repository (see its
`_src/README.md`). It keeps the numbering of these PDFs: a change to a
level's content here may need the same change there.

**Unlisted.** No `_talks` entry; `_config.yml` sets `sitemap: false` for
`tex/2026-papc-challenge` (and everything under it), so the PDFs are
reachable only by their URLs:

- <https://dcastrop.github.io/tex/2026-papc-challenge/slides.pdf>
- `https://dcastrop.github.io/tex/2026-papc-challenge/level-<id>/level-<id>.pdf`,
  for `<id>` in `1`, `2f`…`5f`, `2t`…`5t`, `6`…`9`.

The PDFs link to each other with absolute URLs (`\challengeurl` in
`common/preamble.tex`), so a downloaded copy still links to the rest.

## Layout

| Path              | What |
|-------------------|------|
| `papc-challenge/` | the presentation: title; "We welcome your challenges!"; the challenge in plain words; why prove it; the map of the levels (linked); how to start. It has no theory and no code. Published as `slides.pdf` |
| `level-1/`        | everyone starts here: install Lean and create a project; what a table is; a first proof by `rfl`; choose a track |
| `level-2f/`…`level-5f/` | **programs track**, follows FPIL in order: `select` (FPIL 1.5–1.6); `project`, `product`, `union` (1.6); `dedup`, `diff`, `joinOn`, comparing rows (3.2, 3.5.3); named columns and a query language (1.4, 3.5.5, 7.1–7.3) |
| `level-2t/`…`level-5t/` | **proofs track**, follows TPIL in order: selection and union as `∧`/`∨`, laws 1–3 (3.1, 3.3); difference, `¬` and classical logic, law 4 (3.3, 3.5); products, images, `∀`/`∃`, tactics, law 5 (4.1, 4.4, 5.2); induction on lists (5.6–5.8, 7.6) |
| `level-6/`        | the tracks meet (needs 5F and 5T): the list programs compute the operators on tables, so every law holds for lists (FPIL's induction interlude) |
| `level-7/`, `level-8/` | the laws for every query; a correct optimiser (lean on TPIL 7, 8 and 10) |
| `level-9/`        | fast joins (leans on FPIL 3.4, 8), then the stretch goals. Can be done before or after 7 and 8 |
| `common/`         | `preamble.tex`, `links.tex`, `images/`, `deck.mk` (build rules), shared by every deck |
| `template/`       | `dcptalk.sty`, as in the 2026 hylos decks |

Each level's directory holds `main.tex`, `code/` (its Lean and SQL
snippets), a two-line `Makefile`, and the published `level-<id>.pdf`.

Keep:

- **Tracks.** After Level 1, two tracks that can be done in either order
  or side by side: F (programs, FPIL chapter by chapter) and T (proofs,
  TPIL chapter by chapter). They meet at Level 6. After it, 7 → 8 and 9
  are independent. The presentation's map draws this graph.
- **Each level's shape**: a title page (the club, not a speaker; no date;
  links to the levels before and after, and to the whole challenge);
  "Level n at a Glance" (build, prove, what to learn first, with linked
  book sections); a part "Theory, on Paper"; a part "Lean, on Your
  Computer". Level 1 adds a part "Before You Start" (install Lean, create a
  project). Every frame's tag says theory (orange) or Lean (blue).
- **Theory**: easy in tone, 100% formal. Numbered definitions, facts and
  laws in `\defn` boxes, with short proofs ending in `\proofend`. Numbers
  carry the level: Definition 2F.3, Fact 3T.3, Theorem 6.2. Laws keep
  global numbers (Law 1 to Law 11). Levels 1 to 4 use two-column tables,
  $R \subseteq D_1 \times D_2$; named columns arrive at Level 5F.
  Definition 1.2 (a list *represents* a table) is what Level 6 proves the
  programs respect.
- **Lean**: the programs track works on `List α`, with conditions to
  `Bool`, and checks by `#eval` and `rfl` (numbers only, never string
  equality). The proofs track works on `Sets.Table α := α → Prop` (in
  `namespace Sets`, so both tracks fit in one file), with conditions as
  propositions, and laws stated as `↔` for each row. Level 6 joins them
  with `toTable l := fun t => t ∈ l`.
- The code in `level-*/code/*.lean` has **not been type-checked** (no Lean
  on this machine): check it before the sessions. Goal statements in
  Levels 7 to 9 (`goal.lean`) are sketches, marked "(sketch)".
- Every level stays doable by hand; no slide about tools. No overlays, no
  speaker notes. Content centred and at normal size; a crowded frame is
  split in two rather than shrunk (the user found cramped frames awful).
  Long text in a sticky with `halign = center` wraps badly: use the
  default alignment there.

## Build

    make            # every deck, one after another, and publish each
    make -C level-2t publish   # one deck

Run under a memory cap: `systemd-run --user --scope -p MemoryMax=2G -p
MemorySwapMax=0 make`. Never build decks in parallel. Toolchain: TeX Live
2026, LuaLaTeX, `pygmentize` with its `lean4` lexer. Tagged PDF/UA-2;
every picture has alt text; tables mark their header row (`\headerrow`).
LaTeX notes: no `amsmath` (use `array` to align proofs), double brackets
are `\lBrack`/`\rBrack`.

## Links

`common/links.tex` holds every book link:
`\deflink{key}{book and number}{title}{url}`, read with `#` and `_` as
ordinary characters; `\lnk{key}` prints it. Section numbers, titles and
URLs were taken from the books' own tables of contents on 2026-11-19
(FPIL and TPIL at Lean 4.33, MIL v4.34.0); the links added on 2026-11-20
(FPIL 1.2, 1.3, 3.2; TPIL 3.3, 3.5, 4.4) were checked the same way. TPIL
numbers its sections by their order in each chapter. Every page returned
HTTP 200. Reference alt texts drop the URLs.

The database references point to Abiteboul, Hull and Vianu, *Foundations
of Databases* (free at <https://webdam.di.ens.fr/Alice/>; chapter titles
checked there on 2026-11-19: 3 The Relational Model, 4 Conjunctive Queries,
5 Adding Negation: Algebra and Calculus, 6 Static Analysis and Optimization,
whose section 6.1 covers rewriting with algebraic equivalences and
implementing joins). Garcia-Molina, Ullman and Widom is not cited: its
section numbers differ between printings.

`common/images/papc-logo.png` is the club's logo, from its website.
