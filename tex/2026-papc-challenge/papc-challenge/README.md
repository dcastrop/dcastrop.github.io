# We Have a Challenge for You! (PaPC, 19 November 2026)

The first challenge for the Proofs and Programs Club @ RHUL
(<https://papc-rhul.github.io/>): a verified relational algebra library in
Lean, by hand. The deck is lecture notes, not a lecture: every frame reads
on its own, and the whole deck can be shown in about 5 minutes.

**Unlisted.** No `_talks` entry; `_config.yml` sets `sitemap: false` for
`tex/2026-papc-challenge`, so the PDFs are reachable only by their URL:
<https://dcastrop.github.io/tex/2026-papc-challenge/slides.pdf>.

Keep:

- The title page names the club, not a speaker.
- No part dividers; each title states the frame's point, and the titles
  read as a story.
- Every level stays doable by hand; no slide about tools.
- No overlays and no speaker notes (the PDF is read as notes).
- Content centred and at normal size; no top-aligned frames with spacing
  hacks, no small two-column boxes (the user found those awful).
- Lean code: goal statements only (`code/goals.lean`), not type-checked,
  marked "(sketch)".

## Structure

| File               | Frames |
|--------------------|--------|
| `00-challenge.tex` | title; databases rewrite queries using laws (SQLancer); the challenge (a table: level, build, prove) |
| `01-tables.tex`    | Level 1: relations as sets of rows (the club's tables); the Lean it needs |
| `02-queries.tex`   | Level 2: a crash course on relational algebra (the six operators; rows as functions on a schema, the named perspective; each operator's schema rule and row rule; derived operators: intersection, theta join, natural join, semijoin, division; examples; what the algebra can and cannot express; SQL as algebra), then queries as data and the Lean it needs |
| `03-laws.tex`      | Level 3: laws of selection; projection and join (and a trap); lists, bags, sets; the Lean they need |
| `04-optimiser.tex` | Level 4: query trees rewritten by the laws; the Lean it needs |
| `05-joins.tex`     | Level 5: hash joins equal to the definition (Codd 1970); the Lean they need |
| `06-beyond.tex`    | the goals as Lean theorems; design decisions; stretch goals; the Lean at a glance; earlier work in Coq |
| `07-yours.tex`     | we welcome your challenges; closing |

Each "Level n Needs ..." frame is a `\leanframe` (preamble): a table of
what you can do when ready, each row with its book sections, linked
(`\rds{keys}`).

## Build

    make            # highlight code/, then latexmk -lualatex
    make publish    # ../slides.pdf

Run under a memory cap: `systemd-run --user --scope -p MemoryMax=2G -p
MemorySwapMax=0 make`. Same toolchain as the 2026 hylos decks
(`../template/dcptalk.sty`, TeX Live 2026, LuaLaTeX, `pygmentize` with
its `lean4` lexer). Tagged PDF/UA-2; every picture has alt text; tables
mark their header row (`\headerrow`).

## Links

`links.tex` holds every book link: `\deflink{key}{book and number}{title}{url}`,
read with `#` and `_` as ordinary characters; `\lnk{key}` prints it. Section
numbers, titles and URLs were taken from the books' own tables of contents
on 2026-11-19 (FPIL and TPIL at Lean 4.33, MIL v4.34.0), and every page
returned HTTP 200 then. Reference alt texts drop the URLs.

The database references point to Abiteboul, Hull and Vianu, *Foundations
of Databases* (free at <https://webdam.di.ens.fr/Alice/>; chapter titles
checked there on 2026-11-19: 3 The Relational Model, 4 Conjunctive Queries,
5 Adding Negation: Algebra and Calculus, 6 Static Analysis and Optimization,
whose section 6.1 covers rewriting with algebraic equivalences and
implementing joins). Garcia-Molina, Ullman and Widom is not cited: its
section numbers differ between printings.

`images/papc-logo.png` is the club's logo, from its website.
