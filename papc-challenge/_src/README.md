# The PaPC challenge website

The website version of the club's first challenge (a verified relational
algebra library in Lean), built from `_src/` into plain static pages:

    papc-challenge/
      index.html, level-*.html, laws.html   generated: do not edit
      assets/                               challenge.css, challenge.js, logo
      _src/                                 sources (Jekyll skips "_" folders)
        build.py                            the generator (Python 3, stdlib only)
        pages/*.txt                         one file per page
        links.tsv                           book links, copied from the decks

## Where it lives, and how to remove it

For now it is **unlisted** on dcastrop.github.io, at
<https://dcastrop.github.io/papc-challenge/>. Nothing links to it. Every page
has `<meta name="robots" content="noindex">`, and `_config.yml` keeps the
folder out of `sitemap.xml`.

To remove it: delete this folder, and the `papc-challenge` entry under
`defaults` in `_config.yml`. Nothing else refers to it.

To move it to the club's website (papc-rhul.github.io, also Simple.css):
copy the whole folder there (all links inside it are relative), set
`HIDDEN = False` in `build.py`, rebuild, and link to it from the club's page.
The PDF links point to `PDF_BASE`, in `build.py`; change it if the PDFs move
too.

## Build

    python3 papc-challenge/_src/build.py

The build writes the pages next to `_src`. It stops on an unknown link key,
container, directive or level, and when an internal link points to a page or
anchor that does not exist. Commit the generated pages: GitHub Pages serves
them as they are.

The pages load Simple.css 2.3.7 (as on the club's site) and KaTeX 0.16.11
from jsDelivr. KaTeX renders the maths in the browser. Lean and SQL are
highlighted at build time.

## Content and structure

Each level page follows the PDFs: at a glance (what you build, what you
prove, what to read), milestones, a part "Theory, on paper", and a part "Lean,
on your computer". Level 1 also has a part "Before you start".

- **Numbering** matches the PDFs: definitions, facts, exercises and laws keep
  their numbers. Material that exists only on the website continues after
  them: Exercise 2F.6 onwards, Fact 4T.5 onwards, and so on.
- **Questions** (2F.A, 2F.B, …) are on paper, with answers that open on
  click. **Exercises** are in Lean, with hints, never full solutions. Some
  exercises are "on paper" because the PDFs had them so (3F.2, 4T.3).
- **Milestones** are ticked by the student. Ticks live in the browser's
  `localStorage` only (key `papc-challenge:v1`), and the map on the front page
  shows them. Changing the number of milestones of a level renumbers its
  keys, so students may lose ticks: prefer adding at the end.
- The track graph is fixed in `build.py` (`LEVELS`, `level_map`): after
  Level 1, 2F→5F (FPIL) and 2T→5T (TPIL), side by side; both lead to Level 6;
  then 7→8 and 9.
- **The Lean code is not type-checked.** It copies the decks and adds more
  exercises in the same style. Check it with Lean before the sessions. Code
  blocks marked "Sketch" (Levels 7 to 9) show a theorem's shape; the student's
  own types decide its details.
- Every level stays doable by hand. Pages name the club, not a speaker.

## The markup of `pages/*.txt`

Blocks are separated by blank lines.

| Write | For |
|---|---|
| `## Title`, `### Title` | headings (`## Title {#id}` sets the id) |
| `- item`, `1. item` | lists (no blank lines inside a list) |
| ```` ```lean caption ```` … ```` ``` ```` | code: `lean`, `sql` or `text`; "(sketch)" in the caption adds a Sketch label |
| `$…$`, `$$…$$` | maths (KaTeX); `$$` blocks may span lines |
| `` `code` ``, `**bold**`, `*italic*`, `[text](url)` | inline |
| `[[2f]]`, `[[2f#law-1\|text]]`, `[[laws\|text]]` | links to a level (shown as "Level 2F"), an anchor, or a page |
| `[@fpil-data]` | a book section, from `links.tsv` |
| `Table: caption` then `\| a \| b \|` rows | tables; `\|--:\|` aligns right |
| `@club Member Attended` | the club's tables, side by side |
| `@toc`, `@map`, `@index`, `@pdfs`, `@reset` | page contents, level map, index of boxes, PDF list, the "clear ticks" button |
| `<…>` at the start of a block | raw HTML, up to the next blank line (the SVG trees of Level 8) |

Containers open with `::: kind …` and close with `:::`, and can nest:

| Container | Renders |
|---|---|
| `::: box Definition 2F.1 (Condition)` | a definition, fact, theorem or law box. The first word sets the colour (Definition, Law, else a fact); the id is `definition-2f-1`, `law-3`, … and the box joins the index on the laws page |
| `::: proof` | a proof, ending in ∎ (`::: proof Proof of X` changes the label) |
| `::: ex 2F.1 lean Title` | an exercise (`lean`, `paper` or `stretch`); id `ex-2f-1` |
| `::: q 2F.A Title` | a question on paper; id `q-2f-a` |
| `::: hint`, `::: hint Hint 2`, `::: answer` | collapsed details |
| `::: note Title`, `::: callout` | a highlighted note; the front page's welcome box |
| `::: part theory Title` | a part: `theory`, `lean`, `setup` or `beyond` |
| `::: glance` | lines `build: …`, `prove: …`, `learn: what \| [@ref] · [@ref]` |
| `::: milestones` | a list of `- milestone` lines |
| `::: row`, `::: figure Caption` | side by side; a figure with a caption |
