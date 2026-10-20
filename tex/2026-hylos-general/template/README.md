# dcptalk: an ltx-talk style

The look of the 2025-ITP and 2026 seminar decks (`~/dcastrop.github.io/tex/`)
as a package for `ltx-talk` (tested with 0.6.10, TeX Live 2026), with
tagging on. `example.tex` uses every
feature; build it with `lualatex example` (twice, for the callouts).

    \DocumentMetadata{lang = en-GB, pdfstandard = ua-2, tagging = on}
    \documentclass{ltx-talk}
    \usepackage[fonts = lm, codedir = gen]{dcptalk}

Put this directory on `TEXINPUTS` (e.g. `TEXINPUTS=../template//:`).

## Options

- `fonts`: `lm` (default; Latin Modern Sans text, as the old pdfLaTeX
  decks), `paper` (as the LIPIcs paper: Latin Modern Roman text, Latin
  Modern Sans bold frame titles), `fira` (Fira Sans), or `default`
  (ltx-talk's fonts). Code is JetBrains Mono (else Fira Mono). Latin Modern
  uses its optical sizes.
- `math`: `auto` (default; `lm` with `fonts = paper`, else `cmsans`), `lm`
  (Latin Modern Math, as the paper), `cmsans` (New Computer Modern Sans
  Math, the OpenType form of the `sansmathfonts` maths of the old decks), or
  `fira`.
- `footer = false` (default): no footer. `footer = true`: date, author,
  title, institute, frame number, total frames.
- `titlebar = true` (default): a vertical bar left of the frame title, as
  in the ITP deck; colour `dcptitlebar` (cyan). It patches an ltx-talk
  internal (`\__talk_frame_title:n`), so check it after ltx-talk updates.
- `codedir = gen`: where the highlighted code snippets are.

## What it provides

| Command                                   | Use                                     |
|-------------------------------------------|-----------------------------------------|
| `\titleframe{title}{authors}{venue}`      | title slide                             |
| `\authorblock*{name}{email}{logo}{inst}`  | one author (`*`: speaker, underlined)   |
| `\partframe{Part I}{Title}`               | sticky-note divider slide               |
| `sticky`, `bluebox`, `greenbox`, `infobox`, `greybox` | shadowed boxes (yellow, blue, green, red, grey) |
| `\rocqblock`, `\ocamlblock`, `\badblock`, `\outblock` `[opts]{file}` | code from `<codedir>/<file>.tex` in a blue/green/red/grey box |
| `\popup<2>(x,y)[width][box]{...}`         | a box shown over the slide on an overlay |
| `\callout<2->{x,y}{text}{mark1, mark2}`   | golden label at (x,y) cm, arrows to `\hlmark` boxes or `\tikzmark`s |
| `\speakernote{...}`                       | speaker note for the frame (not on the slides) |
| `\slideref{...}`                          | small reference at the bottom of the slide |
| `\Put(x,y){...}`, `\embf`, `\highl`, `\mathcolorbox`, `\redbf` | as in the old decks |
| TikZ styles `box`, `hot`, `note`; `tikzcd` with `\&` | diagrams |

Code snippets: `pygmentize -f latex -O escapeinside=^^ file.v > gen/file.v.tex`;
inside the snippet, `^\hlmark{name}{text}^` highlights `text` in a box
that `\callout` points at (the arrow ends at the box's edge, at the same
place on every overlay); `^\tikzmark{name}^` marks a bare point instead.
If a label would sit on a full-width code box, narrow the box:
`\rocqblock[width = .8\textwidth]{file}`.
Frames that include code must be `frame*`.

Page: `lightgray!30`.

## Notes

- Every `tikzpicture`/`tikzcd`/`\includegraphics` needs `alt = {...}`;
  callouts and references set it from their text.
- A paragraph left open before an `onlyenv` (or at the end of a frame) puts
  the next frame inside it in the tag tree; end it with `\par`.
- Reveal boxes (code blocks, `sticky`, ...) with `onlyenv`, not `uncover`:
  `uncover` hides the text but the box's shading still shows.
- Spacing: `\parskip` and list spacing are widened (tagged lists are
  `list`/`block` template instances; see the `spacing` part of the style).
- `minted` is not used: its `latexminted` 0.6.0 helper fails on Python 3.14.
- Under LuaLaTeX the double brackets are `\lBrack`/`\rBrack`
  (`\llbracket` is undefined). Banana brackets
  (`\llparenthesis`/`\rrparenthesis`) exist in NewCM Sans Math but not in
  Latin Modern Math or Fira Math; build them as
  `\mathopen{(\mkern-3.5mu|}`.

## Speaker notes

ltx-talk has no notes yet (upstream issue #156). `\speakernote{text}` inside
a frame writes the text to `<job>.notes` with the page it lands on (once per
overlay). Then

    python3 make-notes.py <job> [--duration MINUTES]

writes `<job>.pdfpc`, which pdfpc reads for its presenter console (notes
are Markdown; `--duration` sets its timer), and `<job>-notes.md`, a notes
sheet with one entry per frame. The slides PDF is unchanged. `\code`,
`\emph`, `\textbf` become Markdown; other macros are passed through.
