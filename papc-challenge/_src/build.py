#!/usr/bin/env python3
"""Build the PaPC challenge website.

    python3 papc-challenge/_src/build.py

Reads _src/pages/*.txt (the content, in the small markup described in
_src/README.md) and writes the pages next to _src: index.html,
level-*.html and laws.html. Python 3 standard library only.
"""
import html
import re
import sys
from pathlib import Path

SRC = Path(__file__).resolve().parent
OUT = SRC.parent

# Unlisted while the site lives on dcastrop.github.io: pages ask search
# engines not to index them. Set to False when it moves to the club's site.
HIDDEN = True
CLUB_URL = 'https://papc-rhul.github.io/'
PDF_BASE = 'https://dcastrop.github.io/tex/2026-papc-challenge'
SIMPLE_CSS = 'https://cdn.jsdelivr.net/npm/simpledotcss@2.3.7/simple.min.css'
KATEX = 'https://cdn.jsdelivr.net/npm/katex@0.16.11/dist'

# ------------------------------------------------------------------ levels
TRACKS = {
    'all': 'Everyone starts here',
    'f': 'Programs track · follows FPIL',
    't': 'Proofs track · follows TPIL',
    'meet': 'The two tracks meet',
    'after-t': 'After the tracks meet · leans on TPIL',
    'after-f': 'After the tracks meet · leans on FPIL',
}

LEVELS = [
    # id, title, short title (map), track, after, next
    ('1', 'Tables, and Your First Proof', 'Tables, and a first proof',
     'all', [], ['2f', '2t']),
    ('2f', 'Selection, as a Program', 'Selection', 'f', ['1'], ['3f']),
    ('3f', 'Projection, Product and Union, as Programs',
     'Projection, product, union', 'f', ['2f'], ['4f']),
    ('4f', 'Difference and Joins, by Comparing Rows',
     'Difference and joins', 'f', ['3f'], ['5f']),
    ('5f', 'Named Columns, and a Query Language',
     'Named columns, queries', 'f', ['4f'], ['6']),
    ('2t', 'Selection and Union, Proved', 'Selection and union', 't',
     ['1'], ['3t']),
    ('3t', 'Difference, Proved: “Not”, and Classical Logic',
     'Difference', 't', ['2t'], ['4t']),
    ('4t', 'Product and Projection, Proved: “For All” and “There Exists”',
     'Product and projection', 't', ['3t'], ['5t']),
    ('5t', 'Induction on Lists', 'Induction on lists', 't', ['4t'], ['6']),
    ('6', 'Lists Represent Tables', 'Lists represent tables', 'meet',
     ['5f', '5t'], ['7', '9']),
    ('7', 'The Laws, for Every Query', 'Laws for every query', 'after-t',
     ['6'], ['8']),
    ('8', 'An Optimiser', 'An optimiser', 'after-t', ['7'], ['9']),
    ('9', 'Fast Joins', 'Fast joins', 'after-f', ['6'], ['7']),
]
LEVEL = {l[0]: dict(id=l[0], title=l[1], short=l[2], track=l[3],
                    after=l[4], next=l[5]) for l in LEVELS}


def lname(i):
    return f'Level {i.upper()}'


def lpage(i):
    return f'level-{i}.html'


def lpdf(i):
    return f'{PDF_BASE}/level-{i}/level-{i}.pdf'


# ------------------------------------------------------------------ links
def load_links():
    links = {}
    for line in (SRC / 'links.tsv').read_text(encoding='utf-8').splitlines():
        if line.startswith('#') or not line.strip():
            continue
        key, label, title, url = line.split('\t')
        links[key] = (label, title, url)
    return links


LINKS = load_links()

# The club's three tables, as in Level 1
CLUB = {
    'Member': (['name', 'dept'], 'll',
               [('Ada', 'Maths'), ('Alan', 'CS'), ('Grace', 'CS')]),
    'Attended': (['name', 'week'], 'lr',
                 [('Ada', '1'), ('Alan', '1'), ('Alan', '2'),
                  ('Grace', '3')]),
    'Session': (['week', 'topic'], 'rl',
                [('1', 'Lists'), ('2', 'Proofs'), ('3', 'Types'),
                 ('4', 'Sets')]),
}


def esc(s):
    return html.escape(s, quote=False)


def attr(s):
    return html.escape(s, quote=True)


def slug(s):
    s = re.sub(r'<[^>]+>', '', s)
    s = re.sub(r'\\\(.*?\\\)', '', s)
    s = s.lower()
    s = re.sub(r'[^a-z0-9]+', '-', s).strip('-')
    return s or 'section'


# ------------------------------------------------------------- highlight
LEAN_KW = set('''def theorem example abbrev namespace end open fun match with
if then else let have show from by deriving inductive structure where
instance import variable section do return in at calc termination_by
decreasing_by partial private noncomputable universe class lemma'''.split())
LEAN_TAC = set('''induction cases simp rw exact intro intros constructor
obtain apply rfl decide omega unfold refine ext split contradiction
assumption trivial simp_all funext subst rcases exfalso by_cases
simp_arith'''.split())
LEAN_TY = set('''Type Prop Bool Nat String List Array Option True False
Finset Multiset HashMap Std'''.split())
LEAN_RE = re.compile(r'''
  (?P<c>--[^\n]*|/-.*?-/)
| (?P<s>"(?:[^"\\]|\\.)*")
| (?P<cmd>\#[a-z]+)
| (?P<n>\b\d+\b)
| (?P<id>[A-Za-z_α-ωΑ-Ω][\w'α-ωΑ-Ω₀-₉!?]*(?:\.[A-Za-z_α-ωΑ-Ω][\w'α-ωΑ-Ω₀-₉!?]*)*)
''', re.X | re.S)
SQL_KW = set('''select distinct from where join on and or not as union
except intersect group by order having with recursive count sum'''.split())
SQL_RE = re.compile(r'''
  (?P<c>--[^\n]*)
| (?P<s>'(?:[^']|'')*')
| (?P<n>\b\d+\b)
| (?P<id>[A-Za-z_][\w.]*)
''', re.X)


def highlight(lang, code):
    if lang not in ('lean', 'sql'):
        return esc(code)
    rx = LEAN_RE if lang == 'lean' else SQL_RE
    out, pos = [], 0
    for m in rx.finditer(code):
        out.append(esc(code[pos:m.start()]))
        pos = m.end()
        kind, text = m.lastgroup, m.group()
        cls = None
        if kind in ('c', 's', 'n', 'cmd'):
            cls = kind
        elif lang == 'lean':
            if text == 'sorry':
                cls = 'sorry'
            elif text in LEAN_KW:
                cls = 'k'
            elif text in LEAN_TAC:
                cls = 't'
            elif text in LEAN_TY:
                cls = 'ty'
        elif text.lower() in SQL_KW:
            cls = 'k'
        out.append(f'<span class="{cls}">{esc(text)}</span>' if cls
                   else esc(text))
    out.append(esc(code[pos:]))
    return ''.join(out)


# --------------------------------------------------------------- renderer
def split_cells(row):
    """Split a pipe-table row on | outside $...$ and `...`."""
    row = row.strip()
    if row.startswith('|'):
        row = row[1:]
    if row.endswith('|'):
        row = row[:-1]
    cells, cur, math, code, link = [], '', False, False, 0
    for k, ch in enumerate(row):
        if ch == '$' and not code:
            math = not math
        elif ch == '`' and not math:
            code = not code
        elif row.startswith('[[', k):
            link += 1
        elif row.startswith(']]', k) and link:
            link -= 1
        if ch == '|' and not (math or code or link):
            cells.append(cur.strip())
            cur = ''
        else:
            cur += ch
    cells.append(cur.strip())
    return cells


class Page:
    """Renders one page; collects its headings, boxes and milestones."""

    def __init__(self, pid, registry):
        self.pid = pid
        self.registry = registry
        self.headings = []
        self.ids = set()
        self.milestones = []

    def uid(self, base):
        i, n = base, 2
        while i in self.ids:
            i, n = f'{base}-{n}', n + 1
        self.ids.add(i)
        return i

    # ------------------------------------------------------------ inline
    def ref(self, key):
        if key not in LINKS:
            sys.exit(f'{self.pid}: unknown link key {key!r}')
        label, title, url = LINKS[key]
        lab = f'{esc(label)} ' if label else ''
        return f'<a class="ref" href="{attr(url)}">{lab}<cite>{esc(title)}</cite></a>'

    def xlink(self, target, text):
        page, _, frag = target.partition('#')
        if page in LEVEL:
            href, default = lpage(page), lname(page)
        elif page in ('index', 'laws'):
            href, default = f'{page}.html', 'the challenge' if page == 'index' else 'Laws at a glance'
        elif page == '':
            href, default = '', frag
        else:
            sys.exit(f'{self.pid}: unknown page {page!r}')
        if frag:
            href += '#' + frag
        return f'<a href="{attr(href)}">{text or esc(default)}</a>'

    def inline(self, text):
        store = []

        def keep(s):
            store.append(s)
            return f'\x00{len(store) - 1}\x00'

        text = re.sub(r'`([^`]+)`',
                      lambda m: keep(f'<code>{esc(m.group(1))}</code>'), text)
        text = re.sub(r'\$([^$]+)\$',
                      lambda m: keep(f'\\({esc(m.group(1))}\\)'), text)
        text = re.sub(r'\[@([\w-]+)\]', lambda m: keep(self.ref(m.group(1))),
                      text)
        text = re.sub(r'\[\[([^\]|]+)(?:\|([^\]]+))?\]\]',
                      lambda m: keep(self.xlink(m.group(1), m.group(2))), text)
        text = re.sub(r'\[([^\]]+)\]\(([^)\s]+)\)',
                      lambda m: f'<a href="{attr(m.group(2))}">{m.group(1)}</a>',
                      text)
        text = re.sub(r'&(?!#?\w+;)', '&amp;', text)
        text = re.sub(r'\*\*(.+?)\*\*', r'<strong>\1</strong>', text)
        text = re.sub(r'(?<![\w*])\*(?=\S)(.+?)(?<=\S)\*(?![\w*])',
                      r'<em>\1</em>', text)
        while '\x00' in text:
            text = re.sub('\x00(\\d+)\x00', lambda m: store[int(m.group(1))],
                          text)
        return text

    # ------------------------------------------------------------ blocks
    def blocks(self, lines):
        out, i, n = [], 0, len(lines)

        def starts_block(s):
            return (s.startswith(('```', ':::', '$$', '@', '|', 'Table:'))
                    or re.match(r'(- |\d+\. |#{1,4} )', s))

        while i < n:
            s = lines[i].strip()
            if not s:
                i += 1
                continue
            if s.startswith('```'):
                j = i + 1
                while j < n and lines[j].strip() != '```':
                    j += 1
                out.append(self.code(s[3:].strip(), lines[i + 1:j]))
                i = j + 1
            elif s.startswith(':::') and s != ':::':
                j, depth = i + 1, 1
                while j < n:
                    t = lines[j].strip()
                    if t.startswith('```'):
                        j += 1
                        while j < n and lines[j].strip() != '```':
                            j += 1
                    elif t == ':::':
                        depth -= 1
                        if depth == 0:
                            break
                    elif t.startswith(':::'):
                        depth += 1
                    j += 1
                out.append(self.container(s[3:].strip(), lines[i + 1:j]))
                i = j + 1
            elif s.startswith('$$'):
                j = i
                if not (len(s) > 4 and s.endswith('$$')):
                    j = i + 1
                    while j < n and not lines[j].strip().endswith('$$'):
                        j += 1
                body = '\n'.join(l.strip() for l in lines[i:j + 1])
                body = body.strip()[2:-2].strip()
                out.append(f'<div class="math-display">\\[{esc(body)}\\]</div>')
                i = j + 1
            elif re.match(r'#{1,4} ', s):
                m = re.match(r'(#{1,4}) (.*)', s)
                out.append(self.heading(max(2, len(m.group(1))), m.group(2)))
                i += 1
            elif s.startswith('@'):
                out.append(self.directive(s[1:]))
                i += 1
            elif s.startswith(('|', 'Table:')):
                j = i + 1
                while j < n and lines[j].strip().startswith('|'):
                    j += 1
                out.append(self.table(lines[i:j]))
                i = j
            elif re.match(r'(- |\d+\. )', s):
                ordered = not s.startswith('- ')
                items, j = [], i
                while j < n and lines[j].strip():
                    t = lines[j].strip()
                    if re.match(r'(- |\d+\. )', t) and not lines[j].startswith(' '):
                        items.append(re.sub(r'^(- |\d+\. )', '', t))
                    else:
                        items[-1] += ' ' + t
                    j += 1
                tag = 'ol' if ordered else 'ul'
                lis = ''.join(f'<li>{self.inline(t)}</li>' for t in items)
                out.append(f'<{tag}>{lis}</{tag}>')
                i = j
            elif s.startswith('<'):
                j = i
                while j < n and lines[j].strip():
                    j += 1
                out.append('\n'.join(lines[i:j]))
                i = j
            else:
                j = i + 1
                while j < n and lines[j].strip() and not starts_block(lines[j].strip()):
                    j += 1
                text = ' '.join(l.strip() for l in lines[i:j])
                out.append(f'<p>{self.inline(text)}</p>')
                i = j
        return '\n'.join(out)

    def heading(self, level, text, hid=None, toc=True):
        m = re.match(r'(.*?)\s*\{#([\w-]+)\}$', text)
        if m:
            text, hid = m.group(1), m.group(2)
        inner = self.inline(text)
        hid = self.uid(hid or slug(inner))
        if toc:
            self.headings.append((level, hid, inner))
        return f'<h{level} id="{hid}">{inner}</h{level}>'

    def code(self, info, lines):
        lang, _, cap = info.partition(' ')
        lang = lang or 'text'
        code = '\n'.join(lines).strip('\n')
        sketch = '(sketch)' in cap
        cap = cap.replace('(sketch)', '').strip()
        label = {'lean': 'Lean', 'sql': 'SQL', 'sh': 'Terminal'}.get(lang, 'Text')
        bar = f'<span class="code-lang">{label}</span>'
        if cap:
            bar += f'<span class="code-cap">{self.inline(cap)}</span>'
        if sketch:
            bar += '<span class="chip sketch">Sketch</span>'
        bar += '<button type="button" class="copy" hidden>Copy</button>'
        return (f'<div class="code code-{lang}"><div class="code-bar">{bar}</div>'
                f'<pre tabindex="0"><code>{highlight(lang, code)}</code></pre></div>')

    def table(self, lines):
        caption = ''
        if lines[0].strip().startswith('Table:'):
            caption = lines[0].strip()[6:].strip()
            lines = lines[1:]
        rows = [split_cells(l) for l in lines]
        aligns = []
        if len(rows) > 1 and all(re.fullmatch(r':?-+:?', c) for c in rows[1]):
            aligns = ['r' if c.endswith(':') and not c.startswith(':') else
                      'c' if c.startswith(':') and c.endswith(':') else 'l'
                      for c in rows[1]]
            head, body = rows[0], rows[2:]
        else:
            head, body = None, rows
        return self.table_html(caption, head, aligns, body)

    def table_html(self, caption, head, aligns, body, cls=''):
        def cell(tag, c, k):
            a = aligns[k] if k < len(aligns) else 'l'
            al = f' class="{a}"' if a != 'l' else ''
            sc = ' scope="col"' if tag == 'th' else ''
            return f'<{tag}{al}{sc}>{self.inline(c)}</{tag}>'
        out = [f'<div class="table-wrap{cls}"><table>']
        if caption:
            out.append(f'<caption>{self.inline(caption)}</caption>')
        if head:
            out.append('<thead><tr>' + ''.join(cell('th', c, k) for k, c in enumerate(head))
                       + '</tr></thead>')
        out.append('<tbody>')
        for r in body:
            out.append('<tr>' + ''.join(cell('td', c, k) for k, c in enumerate(r)) + '</tr>')
        out.append('</tbody></table></div>')
        return ''.join(out)

    def club(self, names):
        parts = []
        for name in names:
            cols, al, rows = CLUB[name]
            parts.append(self.table_html(
                f'$\\rel{{{name}}}$', [f'$\\att{{{c}}}$' for c in cols],
                list(al), rows, ' small'))
        return f'<div class="row">{"".join(parts)}</div>'

    def directive(self, s):
        name, _, rest = s.partition(' ')
        if name == 'club':
            return self.club(rest.split())
        if name == 'map':
            return level_map()
        if name == 'toc':
            return '\x01TOC\x01'
        if name == 'index':
            return '\x01INDEX\x01'
        if name == 'pdfs':
            return pdf_list()
        if name == 'reset':
            return ('<p><button type="button" class="reset" hidden>Clear my '
                    'ticks</button></p>')
        sys.exit(f'{self.pid}: unknown directive @{name}')

    # -------------------------------------------------------- containers
    def container(self, head, lines):
        kind, _, rest = head.partition(' ')
        rest = rest.strip()
        if kind == 'box':
            m = re.match(r'(\w+)(?: ([\w.]+))?(.*)', rest)
            word, num, tail = m.group(1), m.group(2) or '', m.group(3).strip()
            cls = {'Definition': 'def', 'Law': 'law'}.get(word, 'fact')
            bid = self.uid(slug(f'{word} {num}' if num else rest))
            name = f'{word} {num}'.strip()
            title = f'<span class="box-n">{esc(name)}</span>'
            if tail:
                title += ' ' + self.inline(tail)
            self.registry.append((self.pid, bid, name, self.inline(tail), cls))
            return (f'<div class="box {cls}" id="{bid}"><p class="box-h">{title}</p>'
                    f'{self.blocks(lines)}</div>')
        if kind == 'proof':
            inner = self.blocks(lines)
            label = f'<em>{esc(rest or "Proof")}.</em> '
            if inner.startswith('<p>'):
                inner = '<p>' + label + inner[3:]
            else:
                inner = f'<p>{label}</p>' + inner
            qed = '<span class="qed" role="img" aria-label="End of proof">∎</span>'
            if inner.endswith('</p>'):
                inner = inner[:-4] + ' ' + qed + '</p>'
            else:
                inner += f'<p class="qed-line">{qed}</p>'
            return f'<div class="proof">{inner}</div>'
        if kind in ('ex', 'q'):
            m = re.match(r'([\w.]+)(?: (lean|paper|stretch))?(.*)', rest)
            num, chip, title = m.group(1), m.group(2), m.group(3).strip()
            word = 'Exercise' if kind == 'ex' else 'Question'
            eid = self.uid(f'{kind}-{slug(num)}')
            h = f'<span class="ex-n">{word} {esc(num)}</span>'
            if chip:
                h += f' <span class="chip {chip}">' + {
                    'lean': 'In Lean', 'paper': 'On paper',
                    'stretch': 'Stretch'}[chip] + '</span>'
            if title:
                h += f' <span class="ex-t">{self.inline(title)}</span>'
            return (f'<div class="{kind}" id="{eid}"><p class="ex-h">{h}</p>'
                    f'{self.blocks(lines)}</div>')
        if kind in ('hint', 'answer'):
            summary = rest or kind.capitalize()
            return (f'<details class="{kind}"><summary>{self.inline(summary)}</summary>'
                    f'{self.blocks(lines)}</details>')
        if kind == 'note':
            h = f'<p class="note-h">{self.inline(rest)}</p>' if rest else ''
            return f'<div class="note">{h}{self.blocks(lines)}</div>'
        if kind == 'callout':
            return f'<div class="callout">{self.blocks(lines)}</div>'
        if kind == 'row':
            return f'<div class="row">{self.blocks(lines)}</div>'
        if kind == 'figure':
            cap = f'<figcaption>{self.inline(rest)}</figcaption>' if rest else ''
            return f'<figure>{self.blocks(lines)}{cap}</figure>'
        if kind == 'part':
            pkind, _, title = rest.partition(' ')
            kicker = {'theory': 'Theory, on paper',
                      'lean': 'Lean, on your computer',
                      'setup': 'Before you start',
                      'beyond': 'Beyond Level 9'}[pkind]
            hid = self.uid(slug(kicker))
            self.headings.append((2, hid, kicker))
            h = (f'<h2 id="{hid}"><span class="part-k">{kicker}</span>'
                 f'<span class="part-t">{self.inline(title)}</span></h2>')
            return (f'<section class="part part-{pkind}" aria-labelledby="{hid}">'
                    f'{h}{self.blocks(lines)}</section>')
        if kind == 'glance':
            return self.glance(lines)
        if kind == 'milestones':
            return self.milestone_list(lines)
        sys.exit(f'{self.pid}: unknown container ::: {kind}')

    def glance(self, lines):
        dl, reads = [], []
        for line in lines:
            line = line.strip()
            if not line:
                continue
            key, _, val = line.partition(':')
            val = val.strip()
            if key == 'build':
                dl.append(('You build', val))
            elif key == 'prove':
                dl.append(('You prove', val))
            elif key == 'learn':
                what, refs = split_cells(val)
                reads.append((what, refs))
            else:
                sys.exit(f'{self.pid}: bad glance line {line!r}')
        hid = self.uid('at-a-glance')
        self.headings.append((2, hid, 'At a glance'))
        out = [f'<section class="glance" aria-labelledby="{hid}">'
               f'<h2 id="{hid}">At a glance</h2><dl>']
        for k, v in dl:
            out.append(f'<div><dt>{k}</dt><dd>{self.inline(v)}</dd></div>')
        out.append('</dl>')
        if reads:
            out.append('<div class="table-wrap"><table class="reads"><caption>What to '
                       'learn first, and where</caption><thead><tr><th scope="col">'
                       'Learn to</th><th scope="col">Read</th></tr></thead><tbody>')
            for what, refs in reads:
                out.append(f'<tr><td>{self.inline(what)}</td><td>{self.inline(refs)}</td></tr>')
            out.append('</tbody></table></div>')
        out.append('</section>')
        return ''.join(out)

    def milestone_list(self, lines):
        items = []
        for line in lines:
            t = line.strip()
            if t.startswith('- '):
                items.append(t[2:])
            elif t and items:
                items[-1] += ' ' + t
        keys = [f'{self.pid}:m{k + 1}' for k in range(len(items))]
        self.milestones.extend(keys)
        hid = self.uid('milestones')
        self.headings.append((2, hid, 'Milestones'))
        lis = ''.join(
            f'<li><label><input type="checkbox" data-milestone="{k}"> '
            f'<span>{self.inline(t)}</span></label></li>'
            for k, t in zip(keys, items))
        n = len(keys)
        return (f'<section class="milestones" aria-labelledby="{hid}">'
                f'<h2 id="{hid}">Milestones</h2>'
                f'<p class="ms-intro">Tick each one when Lean accepts your work. '
                f'Your ticks stay in this browser.</p><ul>{lis}</ul>'
                f'<p class="ms-progress" data-progress="{" ".join(keys)}">'
                f'<progress max="{n}" value="0"></progress> '
                f'<span class="ms-count" aria-live="polite">0 of {n} done</span></p>'
                f'</section>')


# ------------------------------------------------------------- site parts
MILESTONES = {}   # level id -> milestone keys (filled while building)


def level_card(i):
    lv = LEVEL[i]
    keys = ' '.join(MILESTONES.get(i, []))
    return (f'<a class="lvl lvl-{lv["track"]}" href="{lpage(i)}" '
            f'data-progress="{keys}"><span class="lvl-id">{lname(i)}</span> '
            f'<span class="lvl-t">{esc(lv["short"])}</span>'
            f'<span class="lvl-p"></span></a>')


def level_map():
    def col(ids, cls, head=''):
        lis = ''.join(f'<li>{level_card(i)}</li>' for i in ids)
        return f'<div class="map-col {cls}">{head}<ol>{lis}</ol></div>'
    f_head = ('<p class="track-h">Programs first <small>follows FPIL</small></p>')
    t_head = ('<p class="track-h">Proofs first <small>follows TPIL</small></p>')
    return (
        '<nav class="map" aria-label="The levels">'
        f'<div class="map-one"><ol><li>{level_card("1")}</li></ol></div>'
        '<div class="map-two">'
        + col(['2f', '3f', '4f', '5f'], 'col-f', f_head)
        + col(['2t', '3t', '4t', '5t'], 'col-t', t_head)
        + '</div>'
        f'<div class="map-one meet"><ol><li>{level_card("6")}</li></ol></div>'
        '<div class="map-two after">'
        + col(['9'], 'col-f') + col(['7', '8'], 'col-t')
        + '</div></nav>')


def pdf_list():
    items = [f'<li><a href="{PDF_BASE}/slides.pdf">The presentation</a> '
             '(6 pages, no theory, no code)</li>']
    for i in LEVEL:
        items.append(f'<li><a href="{lpdf(i)}">{lname(i)}: '
                     f'{esc(LEVEL[i]["title"])}</a></li>')
    return '<ul class="pdfs">' + ''.join(items) + '</ul>'


def toc_html(headings):
    if len(headings) < 3:
        return ''
    out, open_sub = ['<nav class="toc" aria-label="On this page"><details>'
                     '<summary>On this page</summary><ol>'], False
    for level, hid, text in headings:
        text = re.sub(r'<a [^>]*>|</a>', '', text)
        if level == 2:
            if open_sub:
                out.append('</ol></li>')
                open_sub = False
            out.append(f'<li><a href="#{hid}">{text}</a>')
            out.append('<ol>')
            open_sub = True
        else:
            out.append(f'<li><a href="#{hid}">{text}</a></li>')
    if open_sub:
        out.append('</ol></li>')
    html_ = ''.join(out) + '</ol></details></nav>'
    return html_.replace('<ol></ol>', '')


def index_html(registry):
    out = []
    for i in LEVEL:
        rows = [r for r in registry if r[0] == i]
        if not rows:
            continue
        lis = ''.join(
            f'<li><a href="{lpage(i)}#{bid}"><span class="box-n">{esc(name)}</span></a>'
            f'{" " + tail if tail else ""}</li>'
            for _, bid, name, tail, _ in rows)
        out.append(f'<h3 id="index-{i}"><a href="{lpage(i)}">{lname(i)}</a>: '
                   f'{esc(LEVEL[i]["title"])}</h3><ul class="index">{lis}</ul>')
    return ''.join(out)


def head_html(title, description):
    robots = '<meta name="robots" content="noindex">\n' if HIDDEN else ''
    return f'''<!doctype html>
<html lang="en-GB">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
{robots}<title>{esc(title)}</title>
<meta name="description" content="{attr(description)}">
<link rel="icon" href="assets/papc-logo.png">
<link rel="stylesheet" href="{SIMPLE_CSS}">
<link rel="stylesheet" href="{KATEX}/katex.min.css">
<link rel="stylesheet" href="assets/challenge.css">
<script defer src="{KATEX}/katex.min.js"></script>
<script defer src="{KATEX}/contrib/auto-render.min.js"></script>
<script defer src="assets/challenge.js"></script>
</head>
<body>
<a class="skip" href="#main">Skip to the content</a>
'''


def header_html(current, h1, kicker=''):
    def nav(href, text, key):
        cur = ' aria-current="page"' if key == current else ''
        return f'<li><a href="{href}"{cur}>{text}</a></li>'
    k = f'<p class="kicker">{kicker}</p>' if kicker else ''
    return f'''<header>
<p class="club"><a href="{CLUB_URL}"><img src="assets/papc-logo.png" alt="" width="38" height="48"> The Proofs and Programs Club @ RHUL</a></p>
{k}<h1>{h1}</h1>
<nav aria-label="The challenge"><ul>{nav("index.html", "The challenge", "index")}{nav("index.html#levels", "All levels", "levels")}{nav("laws.html", "Laws at a glance", "laws")}</ul></nav>
</header>
'''


FOOTER = f'''<footer>
<p>The first challenge of the <a href="{CLUB_URL}">Proofs and Programs Club @ RHUL</a>.</p>
<p>Your ticked milestones are kept in this browser only.</p>
</footer>
</body>
</html>
'''


def level_nav(i):
    lv = LEVEL[i]
    after = ' and '.join(f'<a href="{lpage(a)}">{lname(a)}</a>' for a in lv['after'])
    nxt = ' or '.join(f'<a href="{lpage(a)}">{lname(a)}</a>' for a in lv['next'])
    bits = []
    bits.append(f'After {after}' if after else 'Start here')
    bits.append(f'Next: {nxt}')
    bits.append(f'<a href="{lpdf(i)}">Slides (PDF)</a>')
    return '<p class="crumbs">' + ' · '.join(bits) + '</p>'


def next_section(i):
    lv = LEVEL[i]
    cards = ''.join(f'<li>{level_card(n)}</li>' for n in lv['next'])
    extra = ''
    if i in ('8', '9'):
        extra = ('<p>Done with Levels 7, 8 and 9? Take on a '
                 '<a href="level-9.html#beyond-level-9">stretch goal</a>, '
                 'or pitch us your own challenge.</p>')
    return (f'<section class="next" aria-labelledby="next-h"><h2 id="next-h">Next</h2>'
            f'<ol class="next-cards">{cards}</ol>{extra}'
            '<p class="stuck">Stuck, or curious? Ask us: on Discord, or any '
            'Thursday.</p></section>')


def read_page(pid):
    return (SRC / 'pages' / f'{pid}.txt').read_text(encoding='utf-8').splitlines()


def build():
    registry = []
    pages = {}
    for i in LEVEL:
        p = Page(i, registry)
        body = p.blocks(read_page(f'level-{i}'))
        MILESTONES[i] = p.milestones
        pages[i] = (p, body)
    written = []
    for i, (p, body) in pages.items():
        lv = LEVEL[i]
        body = body.replace('\x01TOC\x01', toc_html(p.headings))
        h1 = f'<span class="lvl-k">{lname(i)}</span> {esc(lv["title"])}'
        kicker = f'<span class="chip track-{lv["track"]}">{TRACKS[lv["track"]]}</span>'
        doc = (head_html(f'{lname(i)}: {lv["title"]} · PaPC challenge',
                         f'{lname(i)} of the PaPC challenge: {lv["title"]}.')
               + header_html('', h1, kicker)
               + f'<main id="main">{level_nav(i)}{body}{next_section(i)}</main>\n'
               + FOOTER)
        written.append(write(lpage(i), doc))
    for pid, title, h1, desc in [
            ('index', 'We Have a Challenge for You! · PaPC',
             'We Have a Challenge for You!',
             'The first challenge of the Proofs and Programs Club @ RHUL: a '
             'verified relational algebra library in Lean, by hand.'),
            ('laws', 'Laws at a Glance · PaPC challenge', 'Laws at a Glance',
             'Every definition, fact and law of the PaPC challenge, with '
             'links to where each is proved.')]:
        p = Page(pid, [])
        body = p.blocks(read_page(pid))
        body = body.replace('\x01TOC\x01', toc_html(p.headings))
        body = body.replace('\x01INDEX\x01', index_html(registry))
        kicker = ('A verified relational algebra library in Lean, by hand'
                  if pid == 'index' else '')
        doc = (head_html(title, desc) + header_html(pid, h1, kicker)
               + f'<main id="main">{body}</main>\n' + FOOTER)
        written.append(write(f'{pid}.html', doc))
    check_links()
    print('wrote', ', '.join(written))


DOCS = {}


def write(name, doc):
    if '\x00' in doc or '\x01' in doc:
        sys.exit(f'{name}: unresolved placeholder')
    DOCS[name] = doc
    (OUT / name).write_text(doc, encoding='utf-8')
    return name


def check_links():
    """Every internal link must reach a page, and an id on it."""
    bad = []
    for name, doc in DOCS.items():
        for page, frag in re.findall(r'href="([\w-]*\.html)?#?([\w-]*)"', doc):
            target = page or name
            if page and target not in DOCS:
                bad.append(f'{name}: no page {target}')
            elif frag and f'id="{frag}"' not in DOCS[target]:
                bad.append(f'{name}: no #{frag} in {target}')
    if bad:
        sys.exit('broken links:\n  ' + '\n  '.join(sorted(set(bad))))


if __name__ == '__main__':
    build()
