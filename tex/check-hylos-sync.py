#!/usr/bin/env python3
"""Check that the two hylomorphism talks stay in sync: the code snippets,
frames and style they share must be identical. Run from tex/:

    python3 check-hylos-sync.py

Exit status 1 and a diff for every mismatch.
"""
import difflib
import re
import sys

GEN = '2026-hylos-general/'
SEM = '2026-hylos-seminar/'

# Same file in both decks
SAME_FILES = [
    'template/dcptalk.sty',
] + [f'hylos-general/code/{f}:hylos-seminar/code/{f}' for f in [
    'rocqlexer.py',
    # the calculations and their output
    'qsort2.ml', 'qsort-steps.v', 'knap-steps.v',
    # the general deck's Rocq part, copied from the seminar
    # (not naive-eq.v: the general deck drops a comment; the general deck
    # shows hylo, not quicksort, failing the termination check)
    'naive-cont.v', 'naive-extr.ml',
    'naive-eq.txt', 'cont-class.v', 'recf.v', 'hylo-def.v',
    'hylo-laws.v', 'raw-extr.ml', 'malg.v', 'malg-fusion.v',
]]

# Same frame (title) in both decks, compared with speaker notes
SAME_FRAMES = [
    ('hylos-general/sections/06-rocq.tex',
     'hylos-seminar/sections/06-calculation.tex', 'Quicksort, Step by Step'),
    ('hylos-general/sections/06-rocq.tex',
     'hylos-seminar/sections/07-dynamorphisms.tex', 'Knapsack, Step by Step'),
]

TIKZMARK = re.compile(r'\^\\tikzmark\{[^}]*\}\^')
# The general deck flags the frames its live demo covers
DEMOTAG = re.compile(r'^ *\\demotag\n', re.M)


def read(path):
    with open(path, encoding='utf-8') as f:
        return f.read()


def frame(text, title):
    t = text.index('\\frametitle{' + title + '}')
    b = max(text.rfind('\\begin{frame}', 0, t),
            text.rfind('\\begin{frame*}', 0, t))
    e = text.index('\\end{frame', t)
    return text[b:text.index('\n', e)]


def report(name, a, b):
    if a == b:
        return True
    print(f'MISMATCH: {name}')
    sys.stdout.writelines(difflib.unified_diff(
        a.splitlines(True), b.splitlines(True), 'general', 'seminar'))
    return False


def main():
    ok = True
    for spec in SAME_FILES:
        g, s = spec.split(':') if ':' in spec else (spec, spec)
        ok &= report(g, read(GEN + g), read(SEM + s))
    # The quicksort Derive: the general deck adds two \tikzmarks
    ok &= report('qsort2-derive.v (without \\tikzmark)',
                 TIKZMARK.sub('', read(GEN + 'hylos-general/code/qsort2-derive.v')),
                 read(SEM + 'hylos-seminar/code/qsort2-derive.v'))
    for g, s, title in SAME_FRAMES:
        ok &= report(f'frame "{title}"',
                     DEMOTAG.sub('', frame(read(GEN + g), title)),
                     frame(read(SEM + s), title))
    print('in sync' if ok else 'NOT in sync')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
