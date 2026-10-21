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
    'hylos-general/code/rocqlexer.py:hylos-seminar/code/rocqlexer.py',
    'hylos-general/code/sort-times-two.ml:hylos-seminar/code/sort-times-two.ml',
    'hylos-general/code/qsort2.ml:hylos-seminar/code/qsort2.ml',
    'hylos-general/code/qsort-steps.v:hylos-seminar/code/qsort-steps.v',
    'hylos-general/code/knap-steps.v:hylos-seminar/code/knap-steps.v',
    'hylos-general/code/knap-arr.ml:hylos-seminar/code/knap-arr.ml',
    'hylos-general/code/knap-jump.ml:hylos-seminar/code/knap-jump.ml',
]

# Same frame (title) in both decks, compared with speaker notes
SAME_FRAMES = [
    ('hylos-general/sections/04-results.tex',
     'hylos-seminar/sections/06-calculation.tex', 'Quicksort, Step by Step'),
    ('hylos-general/sections/04-results.tex',
     'hylos-seminar/sections/07-dynamorphisms.tex', 'Knapsack, Step by Step'),
    ('hylos-general/sections/04-results.tex',
     'hylos-seminar/sections/07-dynamorphisms.tex',
     'Knapsack: What Comes Out'),
]

TIKZMARK = re.compile(r'\^\\tikzmark\{[^}]*\}\^')


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
                 read(SEM + 'hylos-seminar/code/qsort2-derive.v')
                 .replace(' finished.\n', '\n  finished.\n'))
    # The knapsack Derive: step 2 of the seminar's two-step calculation
    derive = read(GEN + 'hylos-general/code/knap-derive.v')
    calc = read(SEM + 'hylos-seminar/code/knap-calc.v')
    ok &= report('knap-derive.v in knap-calc.v', derive,
                 calc[calc.index('Derive knapsack_arr'):])
    for g, s, title in SAME_FRAMES:
        ok &= report(f'frame "{title}"', frame(read(GEN + g), title),
                     frame(read(SEM + s), title))
    print('in sync' if ok else 'NOT in sync')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
