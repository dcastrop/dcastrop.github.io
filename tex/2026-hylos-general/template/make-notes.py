#!/usr/bin/env python3
"""Turn <job>.notes (written by \\speakernote in dcptalk.sty) into
<job>.pdfpc, for pdfpc's presenter console, and <job>-notes.md, a printable
notes sheet.

Usage: make-notes.py JOB [--duration MINUTES]
"""
import argparse
import json
import re

SEP = '|||'


def tex_to_md(s):
    """Rough LaTeX to Markdown for note text."""
    s = s.replace('\\\\', ' ')
    for cmd, wrap in (('code', '`'), ('texttt', '`'), ('emph', '*'),
                      ('textit', '*'), ('textbf', '**'), ('embf', '**')):
        s = re.sub(r'\\' + cmd + r'\s*\{([^{}]*)\}', wrap + r'\1' + wrap, s)
    s = re.sub(r'\\(ldots|dots)\b\s*', '...', s)
    s = s.replace('~', ' ').replace('``', '"').replace("''", '"')
    s = s.replace('---', '-').replace('--', '-')
    s = re.sub(r'\\([_&%#$])', r'\1', s)
    s = re.sub(r'\\textasciitilde\s*', '~', s)
    s = re.sub(r'\\textbackslash\s*', '\\\\', s)
    s = re.sub(r'\s+', ' ', s)
    return s.strip()


def read_notes(job):
    """Notes per page, in order: {page: (title, [text, ...])}."""
    pages = {}
    with open(job + '.notes', encoding='utf-8') as f:
        for line in f:
            line = line.rstrip('\n')
            if not line:
                continue
            page, title, text = line.split(SEP, 2)
            page = int(page.strip())
            title = tex_to_md(title)
            entry = pages.setdefault(page, (title, []))
            # \\ separates bullet points
            parts = [tex_to_md(t) for t in text.split('\\\\')]
            parts = [t for t in parts if t]
            entry[1].append(parts[0] if len(parts) == 1
                            else '\n'.join('- ' + t for t in parts))
    return pages


def write_pdfpc(job, pages, duration):
    out = {'pdfpcFormat': 2, 'disableMarkdown': False, 'pages': []}
    if duration:
        out['duration'] = duration
    for page in sorted(pages):
        out['pages'].append({'idx': page - 1, 'label': '', 'overlay': 0,
                             'note': '\n\n'.join(pages[page][1])})
    with open(job + '.pdfpc', 'w', encoding='utf-8') as f:
        json.dump(out, f, indent=1, ensure_ascii=False)


def write_sheet(job, pages):
    """One entry per run of pages with the same title and notes."""
    runs = []
    for page in sorted(pages):
        title, texts = pages[page]
        if runs and runs[-1][2] == title and runs[-1][3] == texts \
                and runs[-1][1] == page - 1:
            runs[-1][1] = page
        else:
            runs.append([page, page, title, texts])
    with open(job + '-notes.md', 'w', encoding='utf-8') as f:
        f.write('# Speaker notes\n\n')
        for first, last, title, texts in runs:
            pages_str = str(first) if first == last else f'{first}-{last}'
            f.write(f'## {title or "(no title)"} (p. {pages_str})\n\n')
            for t in texts:
                f.write(t + '\n\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('job')
    ap.add_argument('--duration', type=int, default=0,
                    help='talk length in minutes, for the pdfpc timer')
    args = ap.parse_args()
    pages = read_notes(args.job)
    write_pdfpc(args.job, pages, args.duration)
    write_sheet(args.job, pages)


if __name__ == '__main__':
    main()
