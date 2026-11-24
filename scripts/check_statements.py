#!/usr/bin/env python3
"""Check that every declaration quoted in STATEMENTS.md occurs verbatim in the Lean sources.

Each ```lean block is split into declarations (a line starting with def/theorem/abbrev/structure); each one must be
a verbatim substring of some file in LeanResidy/. Exit code 1 on any mismatch.
"""
import pathlib, re, sys
root = pathlib.Path(__file__).resolve().parent.parent
src = {p: p.read_text() for p in (root / 'LeanResidy').rglob('*.lean')}
md = (root / 'STATEMENTS.md').read_text()
blocks = re.findall(r'```lean\n(.*?)```', md, re.S)
bad = n = 0
for b in blocks:
    for d in re.split(r'\n(?=(?:theorem|def|abbrev|structure) )', b.strip()):
        n += 1
        if not any(d.strip() in t for t in src.values()):
            bad += 1
            print('NOT FOUND VERBATIM:\n' + d + '\n')
print(f'{n} declarations quoted, {n - bad} found verbatim')
sys.exit(1 if bad else 0)
