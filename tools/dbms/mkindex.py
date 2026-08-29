#!/usr/bin/env python3
"""lean/*.lean から theorem/def/lemma の完全な型を 1 行ずつ抜き出して
lean/LEMMA-INDEX.tsv を作る。書く前に grep するための索引。"""
import re, glob, os
os.chdir(os.path.join(os.path.dirname(__file__), '..', '..', 'lean'))
out = []
for f in sorted(x for x in glob.glob('*.lean') if not x.startswith('.')):
    lines = open(f, encoding='utf-8').read().split('\n')
    for i, l in enumerate(lines):
        m = re.match(r'^(theorem|def|lemma|abbrev)\s+([A-Za-z_][A-Za-z0-9_\'!?]*)', l)
        if not m:
            continue
        sig, j = [l], i + 1
        while j < len(lines) and j < i + 6 and ':=' not in sig[-1] \
                and not sig[-1].rstrip().endswith('by'):
            sig.append(lines[j]); j += 1
        s = re.sub(r'\s+', ' ', ' '.join(x.strip() for x in sig)).split(':=')[0].strip()
        out.append(f"{f}:{i+1}\t{m.group(1)} {m.group(2)}\t{s[:300]}")
open('LEMMA-INDEX.tsv', 'w', encoding='utf-8').write('\n'.join(out) + '\n')
print(f"{len(out)} entries")
