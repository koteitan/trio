# -*- coding: utf-8 -*-
"""シート点（`conv3` の像が E 列に一致する行数）を旗ごとに測る。"""
import sys, os
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import r10
from rows3 import b2d3

D = r10.load3(drop_typo=False)
tot = ok = 0
ng = []
for row, b, d, _ in D:
    if not all(c[2] <= 1 for c in b):
        continue
    tot += 1
    got = tuple(tuple(c) for c in b2d3(list(b)))
    if got == d:
        ok += 1
    else:
        ng.append(row)
fl = ' '.join(k for k in sorted(os.environ) if k.startswith('RS_')) or '既定(v18)'
print('%-42s シート点 **%d / %d**  外れ %d' % (fl, ok, tot, tot - ok))
print('   外れた行（先頭 25）: %s' % ng[:25])
