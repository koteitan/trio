# -*- coding: utf-8 -*-
"""課題 R9 の続き: 綴りは接頭辞の関数ではない。では**正しい条件は何か**。

接頭辞 `P` の束の中で、行列を `seqlex` 昇順に並べたとき、その site が出した柱が
`collt` について**単調非減少**か（＝ 伸ばすと綴りは深くなる方にしか動かない）。
"""
import sys, os, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/g2')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, provc, r7
from rows3 import is_branch
from collections import defaultdict, Counter

v, L = int(sys.argv[1]), int(sys.argv[2])
P = r7.stts_pool(v, L)
bund = defaultdict(list)
t0 = time.time()
for i, M in enumerate(P):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    C, PR = provc.b2d3p(list(M))
    C = tuple(tuple(c) for c in C)
    for idx, (kind, off, why, ctx) in enumerate(PR):
        if kind == 'body' and off < len(M) and is_branch(M[off]):
            bund[tuple(M[:off + 1])].append((M, C[idx]))
c = Counter(); ex = []
for pre, items in bund.items():
    if len(items) < 2:
        continue
    items.sort(key=lambda t: t[0])
    c['_束'] += 1
    for i in range(len(items) - 1):
        a, b = items[i][1], items[i + 1][1]
        c['_隣'] += 1
        if a < b:
            c['増（深くなる）'] += 1
        elif a == b:
            c['同じ'] += 1
        else:
            c['**減（浅くなる）**'] += 1
            if len(ex) < 5:
                ex.append((pre, items[i], items[i + 1]))
fl = ' '.join(k for k in sorted(os.environ) if k.startswith('RS_')) or '既定(v18)'
print('%s  ST_TS v<=%d len<=%d %d 個  束 %d  隣 %d  (%.0fs)'
      % (fl, v, L, len(P), c['_束'], c['_隣'], time.time() - t0))
for k in sorted(c, key=str):
    if not k.startswith('_'):
        print('   %-20s %d' % (k, c[k]))
for pre, a, b in ex[:3]:
    print('   ### 減る例  接頭辞 = %s'
          % ''.join(str(x).replace(' ', '') for x in pre))
    print('      M1 = %s -> %s' % (''.join(str(x).replace(' ', '') for x in a[0]), a[1]))
    print('      M2 = %s -> %s' % (''.join(str(x).replace(' ', '') for x in b[0]), b[1]))
