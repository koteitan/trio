# -*- coding: utf-8 -*-
"""H15 (3b): 族 β（証人が標準形でない）と δ（どれでも直らない）を掘る。"""
import sys, os, pickle, itertools, time
from collections import Counter, defaultdict
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/g2')
import rows3, rows3v, provc, inv3, imgfast
from core import expand, show, isstd

fam = pickle.load(open('/tmp/h1work/h15fam.pkl', 'rb'))
cof = [e['A'] for e in fam]
bad = defaultdict(list)
for A, m, T in pickle.load(open('/tmp/h1work/img54p.pkl', 'rb')):
    a = tuple(map(tuple, A))
    if a in set(cof):
        bad[a].append((m, tuple(map(tuple, T))))

print('=== 族 β（証人が標準形でない）: 探索 `imgfast.find2` で逆像があるか ===')
nb = 0
for e in fam:
    if e['cls'] != '証人が標準形でない':
        continue
    A = e['A']
    for m, T in sorted(bad[A])[:2]:
        t0 = time.time()
        r = imgfast.find2(tuple(A), m, f=rows3.b2d3, T=tuple(T))
        _, B, stage, nodes, capped = r
        nb += 1
        print('  %-40s m=%d  探索 -> %s  (段 %s, 節点 %d, 打ち切り %s, %.0fs)'
              % (show(list(A)), m, ('**逆像あり**' if B else 'なし'), stage,
                 nodes, capped, time.time() - t0))

print()
print('=== 族 δ（どれでも直らない）: 最初にずれた柱 ===')
c = Counter()
for e in fam:
    if e['cls'] != 'どれでも直らない':
        continue
    A = e['A']
    for m, T in sorted(bad[A]):
        B = inv3.d2b3([list(x) for x in T])
        if not B:
            continue
        Bt = tuple(tuple(x) for x in B)
        if not isstd(Bt, 'BMS') or any(x[2] > 1 for x in Bt):
            continue
        C, PR = provc.b2d3p(list(Bt))
        k = 0
        while k < min(len(C), len(T)) and C[k] == T[k]:
            k += 1
        if k >= len(PR):
            c['ずれが記録の外（長さ差 %d）' % (len(C) - len(T))] += 1
            continue
        kind, off, why, ctx = PR[k]
        c[('why=%s' % why, 'ctx=%s' % str(ctx))] += 1
        c['長さ差 %d' % (len(C) - len(T))] += 1
for k, v in c.most_common():
    print('   %-50s %d' % (str(k), v))
