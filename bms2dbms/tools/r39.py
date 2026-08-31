# -*- coding: utf-8 -*-
"""課題 R25: `ImgCofinalT` の破れの候補 `T` は**本物の非像**か。

`T` は短い（5〜13 列）ので、**BMS 標準形を全数なめて像の集合を作り**、
`T` がその中にあるかを直に見る。`preimage_try` の発見性に頼らない**決定的な検査**。

`|conv3 B| >= |B|`（縮約が起きなければ）なので、`|T| <= L` の `T` については
`gen3('BMS', L)` の像を全部見れば**逆像の有無が確定**する（縮約が起きる `B` は
`|B| > |T|` になりうるので、そこだけ上界のまま）。
"""
import sys, time, pickle
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, core
from rows3 import b2d3, gen3, key
from core import expand, isstd, show
from collections import Counter

LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 9
PAT = pickle.load(open('/home/koteitan/proofs/dbms/bms2dbms/tools/r37pat_5_7.pkl', 'rb'))
allmiss = [A for A, s in PAT if set(s) <= set('.') and len(s) >= 8]
hitok = [A for A, s in PAT if s.startswith('RRRR')]
print('すべて外れの A %d 個 / 陽性対照（性質 R が立つ A）%d 個'
      % (len(allmiss), len(hitok)), flush=True)

NEED = {}
for tag, pool in (('候補', allmiss), ('対照', hitok[:40])):
    for A in pool:
        fA = tuple(tuple(x) for x in b2d3(list(A)))
        for m in range(1, 9):
            T = tuple(tuple(x) for x in expand(fA, m))
            if not T or len(T) > LIM:
                continue
            NEED.setdefault(T, []).append((tag, A, m))
print('検査する T: %d 個（|T| <= %d）  内訳 %s'
      % (len(NEED), LIM,
         dict(Counter(t for v in NEED.values() for t, _, _ in v))), flush=True)

t0 = time.time()
IMG = set()
G = gen3('BMS', LIM, zcap=1)
print('  BMS 標準形 <=%d 列: %d 個 (%.0fs)' % (LIM, len(G), time.time() - t0), flush=True)
t0 = time.time()
for i, B in enumerate(G):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    IMG.add(bytes(x for c in b2d3(list(B)) for x in c))
del G
print('  像の集合 %d 件 (%.0fs)' % (len(IMG), time.time() - t0), flush=True)

c = Counter(); ex = []
for T, who in NEED.items():
    inimg = bytes(x for cc in T for x in cc) in IMG
    for tag, A, m in who:
        c['%s: 像の集合に**%s**' % (tag, '入る' if inimg else '入らない')] += 1
    if not inimg and any(t == '候補' for t, _, _ in who) and len(ex) < 6:
        ex.append((T, who[0]))
print()
for k in sorted(c, key=str):
    print('   %-40s %d' % (k, c[k]))
print()
for T, (tag, A, m) in ex:
    print('   ### 候補 |T|=%d  m=%d' % (len(T), m))
    print('      A = %s' % ''.join(str(x).replace(' ', '') for x in A))
    print('      T = %s   isstd DBMS=%s'
          % (''.join(str(x).replace(' ', '') for x in T), isstd(T, 'DBMS')))
