# -*- coding: utf-8 -*-
"""課題 R29: `ImgCofinalT3` を **1 回で決着**させる。

§R28 で **`gen3('BMS', L, zcap=1) = ST_TS ∩ {len <= L}`** が構成的に確定した
（`len<=7` の 77282 個で違反 0）ので、逆像の探索は **`gen3` の像の表**でよい。
`stts` の枝刈りも `preimage_try` の発見性も要らない。

    表   = `gen3('BMS', LB, zcap=1)` の像（＝ `ST_TS ∩ {len<=LB}` の像の全部）
    A    = `gen3('BMS', LA, zcap=1)` から**無作為に** NS 個（教訓: 先頭から取らない）
    判定 = m = 1..MM で `T = (conv3 A)⟦m⟧` が表に入るか
    破れの候補 = 末尾が外れ続ける A
"""
import sys, time, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import rows3, core
from rows3 import b2d3, gen3, key
from core import expand
from collections import Counter

LB = int(sys.argv[1]); LA = int(sys.argv[2])
MM = int(sys.argv[3]) if len(sys.argv) > 3 else 16
NS = int(sys.argv[4]) if len(sys.argv) > 4 else 3000
SEED = int(sys.argv[5]) if len(sys.argv) > 5 else 1

t0 = time.time()
IMG = set(); mx = 0
G = gen3('BMS', LB, zcap=1)
print('表 gen3(BMS,<=%d,zcap=1) = %d 個（= ST_TS ∩ {len<=%d}）(%.0fs)'
      % (LB, len(G), LB, time.time() - t0), flush=True)
t0 = time.time()
for i, B in enumerate(G):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    im = b2d3(list(B))
    IMG.add(bytes(x for c in im for x in c))
    if len(im) > mx:
        mx = len(im)
print('  像の集合 %d 件（最大の長さ %d）(%.0fs)' % (len(IMG), mx, time.time() - t0),
      flush=True)
del G

P = [tuple(map(tuple, M)) for M in gen3('BMS', LA, zcap=1) if len(M) > 1]
random.seed(SEED)
S = random.sample(P, min(NS, len(P)))
print('A: gen3(BMS,<=%d,zcap=1) の |A|>1 %d 個から**無作為に** %d 個  m=1..%d'
      % (LA, len(P), len(S), MM), flush=True)
del P

c = Counter(); tail = []
t0 = time.time()
for i, A in enumerate(S):
    if i % 500 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    fA = tuple(tuple(x) for x in b2d3(list(A)))
    hits = []
    for m in range(1, MM + 1):
        T = tuple(tuple(x) for x in expand(fA, m))
        if not T:
            hits.append('-'); continue
        if len(T) > mx:
            hits.append('?'); c['測れない（|T| > 表の最大 %d）' % mx] += 1; continue
        if bytes(x for cc in T for x in cc) in IMG:
            hits.append('O'); c['**逆像あり**'] += 1
        else:
            hits.append('.'); c['逆像なし |T|=%d' % len(T)] += 1
    s = ''.join(hits)
    c['並び ' + s] += 1
    if s.rstrip('-?').endswith('.'):
        tail.append((A, s))
print('  %.0fs' % (time.time() - t0))
print('== 判定')
for k in sorted(c, key=str):
    if k.startswith('**') or k.startswith('測れ'):
        print('   %-40s %d' % (k, c[k]))
print('   逆像なしの合計 %d'
      % sum(v for k, v in c.items() if k.startswith('逆像なし')))
print('== 並びの型（先頭 10）')
for k, n in Counter({k[3:]: v for k, v in c.items() if k.startswith('並び ')}).most_common(10):
    print('   %-20s %d' % (k, n))
print('== **末尾が外れ続ける A（ImgCofinalT の破れの候補）: %d / %d**'
      % (len(tail), len(S)))
for A, s in tail[:10]:
    print('   %-18s %s' % (s, ''.join(str(x).replace(' ', '') for x in A)))
