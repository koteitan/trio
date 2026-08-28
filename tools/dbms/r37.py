# -*- coding: utf-8 -*-
"""課題 R24 ＋ R23: **弱い性質 R** と、`preimage_try` による三つ組を 1 回の走りで。

  A ∈ ST_TS、m = 2..MMAX、T = (conv3 A)⟦m⟧ について
    (a) ∃ n' >= 1 : conv3 (A⟦n'⟧) == T          ← **性質 R そのもの**
    (b) (a) が偽のとき preimage_try で B が取れるか
    (c) B が取れたとき、B と最も近い A⟦n'⟧ の差の形

  (a) 真          … `ImgCofinalT` が自明
  (a) 偽 & (b) 真 … 非自明だが逆像はある
  (a) 偽 & (b) 偽 … **`ImgCofinalT` の破れの候補**
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7, inv3
from rows3 import b2d3, preimage_try
from core import expand
from collections import Counter

v, L = int(sys.argv[1]), int(sys.argv[2])
MMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 16
NR = int(sys.argv[4]) if len(sys.argv) > 4 else 16
TCAP = int(sys.argv[5]) if len(sys.argv) > 5 else 80   # |T| がこれを超えたら測らない
f = lambda X: [tuple(y) for y in b2d3(X)]

P = [M for M in r7.stts_pool(v, L) if len(M) > 1]
print('A 側 ST_TS v<=%d len<=%d の |A|>1  **%d 個**  m=2..%d  n\'=1..%d'
      % (v, L, len(P), MMAX, NR), flush=True)
c = Counter(); ex = []; tail = []; PAT = []
t0 = time.time()
for i, A in enumerate(P):
    if i % 500 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        if i:
            print('   %d / %d (%.0fs)' % (i, len(P), time.time() - t0), flush=True)
    fA = tuple(tuple(x) for x in b2d3(list(A)))
    # A⟦n'⟧ の像を集める（性質 R の候補）
    RIMG = {}
    for n2 in range(1, NR + 1):
        An = expand(A, n2)
        if not An:
            break
        RIMG.setdefault(tuple(tuple(x) for x in b2d3(list(An))), n2)
    hits = []
    for m in range(2, MMAX + 1):
        T = tuple(tuple(x) for x in expand(fA, m))
        if not T:
            hits.append('-')
            continue
        c['_判定'] += 1
        if T in RIMG:
            c['**(a) 性質 R が成り立つ**'] += 1
            hits.append('R')
            continue
        if len(T) > TCAP:
            c['**測っていない（|T| > %d）**' % TCAP] += 1
            hits.append('?')
            continue
        B = preimage_try(f, T, inv3.d2b3)
        if B is not None:
            c['**(a) 偽 & (b) 真（逆像はある）**'] += 1
            hits.append('O')
            B = tuple(tuple(x) for x in B)
            # (c) 最も近い A⟦n'⟧ との差
            best = None
            for Rt, n2 in RIMG.items():
                An = tuple(tuple(x) for x in expand(A, n2))
                dl = len(B) - len(An)
                if best is None or abs(dl) < abs(best[0]):
                    best = (dl, n2, An)
            if best:
                c['(c) |B| - |A⟦n\'⟧| = %+d' % best[0]] += 1
                An = best[2]
                if B[:len(An)] == An:
                    c["(c) B は A⟦n'⟧ の**接頭辞拡張**"] += 1
                elif An[:len(B)] == B:
                    c["(c) B は A⟦n'⟧ の**接頭辞**"] += 1
                else:
                    c['(c) 接頭辞の関係なし'] += 1
                if len(ex) < 4 and best[0] != 0:
                    ex.append((A, m, best[1], An, B))
        else:
            c['**(a) 偽 & (b) 偽（ImgCofinalT の候補）**'] += 1
            hits.append('.')
            c['候補 |T|=%d' % len(T)] += 1
    s = ''.join(hits)
    PAT.append((A, s))
    if s.rstrip('-?').endswith('.'):
        tail.append((A, s))
print('  %.0fs' % (time.time() - t0))
print('== 判定 %d 回' % c['_判定'])
for k in sorted(c, key=str):
    if not k.startswith('_') and not k.startswith('候補 ') and not k.startswith('(c)'):
        print('   %-44s %d' % (k, c[k]))
print('== (c) B と最も近い A⟦n\'⟧ の差')
for k in sorted(c, key=str):
    if k.startswith('(c)'):
        print('   %-44s %d' % (k, c[k]))
print('== 候補の |T| 分布')
for k in sorted(c, key=str):
    if k.startswith('候補 '):
        print('   %-24s %d' % (k, c[k]))
print('== 末尾が外れ続ける A（ImgCofinalT の破れの候補）: **%d 個**' % len(tail))
for A, s in tail[:8]:
    print('   %-18s %s' % (s, ''.join(str(x).replace(' ', '') for x in A)))
import pickle
pickle.dump(PAT, open('/home/koteitan/proofs/dbms/tools/dbms/r37pat_%d_%d.pkl'
                      % (v, L), 'wb'))
print('== 当たり外れの並びを %d 件 pickle に保存' % len(PAT))
from collections import Counter as C2
print('   並びの型（先頭 12 種）:')
for k, n in C2(s for _, s in PAT).most_common(12):
    print('     %-20s %d' % (k, n))
for A, m, n2, An, B in ex:
    print('   ### (a) 偽・(b) 真の例  m=%d  最も近いのは n\'=%d' % (m, n2))
    print('      A     = %s' % ''.join(str(x).replace(' ', '') for x in A))
    print('      A⟦n\'⟧ = %s' % ''.join(str(x).replace(' ', '') for x in An))
    print('      B     = %s' % ''.join(str(x).replace(' ', '') for x in B))
