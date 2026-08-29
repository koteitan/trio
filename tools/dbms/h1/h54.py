# -*- coding: utf-8 -*-
"""**課題 H53 —— タイ側の「組み直し」。**

`R = R1 ++ [tie] ++ R2`（`tie` は行 1 = `v` の**最後**の列）を割ったあと、
どう戻すか。母集団は H49-0 の正しい作り方（タイの場面）。
"""
import sys, io, contextlib
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
with contextlib.redirect_stdout(io.StringIO()):
    import h51
import trio, h50, h53
import probe_tiefree_tower as PT
from collections import Counter

tie = [s for s in h51.scenes if not all(p[1] != s[3] for p in s[2])]
print('母集団: タイの場面 **%d 件**（H49-0 の正しい作り方）' % len(tie))
print()


def parts(R, v):
    t = max(i for i, p in enumerate(R) if p[1] == v)
    return R[:t], R[t], R[t + 1:], t


# ---- H53-a ---------------------------------------------------------
print('**H53-a `R2` は `tie` の下にぶら下がるか**（`∀ p ∈ R2, tie の行 0 < p の行 0`）')
c = Counter()
exa = []
for M, j, R, v in tie:
    R1, tp, R2, t = parts(R, v)
    if not R2:
        c['`R2` が空'] += 1
        continue
    lt = all(tp[0] < p[0] for p in R2)
    le = all(tp[0] <= p[0] for p in R2)
    c['**真に深い**' if lt else ('以上（等号あり）' if le else '**浅い列がある**')] += 1
    if not le and len(exa) < 3:
        exa.append((M, j, R, v, tp, R2))
n = sum(c.values())
for k, v2 in c.most_common():
    print('   %-20s %5d (%.1f%%)' % (k, v2, 100.0 * v2 / n))
if exa:
    print('   浅い列がある例:')
    for M, j, R, v, tp, R2 in exa:
        print('      v=%d tie=%s R2=%s' % (v, tp, h53.sh(R2)))
print()

# ---- H53-b ---------------------------------------------------------
print('**H53-b `graft` の形に書けるか**')
print('   `R2\'\' := [(0, tie.1, tie.2)] ++ (R2 の行 0 から tie の行 0 を引いたもの)` と置くと')
print('   `graft ((0,v,z) :: R1 ++ [tie]) R2\'\' = (0,v,z) :: R` は**構成から恒等**。')
print('   本当の中身は **clause 3 が使えるか**（`domT` と `R2\'\' ∈ W m`）:')
cb = Counter()
exb = []
for M, j, R, v in tie:
    R1, tp, R2, t = parts(R, v)
    base = [(0, v, 0)] + R1 + [tp]
    jj = len(base) - 1
    sr = h50.srow(base, jj)
    orph = trio.parent([tuple(q) for q in base], sr, jj) is None
    lev = 2 * tp[1] + tp[2]
    R2p = [(0, tp[1], tp[2])] + [(p[0] - tp[0], p[1], p[2]) for p in R2]
    ident = ([tuple(q) for q in PT.graft(list(base), R2p)]
             == [tuple(q) for q in ([(0, v, 0)] + R)])
    cb['恒等式が成立'] += ident
    cb['**`tie` が `(0,v,z)::R1++[tie]` で孤児（`domT` の前提）**'] += orph
    cb['`lev tie > 0`'] += (lev > 0)
    cb['**両方（clause 3 が使える）**'] += (orph and lev > 0)
    if not orph and len(exb) < 3:
        exb.append((v, tp, sr, base))
N = len(tie)
for k in ('恒等式が成立', '**`tie` が `(0,v,z)::R1++[tie]` で孤児（`domT` の前提）**',
          '`lev tie > 0`', '**両方（clause 3 が使える）**'):
    print('   %-46s **%5d / %d (%.1f%%)**' % (k, cb[k], N, 100.0 * cb[k] / N))
if exb:
    print('   `tie` が孤児でない例（`srow` と親の有無）:')
    for v, tp, sr, base in exb:
        print('      v=%d tie=%s srow=%d  base=%s' % (v, tp, sr, h53.sh(base)))
print()

# ---- H53-c ---------------------------------------------------------
print('**H53-c `split_lastMin` の分割は `tie` の位置と一致するか**')
cc = Counter()
for M, j, R, v in tie:
    R1, tp, R2, t = parts(R, v)
    X = [(0, v, 0)] + R
    A, P = h53.split_lastMin(X)
    cc['`X` の分割位置'] = None
    cc['`X` で `A = []`（根が唯一の最小）'] += (len(A) == 0)
    A2, P2 = h53.split_lastMin(R)
    i2 = len(A2)
    cc['`R` の分割が `tie` と一致'] += (i2 == t)
    cc['`R` の分割が `tie` より**右**'] += (i2 > t)
    cc['`R` の分割が `tie` より**左**'] += (i2 < t)
del cc['`X` の分割位置']
for k in ('`X` で `A = []`（根が唯一の最小）', '`R` の分割が `tie` と一致',
          '`R` の分割が `tie` より**右**', '`R` の分割が `tie` より**左**'):
    print('   %-36s **%5d / %d (%.1f%%)**' % (k, cc[k], N, 100.0 * cc[k] / N))
print()
print('   ⟹ `(0,v,z) :: R` に `split_lastMin` を当てても、根が唯一の行 0 最小なので')
print('      **必ず `A = []`、分割は起きない**（`argOK R` から構造的）。')
