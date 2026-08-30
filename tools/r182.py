# -*- coding: utf-8 -*-
"""(z3b) `V` は `Q` とどう違うか ＋ `Lift1` の補題が使えるか。

`L105Cap:2054`（逐語、緑、`sorry` 0）:

    theorem liftStage_of_zeroRow2 {m d : ℕ} {X : TrioSeq} (hz : ∀ p ∈ X, p.2.2 = 0)
        (hX : X ∈ W m) : Lift1 X d ∈ W (m + 2 * d)

⟹ **前提「行 2 ≡ 0」、代償「`W (m + 2*d)`」**。ここでは `d = e*(n-1)`。

**測る**: `p_rel = 0` の母集団で
  (i)  `Q` の行 2 が全部 0 か（`liftStage_of_zeroRow2` の前提）
  (ii) `V` と `shiftr01 δ 0 Q` の差は「行 1 だけ、`le1 Q 0 i` の列だけ、量 `e*(n-1)`」か
  (iii) 差が出る列は何本か
"""
import sys, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower, Lift1, sh
from r141 import block


def run(E, LS, NS, DE, nsamp, seed):
    COL = [(a, b, c) for a in range(E) for b in range(E) for c in (0, 1)]
    rnd = random.Random(seed); c = Counter()
    for _ in range(nsamp):
        L = rnd.choice(LS)
        root = rnd.choice(COL); hi = [x for x in COL if x[0] > root[0]]
        if not hi: continue
        Q = [root] + [rnd.choice(hi) for _ in range(L - 1)]
        d, e, n = rnd.choice(DE), rnd.choice(DE), rnd.choice(NS)
        T = [tuple(x) for x in mTower(Q, d, e, n)]
        S = T + block(Q, d, e, n)[:1]
        last = len(S) - 1
        par = trio.parent(S, srow(S, last), last)
        if par is None or par != (n - 1) * L: continue
        c['母集団 (j=0, p_rel=0)'] += 1
        V = [tuple(x) for x in S[par:last]]
        dl = V[0][0] - Q[0][0]
        base = [(p[0] + dl, p[1], p[2]) for p in Q]
        t = e * (n - 1)
        if all(p[2] == 0 for p in Q): c['(i) Q の行 2 が全部 0（補題の前提）'] += 1
        if t > 0 and all(p[2] == 0 for p in Q): c['(i) 上記 かつ リフト量 > 0'] += 1
        diff = [i for i in range(L) if V[i] != base[i]]
        if not diff: c['(ii) V = 純粋なずらし（差なし）'] += 1
        else:
            ok = all(V[i][0] == base[i][0] and V[i][2] == base[i][2]
                     and V[i][1] == base[i][1] + t for i in diff)
            msk = all(trio.is_ancestor(sh(Q, d*(n-1)), 1, 0, i) for i in diff)
            if ok: c['(ii) 差は行 1 だけ、量はちょうど `e*(n-1)`'] += 1
            else: c['⚠ (ii) それ以外の差'] += 1
            if msk: c['(ii) 差が出る列は全部 `le1 X 0 i`'] += 1
            c[('(iii) 差が出る列の本数', len(diff))] += 1
        c['行 0 のずらし量 delta の合計'] += dl
        if dl == d * (n - 1): c['(ii) delta = d*(n-1)'] += 1
    tt = c['母集団 (j=0, p_rel=0)']
    print(f'### 値域<{E} |Q|∈{LS} n∈{tuple(NS)} (d,e)∈{tuple(DE)}  母集団 {tt}')
    for k in sorted(x for x in c if isinstance(x, str) and x != '母集団 (j=0, p_rel=0)'
                    and not x.startswith('行 0')):
        print(f'    {k:44s} {c[k]:7d} ({100*c[k]/max(tt,1):6.2f}%)')
    print('    (iii) 差が出る列の本数: ',
          dict(sorted((k[1], c[k]) for k in c if isinstance(k, tuple))))
    print()


if __name__ == '__main__':
    run(4, (3, 4, 5, 6), (2, 3, 4), range(4), 60000, 101)
    run(6, (3, 4, 5, 6, 8), (2, 3, 4, 5), range(6), 60000, 103)
