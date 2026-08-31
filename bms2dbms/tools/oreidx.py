# -*- coding: utf-8 -*-
"""**課題 L28 の測定** —— 順序の破れ 24 件は `OrderReindexT3` に当たるか。

`lean/Dbms3.lean` の `ReindexT1_of_cofinal'` が使う順序は (←) だけで、しかも
相手 `B` は `(conv3 A)⟦m⟧ = conv3 B` を満たすものに限られる（`OrderReindexT3`）。
順序の破れ (X, Y)（入力 X < Y、像 f X > f Y）が Lean 側を壊すのは次のどちらか:

    (ii)  ∃ A ∈ ST_TS, n>=1, m>=n+1 :  A⟦n⟧ = Y  かつ  (conv3 A)⟦m⟧ = conv3 X
    (iii) ∃ m>=2                     :  (conv3 X)⟦m⟧ = conv3 Y

どちらも起きなければ、**順序が破れたままでも `ReindexT1` は通る**。

長さで先に切れる: `S⟦m⟧` の長さは `r + m*bp`（`|S| = r + bp`）なので
`m >= 2` なら `|S⟦m⟧| > |S|`。

使い方: python3 bms2dbms/tools/oreidx.py [v] [len]
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7, trio
from rows3 import b2d3
from core import expand

v = int(sys.argv[1]) if len(sys.argv) > 1 else 5
L = int(sys.argv[2]) if len(sys.argv) > 2 else 11

t0 = time.time()
P = r7.stts_pool(v, L)
print('母集団 ST_TS v<=%d len<=%d  %d 個  (%.0fs)' % (v, L, len(P), time.time() - t0),
      flush=True)

t0 = time.time()
IM = []
for i, M in enumerate(P):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    IM.append(tuple(tuple(c) for c in b2d3(list(M))))
print('  像 (%.0fs)' % (time.time() - t0), flush=True)

brk = [i for i in range(len(P) - 1) if IM[i] >= IM[i + 1]]
print('順序 (→) の破れ **%d 件**' % len(brk), flush=True)

# --- A⟦n⟧ の逆引き表（n = 1..3）
t0 = time.time()
pre = {}
for A in P:
    for n in (1, 2, 3):
        T = tuple(map(tuple, core.expand(A, n)))
        if T:
            pre.setdefault(T, []).append((A, n))
print('  A⟦n⟧ の逆引き表 %d 通り (%.0fs)' % (len(pre), time.time() - t0), flush=True)


def head_bad(S):
    """`|S| = r + bp` の `(r, bp)`。展開できないなら None。"""
    r = core.pim(S)
    return r


n_ii = n_iii = 0
ex_ii, ex_iii = [], []
for i in brk:
    X, Y = P[i], P[i + 1]
    fX, fY = IM[i], IM[i + 1]
    # (iii) (conv3 X)⟦m⟧ = conv3 Y   ——  m>=2 なら長さが伸びるので |fY| > |fX| が要る
    ok3 = False
    for m in range(2, 8):
        T = tuple(map(tuple, expand(fX, m)))
        if not T or len(T) > len(fY) + 4:
            break
        if T == fY:
            ok3 = True; break
    if ok3:
        n_iii += 1
        if len(ex_iii) < 3: ex_iii.append((X, Y))
    # (ii) A⟦n⟧ = Y かつ (conv3 A)⟦m⟧ = conv3 X
    ok2 = False
    for A, n in pre.get(Y, []):
        fA = tuple(tuple(c) for c in b2d3(list(A)))
        for m in range(n + 1, n + 8):
            T = tuple(map(tuple, expand(fA, m)))
            if not T or len(T) > len(fX) + 4:
                break
            if T == fX:
                ok2 = True; break
        if ok2:
            break
    if ok2:
        n_ii += 1
        if len(ex_ii) < 3: ex_ii.append((X, Y))

print(flush=True)
print('=== `OrderReindexT3` に当たるか', flush=True)
print('  (ii)  A⟦n⟧ = Y かつ (conv3 A)⟦m⟧ = conv3 X : **%d / %d**' % (n_ii, len(brk)),
      flush=True)
print('  (iii) (conv3 X)⟦m⟧ = conv3 Y               : **%d / %d**' % (n_iii, len(brk)),
      flush=True)
if n_ii == 0 and n_iii == 0:
    print('  ⟹ **24 件は `OrderReindexT3` を壊さない。Lean 側は通る。**', flush=True)
else:
    print('  ⟹ **壊す。順序を直す必要がある。**', flush=True)
    for X, Y in (ex_ii + ex_iii)[:3]:
        f = lambda M: ''.join('(%d,%d,%d)' % c for c in M)
        print('     X=%s' % f(X), flush=True)
        print('     Y=%s' % f(Y), flush=True)
