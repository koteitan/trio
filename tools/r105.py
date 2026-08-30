# -*- coding: utf-8 -*-
"""**R99-b —— 下げる方向（`lowerAt`）の不安定性。L3 の課題 L119 / `WConvexUnit` 用。**

`L53.lowerAt C j0`（`L53Subst:3453`）= **1 列 `j0` だけ行 1 を 1 下げる**（`Nat` 減算）。
`L53.WConvexUnit`（`:3505`）= `A ∈ W a`, `C ∈ W a`, `Le1 A B`, `Le1 B C`,
`B` と `C` は `j0` でだけ違い `entry C 1 j0 = entry B 1 j0 + 1` ⟹ `B ∈ W a`。
（`B = lowerAt C j0`。）

**測ること（team-lead の「展開の不安定性」）**:

  (w1) `srow`（最終列）が変わるか
  (w2) バッドルート `j0'` が変わるか
  (w3) 錐 `le1 X 0 ·` が変わるか
  (w4) ★ **展開と可換か**: `(lowerAt C j0)⟦n⟧` は `C⟦n⟧` を「どこか 1 列下げたもの」か
       可換なら L3 の帰納がそのまま回る。可換でないならそこが壁

⚠ 行 1 が 0 の列を下げても `Nat` 減算で恒等 ⟹ **`entry C 1 j0 >= 1` の場合だけ数える**。
⚠ `Trio.lean:98` の `oper` を使う（`oper_lean`）。
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r98 import oper_lean


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def badroot(S):
    j1 = len(S) - 1
    if j1 == 0:
        return ('ident', None)
    if S[j1][0] == 0 and S[j1][1] == 0 and S[j1][2] == 0:
        return ('zero', None)
    i1 = srow(S, j1)
    p = trio.parent(S, i1, j1)
    return (('noparent', None) if p is None else ('copy', p))


def lowerAt(C, j0):
    return [(c[0], c[1] - 1 if i == j0 and c[1] >= 1 else c[1], c[2])
            for i, c in enumerate(C)]


def cone(X):
    return frozenset(j for j in range(len(X)) if trio.is_ancestor(X, 1, 0, j))


def run(DS, BS, CS, VS, ZS, LS, NS, label):
    COL = [(d, b, c) for d in DS for b in BS for c in CS]
    n = 0
    r = Counter(); ex = {}
    t0 = time.time()
    for L in LS:
        for Rt in itertools.product(COL, repeat=L):
            R = list(Rt)
            if any(p[0] < 1 for p in R):
                continue
            for v in VS:
                for z in ZS:
                    C = [(0, v, z)] + R
                    for jj in range(len(C)):
                        if C[jj][1] < 1:
                            continue                       # 下げても恒等
                        n += 1
                        B = lowerAt(C, jj)
                        r['(w1) srow(最終列) 変化/' +
                          ('同じ' if srow(C, len(C) - 1) == srow(B, len(B) - 1)
                           else '**変わる**')] += 1
                        bc, bb = badroot(C), badroot(B)
                        r['(w2) バッドルート 変化/' +
                          ('同じ' if bc == bb else '**変わる**')] += 1
                        r['(w3) 錐 変化/' +
                          ('同じ' if cone(C) == cone(B) else '**変わる**')] += 1
                        # (w4) 展開のあとも「行 0・行 2 が同じで行 1 が 0 か 1 だけ低い」か
                        lenok = unit = le1ok = True
                        maxdiff = 0
                        for nn in NS:
                            EC, EB = oper_lean(C, nn), oper_lean(B, nn)
                            if len(EC) != len(EB):
                                lenok = False; unit = False; le1ok = False; break
                            for i in range(len(EC)):
                                if EC[i][0] != EB[i][0] or EC[i][2] != EB[i][2]:
                                    le1ok = False
                                if EB[i][1] > EC[i][1]:
                                    le1ok = False
                                elif EC[i][1] - EB[i][1] > 1:
                                    unit = False
                            maxdiff = max(maxdiff,
                                          sum(1 for i in range(len(EC))
                                              if EC[i] != EB[i]))
                        r['(w4a) 展開後も長さが同じ/' +
                          ('ok' if lenok else '**破れる**')] += 1
                        r['(w4b) 展開後も行 0・行 2 が同じで行 1 が下/' +
                          ('ok' if le1ok else '**破れる**')] += 1
                        r['(w4c) 展開後も差は各列 <= 1（unit のまま）/' +
                          ('ok' if (lenok and unit) else '**破れる**')] += 1
                        r[f'  (w4) 差の列数 {min(maxdiff,5)}{"+" if maxdiff>5 else ""}'] += 1
                        if not lenok and 'w4a 破れ（長さが変わる）' not in ex:
                            ex['w4a 破れ（長さが変わる）'] = (C, jj, B,
                                [oper_lean(C, nn) for nn in NS[:2]],
                                [oper_lean(B, nn) for nn in NS[:2]])
                        if lenok and not unit and 'w4c 破れ（差が 2 以上）' not in ex:
                            ex['w4c 破れ（差が 2 以上）'] = (C, jj, B,
                                [oper_lean(C, nn) for nn in NS[:2]],
                                [oper_lean(B, nn) for nn in NS[:2]])
    dt = time.time() - t0
    print(f'### {label}  ({dt:.1f}s)  母数 **{n}**')
    for k in sorted(r):
        print(f'  {k:52s} {r[k]:10d}  ({100*r[k]/max(n,1):5.1f}%)')
    for k in sorted(ex):
        print(f'  ★ 最小の {k}:')
        print(f'      C={ex[k][0]}  j0={ex[k][1]}  B={ex[k][2]}')
        print(f'      C⟦n⟧={ex[k][3]}')
        print(f'      B⟦n⟧={ex[k][4]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=3)
    a = ap.parse_args()
    run((1, 2, 3), (0, 1, 2, 3), (0, 1, 2), (0, 1, 2, 3), (0, 1),
        tuple(range(1, a.L + 1)), (1, 2, 3),
        f'R99-b `lowerAt` の不安定性 |R|<={a.L}')
