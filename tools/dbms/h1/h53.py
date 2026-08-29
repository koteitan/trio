# -*- coding: utf-8 -*-
"""**課題 H52 —— `D_2` / `D_1` を端から端まで通す。**

`lean/Wset.lean` の連鎖（`mem_W_of_bound_aux`、長さの帰納）:

    M != [] ⟹ split_lastMin: M = A ++ P, P != [], rsum A P,
              ∀ p ∈ P.tail, entry P 0 0 < p.1
    P = p0 :: R,  R' := shiftl0 p0.1 R  （argOK）
    Q := (0, p0.2.1, p0.2.2) :: R'      （= p_{v,z}(R')）
    Q ∈ W u  ←  R' ∈ Wstar（ここで TowerOK）
    W_shift で P に戻し、rsum で W_add ⟹ A ++ P ∈ W u
    A に再帰（長さが真に減る）

`split_lastMin` の具体形: `m = min(行 0)`、`i = 行 0 が m になる**最後の**添字`、
`A = M[:i]`, `P = M[i:]`（`rsum` と `P.tail` の狭義性がちょうど出る）。
"""
import sys, io, contextlib
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio, h50
from collections import Counter


def sh(M):
    return ''.join('(%d,%d,%d)' % tuple(q) for q in M)


def split_lastMin(M):
    m = min(p[0] for p in M)
    i = max(j for j, p in enumerate(M) if p[0] == m)
    return list(M[:i]), list(M[i:])


def rsum(A, B):
    r = B[0][0]
    return all(r <= p[0] for p in A) and all(r <= p[0] for p in B)


def trace(M, label):
    print('### 標的 `%s` = `%s`' % (label, sh(M)))
    print()
    print('| 段 | `M` | `A` | `P` | `p0`=(d,v,z) | `R\'` | `rsum A P` | `P.tail` が狭義 | `argOK R\'` |')
    print('|--:|---|---|---|---|---|---|---|---|')
    cur = [tuple(c) for c in M]
    k = 0
    nodes = []
    while cur:
        A, P = split_lastMin(cur)
        p0, R = P[0], P[1:]
        Rp = [(q[0] - p0[0], q[1], q[2]) for q in R]
        ok_r = rsum(A, P)
        ok_t = all(P[0][0] < q[0] for q in P[1:])
        ok_a = all(q[0] > 0 for q in Rp)
        print('| %d | `%s` | `%s` | `%s` | `(%d,%d,%d)` | `%s` | %s | %s | %s |'
              % (k, sh(cur), sh(A) or '[]', sh(P), p0[0], p0[1], p0[2],
                 sh(Rp) or '[]', 'OK' if ok_r else '**破れ**',
                 'OK' if ok_t else '**破れ**', 'OK' if ok_a else '**破れ**'))
        nodes.append((k, cur, A, P, p0, Rp, ok_r, ok_t, ok_a))
        cur = A
        k += 1
    print()
    print('**降りきるまでの段数: %d**' % len(nodes))
    bad = [n for n in nodes if not (n[6] and n[7] and n[8])]
    print('**仮定が破れる段: %s**' % ('**無し**' if not bad else [n[0] for n in bad]))
    print()
    print('各段の `R\'` が `Wstar` の場面としてどの枝に落ちるか:')
    print()
    print('| 段 | `R\'` | `v` | `z` | `srow` 末尾 | `domT R\'` | **復活** | 枝 |')
    print('|--:|---|--:|--:|--:|---|---|---|')
    for k2, cur2, A, P, p0, Rp, a, b, c in nodes:
        v, z = p0[1], p0[2]
        if not Rp:
            print('| %d | `[]` | %d | %d | — | — | — | **節 1（底）: `R\' = []`** |'
                  % (k2, v, z))
            continue
        j = len(Rp) - 1
        sr = h50.srow(Rp, j)
        dom = (2 * Rp[j][1] + Rp[j][2] > 0) and not h50.hp(Rp, j)
        X = [(0, v, z)] + Rp
        rev = trio.parent([tuple(q) for q in X], sr, len(Rp)) is not None
        if not dom:
            br = '`domT` が偽 ⟹ **節 2（展開）**'
        elif not rev:
            br = '復活しない ⟹ **節 3（graft）がそのまま**'
        elif sr == 1:
            br = '**`TowerOK1`**（証明ずみ）'
        else:
            notie = all(q[1] != v for q in Rp)
            strict = all(v < q[1] for q in Rp)
            br = ('**`TowerOK2` / 狭義**' if strict else
                  ('**`TowerOK2` / 無タイ**' if notie else '**`TowerOK2` / タイ**'))
        print('| %d | `%s` | %d | %d | %d | %s | %s | %s |'
              % (k2, sh(Rp), v, z, sr, 'True' if dom else 'False',
                 'する' if rev else 'しない', br))
    print()
    return nodes


D1 = [(0, 0, 0), (1, 1, 1)]
D2 = [(0, 0, 0), (1, 1, 1), (2, 2, 1)]
print('## `D_1`（= `psi(Omega_omega)`、2 行の極限）')
print()
n1 = trace(D1, 'D_1')
print('## `D_2`（= BM4 ブック全 7 シートより上）')
print()
n2 = trace(D2, 'D_2')
