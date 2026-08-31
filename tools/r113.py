# -*- coding: utf-8 -*-
"""**課題 R113 —— マスクはブロック局所か。`mTower` と `operTower` は一致するか。**

    `mTower Q d e n`   = `concat_{k<n} Lift1 (shiftr01 (k*d) 0 Q) (k*e)`
                          … マスクを **`Q` の中で**計算（ブロック局所）＝ R2 / H12 の形
    `operTower Q d e n` = `T_0 = []`,  `T_{k+1} = Q ++ shiftr01 d 0 (Lift1 T_k e)`
                          … マスクを **塔全体の上で**計算 ＝ `oper_cons_tower2` が実際に作る形

⚠ `Wset.le1_take`（`:908`、緑）は **接頭辞局所性**しか与えない
   （`le1 (X.take l) a b ↔ le1 X a b`、`b < l`）。
   ⟹ ブロック 0 のマスクが `Q` だけで決まることは出るが、
      **第 `k` ブロック（`k>=1`）のマスクが `Q` だけで決まることは Lean では出ない。**
   ⟹ **実測で真でも「証明できる」ではない**（教訓 14 の逆側の注意）。ここで測るのは**真偽だけ**。

  (q1) 一致率。**分母と単位を必ず**（塔単位 / ブロック単位 / 列単位）
  (q2) ★ 陰性対照: ブロッカーがある `Q` で、第 2 ブロックのマスクが第 1 ブロックと違う例を探す
  (q3) 陽性対照: わざと壊した版（マスクを 1 列ずらす）が鳴るか
  (q4) `|Q|` と `n` を伸ばして壊す（教訓 21）
"""
import sys, itertools, random, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def lev(c):
    return 2 * c[1] + c[2]


def Lift1(X, dd):
    return [(c[0], c[1] + (dd if trio.is_ancestor(X, 1, 0, i) else 0), c[2])
            for i, c in enumerate(X)]


def Lift1_bad(X, dd):
    """陽性対照: マスクを 1 列ずらした偽版。"""
    m = [trio.is_ancestor(X, 1, 0, i) for i in range(len(X))]
    m = [False] + m[:-1]
    return [(c[0], c[1] + (dd if m[i] else 0), c[2]) for i, c in enumerate(X)]


def sh(X, d0):
    return [(c[0] + d0, c[1], c[2]) for c in X]


def mTower(Q, d, e, n, lift=Lift1):
    out = []
    for k in range(n):
        out += lift(sh(Q, k * d), k * e)
    return out


def operTower(Q, d, e, n, lift=Lift1):
    T = []
    for _ in range(n):
        T = list(Q) + sh(lift(T, e), d)
    return T


def run(gen, NS, label, lift=Lift1, tag='本物'):
    tw = Counter(); blk = Counter(); col = Counter(); ex = {}
    for Q, d, e, has_blk in gen:
        for n in NS:
            A = mTower(Q, d, e, n, lift)
            B = operTower(Q, d, e, n, lift)
            same = (A == B)
            tw[('塔単位', 'ok' if same else '**不一致**')] += 1
            if len(A) == len(B):
                for k in range(n):
                    a = A[k * len(Q):(k + 1) * len(Q)]
                    b = B[k * len(Q):(k + 1) * len(Q)]
                    blk[('ブロック単位', 'ok' if a == b else '**不一致**')] += 1
                for i in range(len(A)):
                    col[('列単位', 'ok' if A[i] == B[i] else '**不一致**')] += 1
            else:
                blk[('ブロック単位', '**長さが違う**')] += 1
            if not same:
                key = 'ブロッカー有' if has_blk else 'ブロッカー無'
                if key not in ex:
                    ex[key] = (Q, d, e, n, A, B)
    print(f'### {label}（{tag}）')
    for c, nm in ((tw, '塔'), (blk, 'ブロック'), (col, '列')):
        s = sum(c.values())
        if not s:
            continue
        for k in sorted(c):
            print(f'  {k[0]:12s} {k[1]:14s} {c[k]:10d} / {s:10d} '
                  f'({100*c[k]/s:6.2f}%)')
    for k in sorted(ex):
        print(f'  ★ 最小の不一致（{k}）: Q={ex[k][0]} d={ex[k][1]} e={ex[k][2]} n={ex[k][3]}')
        print(f'      mTower    = {ex[k][4]}')
        print(f'      operTower = {ex[k][5]}')
    print()


def scene_gen(COL, VS, ZS, Ls, sample_from=5, sample=120000, seed=20260830):
    rng = random.Random(seed)
    for L in Ls:
        smp = sample if L >= sample_from else None
        src = ([rng.choice(COL) for _ in range(L)] for _ in range(smp)) if smp \
            else (list(x) for x in itertools.product(COL, repeat=L))
        for R in src:
            if any(p[0] < 1 for p in R):
                continue
            j = len(R) - 1
            i1 = srow(R, j)
            if i1 != 2 or trio.parent(R, i1, j) is not None or lev(R[j]) - 1 < 0:
                continue
            for v in VS:
                for z in ZS:
                    if trio.parent([(0, v, z)] + R, i1, len(R)) is None:
                        continue
                    Q = [(0, v, z)] + R[:-1]
                    d = R[j][0]
                    e = R[j][1] - v
                    yield Q, d, e, any(p[1] <= v for p in R[:-1])


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=5)
    ap.add_argument('--n', type=int, default=5)
    a = ap.parse_args()
    COL = [(d, b, c) for d in (1, 2) for b in (0, 1, 2) for c in (0, 1)]
    NS = tuple(range(2, a.n + 1))
    Ls = tuple(range(2, a.L + 1))
    run(scene_gen(COL, (0, 1, 2), (0, 1), Ls), NS,
        f'R113 塔の場面（H12 の箱）|R|<={a.L}, n=2..{a.n}')
    # (q2) ブロッカーがあるものだけに絞る
    run(((Q, d, e, b) for Q, d, e, b in scene_gen(COL, (0, 1, 2), (0, 1), Ls) if b),
        NS, f'R113 (q2) **ブロッカーがある `Q` だけ** |R|<={a.L}')
    # (q3) 陽性対照
    run(scene_gen(COL, (0, 1, 2), (0, 1), (2, 3)), (2, 3),
        'R113 (q3) 陽性対照（マスクを 1 列ずらした偽版）', Lift1_bad, '偽版')


def mechanism(COL, VS, ZS, Ls, NS, label, sample_from=5, sample=40000):
    """★ なぜブロック局所になるのか —— 錐の外の列は「同じブロック内」にブロッカーを持つか。

    `Lcone.le1_zero_iff`（緑）: `¬le1 T 0 j ⟺ ∃ y ∈ anc0(T,j), y≠0, entry T 1 y <= v`。
    ブロック `k` の列 `j` について、その `y` が**ブロック `k` の中**に取れるなら、
    マスクはブロック局所になる（＝ 外に出る祖先はブロッカーにならない）。
    """
    import random
    rng = random.Random(20260830)
    r = Counter(); ex = {}
    for Q, d, e, hb in scene_gen(COL, VS, ZS, Ls, sample_from, sample):
        for n in NS:
            T = operTower(Q, d, e, n)
            if not T:
                continue
            v0 = T[0][1]
            for j in range(len(T)):
                k = j // len(Q)
                if trio.is_ancestor(T, 1, 0, j):
                    r['錐の中'] += 1
                    continue
                ch = [j]
                while True:
                    p = trio.parent(T, 0, ch[-1])
                    if p is None:
                        break
                    ch.append(p)
                blk_in = [y for y in ch if y != 0 and T[y][1] <= v0
                          and y // len(Q) == k]
                blk_out = [y for y in ch if y != 0 and T[y][1] <= v0
                           and y // len(Q) != k]
                if blk_in:
                    r['錐の外 / **同ブロック内にブロッカーあり**'] += 1
                elif blk_out:
                    r['錐の外 / **外のブロックにしか無い**'] += 1
                    ex.setdefault('外だけ', (Q, d, e, n, j, k, ch, blk_out))
                else:
                    r['錐の外 / ブロッカーが無い（**あり得ないはず**）'] += 1
                    ex.setdefault('なし', (Q, d, e, n, j, ch))
    print(f'### {label}')
    s = sum(r.values())
    for k in sorted(r):
        print(f'  {k:44s} {r[k]:10d} / {s:10d} ({100*r[k]/max(s,1):6.2f}%)')
    for k in sorted(ex):
        print(f'  ★ {k}: {ex[k]}')
    print()
