# -*- coding: utf-8 -*-
"""**F2b（`z = 1`）の構造 —— 復活を認めた上で、展開が何になるか。**

**背景**: §93 で「ブロック内で孤児 ⟹ 塔でも孤児」は **F2b では偽**と確定
（私の §R132 の 1,812 件）。§R134 で **親は必ず「1 つ前のブロック」**、
**`q_parent ∈ [1, |Q|-2]`**、そして **`n = 2` に完全に還元できる**ことも出た。

**⟹ 残るのは「復活したときに `T⟦m⟧` が何になるか」。**

**私の導出（先に書く。教訓 45）**:
`T = mTower Q d e n`、`last = |T|-1 = n*|Q|-1`、`j0` はブロック `n-2` の列 `q`。

    **`Lb = last − j0 = (n-1)*|Q| + (|Q|-1) − ((n-2)*|Q| + q) = 2*|Q| − 1 − q`**
    `q ∈ [1, |Q|-2]` ⟹ **`Lb ∈ [|Q|+1, 2*|Q|−2]` ⟹ 必ず `Lb > |Q|`**
    ⟹ **複製される塊はブロック境界をまたぐ**（L3 の観察どおり）
    ⟹ **`T.take j0 = mTower Q d e (n-2) ++ (ブロック n-2 の先頭 q 列)`**

**測るもの**:

    **(k1)** `Lb` の分布。**`Lb > |Q|` が本当に 100% か**
    **(k2)** `d0`, `d1` の値
    **(k3) ★本命** `T⟦m⟧` の**末尾列がまた F2b か**（再帰するか）。
            再帰するなら無限後退、しないなら底に着く
    **(k4)** `T⟦m⟧` の長さと、そこに現れる「ブロック」の形

**箱と単位**: 単位 `(Q,d,e,n,m)`。箱 = 行0<4, 行1<3, 行2<=cm、`|Q| = 3..5`、
`d,e ∈ 0..3`、`n ∈ {2,3}`、`m ∈ {1,2,3}`。母集団 = **F2b かつ塔で復活する**もの。
**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow, hasP, le1_root, classify
from r113 import mTower
from r98 import oper_lean


def isF2b(S):
    """`S` の末尾列が F2b（srow=2 ∧ 錐の中 ∧ 行 2 が根以下）か。"""
    j = len(S) - 1
    return (srow(S, j) == 2 and le1_root(S, j) and S[j][2] <= S[0][2])


def run(cm, L, DE, NS, MS):
    COL = [(a, b, c) for a in range(4) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            Q = [root] + list(t)
            if hasP(Q):
                continue
            i, fs = classify(Q)
            if '+'.join(f.split()[0] for f in fs) != 'F2b':
                continue
            for d in DE:
                for e in DE:
                    for n in NS:
                        T = [tuple(x) for x in mTower(Q, d, e, n)]
                        last = len(T) - 1
                        sr = srow(T, last)
                        j0 = trio.parent(T, sr, last)
                        if j0 is None:
                            continue                      # 復活したものだけ
                        c['★ 復活した件数'] += 1
                        Lb = last - j0
                        c[('Lb > |Q|', Lb > L)] += 1
                        c[('Lb - |Q|', Lb - L)] += 1
                        kp, qp = divmod(j0, L)
                        c[('親のブロック戻り', (n - 1) - kp)] += 1
                        c[('親の列 q', qp)] += 1
                        d0 = T[last][0] - T[j0][0]
                        d1 = (T[last][1] - T[j0][1]) if sr > 1 else 0
                        c[('d0 == d', d0 == d)] += 1
                        c[('d1 == e', d1 == e)] += 1
                        c[('d1 の値', d1 if d1 <= 4 else '>=5')] += 1
                        for m in MS:
                            R2_ = oper_lean(T, m)
                            c[('展開の分母', m)] += 1
                            if len(R2_) < 2:
                                c[('展開が短い（|.|<2）', m)] += 1
                                continue
                            f2b2 = isF2b(R2_)
                            c[('★ 展開もまた F2b', m, f2b2)] += 1
                            c[('展開の srow', m, srow(R2_, len(R2_) - 1))] += 1
                            c[('展開の長さ / |T|', m, min(len(R2_) // max(len(T), 1), 4))] += 1
                            if f2b2:
                                ex.setdefault('再帰', (Q, d, e, n, m, len(T), len(R2_)))
                            else:
                                ex.setdefault('非再帰', (Q, d, e, n, m, len(T), len(R2_),
                                                      srow(R2_, len(R2_) - 1)))
    tot = c['★ 復活した件数']
    print(f'### 行2<={cm} |Q|={L}  復活 {tot:8d} 件  [{time.time()-t0:.1f}s]')
    if not tot:
        print('  （復活が 0 件。この箱では測れない）\n')
        return
    print(f'  **(k1) `Lb > |Q|`: {c[("Lb > |Q|", True)]:8d} / {tot} '
          f'({100*c[("Lb > |Q|", True)]/tot:6.2f}%)**   '
          f'`Lb - |Q|` の分布 ' + str(dict(sorted((k[1], c[k]) for k in c
                                             if isinstance(k, tuple) and k[0] == 'Lb - |Q|'))))
    print('  親のブロック戻り: ', dict(sorted((k[1], c[k]) for k in c
                                     if isinstance(k, tuple) and k[0] == '親のブロック戻り')),
          '  親の列 q: ', dict(sorted((k[1], c[k]) for k in c
                                 if isinstance(k, tuple) and k[0] == '親の列 q')))
    print(f'  **(k2) `d0 == d`: {c[("d0 == d", True)]}/{tot}  '
          f'`d1 == e`: {c[("d1 == e", True)]}/{tot}**  '
          f'`d1` の値 ' + str(dict(sorted(((k[1], c[k]) for k in c
                                      if isinstance(k, tuple) and k[0] == 'd1 の値'), key=str))))
    for m in MS:
        dn = c[('展開の分母', m)]
        if not dn:
            continue
        yes = c[('★ 展開もまた F2b', m, True)]; no = c[('★ 展開もまた F2b', m, False)]
        print(f'  **(k3) m={m}: 分母 {dn:8d}  展開もまた F2b {yes:8d} '
              f'({100*yes/max(yes+no,1):6.2f}%)  そうでない {no:8d}**  '
              f'展開の srow ' + str({k[2]: c[k] for k in c if isinstance(k, tuple)
                                 and k[0] == '展開の srow' and k[1] == m}))
    for k in sorted(ex, key=str):
        print(f'      例 {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=5)
    a = ap.parse_args()
    for cm in (1, 2):
        for L in range(3, a.L + 1):
            run(cm, L, range(4), (2, 3), (1, 2, 3))
