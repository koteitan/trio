# -*- coding: utf-8 -*-
"""**課題 R129（L3 の依頼）—— (A1)「塔 ＋ ブロック `n` の根 1 列」の構造。**

**主語**: `S = mTower Q d e n ++ [ブロック n の根]`、`j = |S|-1 = n*|Q|`。
ブロック `n` の根は `mTower Q d e (n+1)` の位置 `n*|Q|` **そのもの**を取る（写し間違い防止）。

**使える緑の補題の主語（逐語で写した）:**

    `L105Cap:144` **`snoc_orphan_W`** (p) (hC : C ∈ W u) (hCne : C ≠ [])
        (hnp : ¬ hasParent (C ++ [p]) (srow (C ++ [p]) |C|) |C|) : `C ++ [p] ∈ W u`
      ⟹ 主語 `C ++ [p]`。**(A1) と一致する** ✅

    `Wtower2:2208` **`snoc_flat_root`** (hC) (hCne)
        **(hsr : srow (C ++ [p]) |C| = 0)**   ← ⚠ **足す列が「フラット」であることが要る**
        (hbp : parent (C ++ [p]) (srow …) |C| = 0)   (hpar : hasParent …)
      ⟹ **「親が根」だけでは足りない。`srow = 0` も要る。**
        ブロック `n` の根の `srow` は `z > 0` なら 2、`entry Q 1 0 + e*n > 0` なら 1。
        ⟹ **`z = 0` かつ `entry Q 1 0 = 0` かつ `e*n = 0` のときしか当たらない。**

**(c2) L3 の予想**: 「ブロック `n-1` の根が**行 0 の親**になる ⟹ 孤児ではない」
⚠ **私の疑い（先に書く。教訓 45）**: **行 0 に親があっても `srow` が 2 なら意味が無い。**
`hasParent S (srow S j) j` が要るのは **行 `srow`** の親であって行 0 ではない。
⟹ **`z = 1`（`srow = 2`）では孤児のままの可能性が高い。**

**箱と単位**: 単位 `(Q, d, e, n)`。箱 = 行0<4, 行1<3, 行2<=cm（**3 段**）、
`|Q| = 2..4`、`d,e ∈ 0..3`、`n ∈ {1,2,3}`。
母集団 = `2<=|Q|` ∧ **根が狭義最浅** ∧ **`HasParentInBlock Q`**（残差 A の前提）。
**`W` 所属は判定しない。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r126 import srow, hasP
from r113 import mTower


def run(cm, L, DE, NS, need_hblk):
    COL = [(a, b, c) for a in range(4) for b in range(3) for c in range(cm + 1)]
    c = Counter(); ex = {}
    t0 = time.time()
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            Q = [root] + list(t)
            if need_hblk and not hasP(Q):
                continue
            z = root[2]
            for d in DE:
                for e in DE:
                    for n in NS:
                        big = [tuple(x) for x in mTower(Q, d, e, n + 1)]
                        C = big[:n * L]
                        S = C + [big[n * L]]
                        j = len(S) - 1
                        i = srow(S, j)
                        p = trio.parent(S, i, j)
                        c['分母'] += 1
                        c[('srow(p)', i)] += 1
                        c[('z', z)] += 1
                        if p is None:
                            c['★ 孤児（snoc_orphan_W で無料）'] += 1
                            c[('孤児srow', i)] += 1
                            c[('孤児z', z)] += 1
                            ex.setdefault(('孤児', i), (Q, d, e, n))
                            continue
                        kp, qp = divmod(p, L)
                        c[('親のブロック戻り', (n - 1) - kp)] += 1
                        c[('親の列', qp)] += 1
                        if p == 0:
                            c['親 = 根（index 0）'] += 1
                            if i == 0:
                                c['★★ snoc_flat_root の全前提が成立'] += 1
                        # (c2) L3 の予想: 行 0 の親がブロック n-1 の根か
                        p0 = trio.parent(S, 0, j)
                        if p0 == (n - 1) * L:
                            c['(c2) 行0の親 = ブロック n-1 の根'] += 1
                        c[('(c2) 行0の親の戻り', ((n - 1) - (p0 // L)) if p0 is not None else None)] += 1
    tot = c['分母']
    print(f'### 行2<={cm} |Q|={L} hblk={"要求" if need_hblk else "落とす"}  '
          f'分母 {tot:9d}  [{time.time()-t0:.1f}s]')
    orp = c['★ 孤児（snoc_orphan_W で無料）']
    print(f'  **(c1) 孤児（＝ `snoc_orphan_W` で無料）: {orp:9d} ({100*orp/max(tot,1):6.2f}%)**')
    for i in (0, 1, 2):
        n_ = c[('srow(p)', i)]
        if n_:
            print(f'      srow(足す列)={i}: 分母 {n_:9d}  孤児 {c[("孤児srow", i)]:9d} '
                  f'({100*c[("孤児srow", i)]/n_:6.2f}%)')
    for z in range(cm + 1):
        n_ = c[('z', z)]
        if n_:
            print(f'      z={z}: 分母 {n_:9d}  孤児 {c[("孤児z", z)]:9d} ({100*c[("孤児z", z)]/n_:6.2f}%)')
    print(f'  **(c3) 親 = 根（index 0）: {c["親 = 根（index 0）"]:9d} '
          f'({100*c["親 = 根（index 0）"]/max(tot-orp,1):6.2f}% of 親あり)**')
    print(f'      ⚠ **`snoc_flat_root` の全前提（`srow=0` も）が成立: '
          f'{c["★★ snoc_flat_root の全前提が成立"]:9d}**')
    print(f'  **(c2) 行 0 の親 = ブロック n-1 の根: {c["(c2) 行0の親 = ブロック n-1 の根"]:9d}**')
    print('      親（行 `srow`）のブロック戻り: ', dict(sorted(
        (k[1], c[k]) for k in c if isinstance(k, tuple) and k[0] == '親のブロック戻り')))
    print('      行 0 の親のブロック戻り:      ', dict(sorted(
        ((k[1], c[k]) for k in c if isinstance(k, tuple) and k[0] == '(c2) 行0の親の戻り'),
        key=lambda x: (x[0] is None, x[0]))))
    for k in sorted(ex, key=str)[:4]:
        print(f'      例 {k}: Q={ex[k][0]} d={ex[k][1]} e={ex[k][2]} n={ex[k][3]}')


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--noblk', action='store_true')
    a = ap.parse_args()
    for cm in (1, 2, 3):
        for L in (2, 3, 4):
            run(cm, L, range(4), (1, 2, 3), not a.noblk)
