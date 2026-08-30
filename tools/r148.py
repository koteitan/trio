# -*- coding: utf-8 -*-
"""**課題 (p1)-(p3)（L3 の直接依頼）—— F2b の再帰の各段で、残る前提 2 つ（＋1）の成立率。**

**測る前提（L3 の指定を逐語で）:**

    **(p1) `hj0c : le1 M 0 j0`** … 悪根が全体の根の行 1 錐に入る
    **(p2) `hd0pos : 0 < d0`**   … ブロック間の行 0 の差が正
    **(p3) `hup : ∀ l, j0 < l <= j0+Lb → entry M 0 j0 < entry M 0 l`** … 悪根が写し窓の中で最浅

**単位**: **F2b の再帰の各段**（`M` は各段の列、`j0 = parent M (srow M last) last`）。

## ★ 反例の形を先に書く（教訓 45）＋ 充足率の見積もり（L3 の §105.2）

**先に導出できてしまう部分:**

    **(p3)** `nextrel0` の「途中に窪みなし」より `∀ j, j0<j<last → entry 0 last <= entry 0 j`、
             かつ `entry 0 j0 < entry 0 last` ⟹ **`entry 0 j0 < entry 0 l` が `j0<l<=last` で自動**
             ⟹ **(p3) は 100% のはず。**
    **(p2)** `d0 = if 0 < srow then entry 0 last − entry 0 j0 else 0`。
             `srow >= 1` なら `nextrel0` より正。⟹ **破れるのは `srow = 0` の段だけ。**
    **(p1)** `le1` の親鎖は一意（各点の `nextrel1` の前者は一意）。
             `le1 M 0 last`（F2b）と `le1 M j0 last`（`nextrel2` が要求）から
             **`0` も `j0` も同じ鎖の上** ⟹ `0 <= j0` なので **`le1 M 0 j0`** ⟹ **100% のはず。**

> **⚠ 反例の形: 「その段の `srow` が 0 になる」（(p2) が破れる唯一の形）。**
> **⚠ 充足率の見積もり: §R143 (k3) で展開の `srow=0` は 3.3% だった ⟹ **(p2) の破れは 2 〜 6%**。**
> **(p1)(p3) の破れは 0% と見積もる。**

**箱と単位**: 単位 = 再帰の各段。母集団 = F2b かつ塔で復活した `(Q,d,e,n)` から出発。
箱 = 行0<4, 行1<3, 行2<=cm（**3 段**）、`|Q| = 3..5`、`d,e ∈ 0..3`、`n ∈ {2,3}`、`m ∈ 1..3`。
**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow, hasP, le1_root, classify
from r113 import mTower
from r98 import oper_lean


def le1g(M, a, b):
    if a >= len(M) or b >= len(M):
        return False
    return trio.is_ancestor(M, 1, a, b)


def isF2b(S):
    j = len(S) - 1
    return len(S) >= 2 and srow(S, j) == 2 and le1_root(S, j) and S[j][2] <= S[0][2]


def probe(M, c, ex):
    """1 段ぶんの (p1)(p2)(p3) を測る。親が無ければ None を返す。"""
    last = len(M) - 1
    sr = srow(M, last)
    j0 = trio.parent(M, sr, last)
    if j0 is None:
        c['親なし（その段で孤児）'] += 1
        return None
    Lb = last - j0
    d0 = (M[last][0] - M[j0][0]) if sr > 0 else 0
    p1 = le1g(M, 0, j0)
    p2 = d0 > 0
    p3 = all(M[j0][0] < M[l][0] for l in range(j0 + 1, last + 1))
    c['段の分母'] += 1
    c[('srow', sr)] += 1
    c[('(p1) le1 M 0 j0', p1)] += 1
    c[('(p2) 0 < d0', p2)] += 1
    c[('(p3) 窓の中で最浅', p3)] += 1
    c[('(p2) を srow 別', sr, p2)] += 1
    c[('(p1) を srow 別', sr, p1)] += 1
    c[('(p3) を srow 別', sr, p3)] += 1
    if not p1:
        ex.setdefault('p1 破れ', (M[:6], j0, sr))
    if not p2:
        ex.setdefault('p2 破れ', (M[:6], j0, sr, d0))
    if not p3:
        ex.setdefault('p3 破れ', (M[:6], j0, sr))
    return j0


def run(cm, L, DE, NS, MS, cap=12):
    COL = [(a, b, c_) for a in range(4) for b in range(3) for c_ in range(cm + 1)]
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
                        if trio.parent(T, srow(T, len(T) - 1), len(T) - 1) is None:
                            continue                       # 復活したものだけ
                        # 再帰の鎖をたどり、各段で測る
                        S = T; depth = 0
                        while depth < cap and len(S) >= 2:
                            if probe(S, c, ex) is None:
                                break
                            nxt = None
                            for m in MS:
                                R = oper_lean(S, m)
                                if len(R) < 2:
                                    continue
                                if isF2b(R):
                                    nxt = R; break
                                if nxt is None:
                                    nxt = R
                            if nxt is None:
                                break
                            S = nxt; depth += 1
                            if not isF2b(S):
                                probe(S, c, ex)            # 最後の段も測る
                                break
    tot = c['段の分母']
    print(f'### 行2<={cm} |Q|={L}  測った段 {tot:9d}  [{time.time()-t0:.1f}s]')
    if not tot:
        print('  （0 件）\n'); return
    for k, lab in (('(p1) le1 M 0 j0', '(p1) `le1 M 0 j0`'),
                   ('(p2) 0 < d0', '(p2) `0 < d0`'),
                   ('(p3) 窓の中で最浅', '(p3) 窓の中で最浅')):
        y = c[(k, True)]; nn = c[(k, False)]
        print(f'  **{lab:24s}: {y:9d} / {y+nn} ({100*y/max(y+nn,1):6.2f}%)**  破れ {nn}')
    print('  段の `srow`: ', dict(sorted((k[1], c[k]) for k in c
                                    if isinstance(k, tuple) and len(k) == 2 and k[0] == 'srow')))
    for lab in ('(p1)', '(p2)', '(p3)'):
        print(f'  {lab} を `srow` 別: ', dict(sorted(((k[1], k[2]), c[k]) for k in c
                                         if isinstance(k, tuple) and len(k) == 3 and k[0] == f'{lab} を srow 別')))
    print(f'  親なし（その段で孤児）: {c["親なし（その段で孤児）"]}')
    for k in sorted(ex):
        print(f'      {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=5)
    a = ap.parse_args()
    for cm in (1, 2):
        for L in range(3, a.L + 1):
            run(cm, L, range(4), (2, 3), (1, 2, 3))
