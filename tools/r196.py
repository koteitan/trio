# -*- coding: utf-8 -*-
"""**課題 (y2) —— 真の核（`¬h2cone(V)`）の構造。**

## 前提の逐語（教訓 2）

`Trio.lean:60`  `nextrel2 M j0 j1 = j0<|M| ∧ j1<|M| ∧ j0<j1 ∧
                   entry M 2 j0 < entry M 2 j1 ∧ le1 M j0 j1 ∧
                   (∀ j, j0 < j ∧ le1 M j j1 → entry M 2 j1 ≤ entry M 2 j)`
`Trio.lean:49`  `nextrel1 M j0 j1 = … ∧ **entry M 1 j0 < entry M 1 j1**（狭義）∧ le0 M j0 j1 ∧ …`

⟹ **主語の決着**: 「隣り合う」は**添字**ではなく **`le0` の祖先鎖**。
`nextrel1` が `le0 M j0 j1` を要求するので、行 1 の比較は**行 0 の祖先の間**でしか起きない。

## ★ 予想（教訓 45）＋ 見積もり

team-lead の見立て:「機構は**行 1 の等号**。100% では」

> **⚠ 私は **100% にならない**と予想する。別の機構が既に見えている:**
> **`r195.py` の例 `V = [(4,0,1), (8,8,1)]` は、孤児 `j=1` に対して
>   **行 2 = 0 の列がそもそも 1 本も無い**（`V[0]` の行 2 も 1）。**
> **⟹ 「行 1 の等号」ではなく「候補ゼロ」。**
> **⚠ 見積もり: 行 1 の等号 20〜50%、候補ゼロ 40〜70%。**
> **⚠ もし 100% が出たら箱を伸ばして壊しにいく。**
"""
import sys, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r183 import hr0
from r195 import h2cone


def why(V, j):
    """孤児 `j`（行 2 正・錐の中・親なし）について、**なぜ親が無いか**を分類。"""
    cand = [p for p in range(j) if V[p][2] < V[j][2]]        # 行 2 の値で候補
    if not cand:
        return '(A) 行 2 が小さい列がそもそも無い'
    c0 = [p for p in cand if trio.is_ancestor(V, 0, p, j)]   # le0 祖先でもある
    if not c0:
        return '(B) 候補はあるが `le0` 祖先が 1 つも無い'
    eq  = [p for p in c0 if V[p][1] == V[j][1]]
    gt  = [p for p in c0 if V[p][1] >  V[j][1]]
    lt  = [p for p in c0 if V[p][1] <  V[j][1]]
    if not lt:
        if eq and not gt: return '(C) ★ 候補は全部**行 1 が等しい**'
        if gt and not eq: return '(D) 候補は全部行 1 が大きい'
        return '(E) 行 1 が等しい／大きい の混在'
    return '(F) 行 1 は小さいが `le1` が繋がらない（最小性など）'


def run(E, LS, NS, DE, nsamp, seed, tag):
    rnd = random.Random(seed); c = Counter(); ex = []; t0 = time.time(); tries = 0
    while c['Q の本数'] < nsamp and tries < nsamp * 300:
        tries += 1
        L = rnd.choice(LS)
        a = rnd.randrange(E - 1)
        Q = [(a, rnd.randrange(E), rnd.randrange(2))] + \
            [(rnd.randrange(a + 1, E), rnd.randrange(E), rnd.randrange(2))
             for _ in range(L - 1)]
        if h2cone(Q): continue                     # 母集団 = `hr0 ∧ h2cone(Q)`
        c['Q の本数'] += 1
        d, e = rnd.choice(DE), rnd.choice(DE)
        for n in NS:
            for j0 in range(L):
                T = [tuple(x) for x in mTower(Q, d, e, n)]
                S = T + block(Q, d, e, n)[:j0 + 1]
                last = len(S) - 1
                par = trio.parent(S, srow(S, last), last)
                if par is None: continue
                V = [tuple(x) for x in S[par:last]]
                if len(V) < 2: continue
                c['全段'] += 1
                nd = len(V) >= L
                if nd: c['非減少の段'] += 1
                else:  c['減る段'] += 1
                bad = h2cone(V)
                if not bad: continue
                c['★ 核（`¬h2cone(V)`）'] += 1
                c[('減る' if not nd else '非減少')] += 1
                p_rel = par % L if par < n * L else None
                c[('(y2c) p_rel', p_rel if p_rel is not None else -1)] += 1
                c[('(y2c) srow', srow(S, last))] += 1
                for j in bad:
                    c['孤児の列の総数'] += 1
                    c[('(y2b) 理由', why(V, j))] += 1
                # (y2a) `le0` 祖先鎖の上に「行 1 が等しい」対があるか
                pair = any(V[p][1] == V[q][1]
                           for q in range(len(V)) for p in range(q)
                           if trio.is_ancestor(V, 0, p, q))
                if pair: c['(y2a) `le0` 鎖上に行 1 の等号がある'] += 1
                if len(ex) < 3: ex.append((V, bad))
    t = c['全段']; k = c['★ 核（`¬h2cone(V)`）']
    print(f'### {tag} 値域<{E} |Q|∈{LS}  全段 {t}  核 {k} ({100*k/max(t,1):6.3f}%)  '
          f'[{time.time()-t0:.1f}s]')
    print(f'    減る段 {c["減る段"]} / 非減少 {c["非減少の段"]}   '
          f'核のうち 減る {c["減る"]} / 非減少 {c["非減少"]}   '
          f'**減る段での核の率 {100*c["減る"]/max(c["減る段"],1):7.4f}%**')
    print(f'    **(y2a) `le0` 鎖上に行 1 の等号 … {c["(y2a) `le0` 鎖上に行 1 の等号がある"]} / {k} '
          f'({100*c["(y2a) `le0` 鎖上に行 1 の等号がある"]/max(k,1):7.3f}%)**')
    print(f'    (y2b) 孤児の列 {c["孤児の列の総数"]} 本の理由:')
    for kk in sorted(x for x in c if isinstance(x, tuple) and x[0] == '(y2b) 理由'):
        print(f'        {kk[1]:44s} {c[kk]:7d} '
              f'({100*c[kk]/max(c["孤児の列の総数"],1):6.2f}%)')
    print('    (y2c) p_rel（-1 = 親が最終ブロック内）: ',
          dict(sorted((x[1], c[x]) for x in c if isinstance(x, tuple) and x[0] == '(y2c) p_rel')))
    print('    (y2c) 足す列の srow: ',
          dict(sorted((x[1], c[x]) for x in c if isinstance(x, tuple) and x[0] == '(y2c) srow')))
    for V, b in ex: print(f'      ⚠ 核の例 V={V} 孤児={b}')
    print()


if __name__ == '__main__':
    run(6,  (3,4,5,6,8),  (1,2,3,4,5), range(6),  5000, 261, '(y2)')
    print('#### (y2d) 教訓 21: 箱を伸ばして頭打ちを見る')
    run(9,  (4,6,8,10),   (1,2,3,4,6), range(9),  3500, 263, '(y2d)')
    run(12, (5,8,12),     (1,2,3,5,8), range(12), 2500, 265, '(y2d)')
    run(15, (6,10,16),    (1,2,3,5,8), range(15), 1800, 267, '(y2d)')
    run(20, (8,14,20),    (1,2,3,5,8), range(20), 1200, 269, '(y2d)')
