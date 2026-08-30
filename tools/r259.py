# -*- coding: utf-8 -*-
"""**(BLK) ＋ (WIN-W-b)(WIN-W)。**

## ⚠ `W` 所属は有限判定できません

`W u = Wf (u+1) u`、`Wf` は `lfpS (Aset ...)`（`Wset.lean:217`）で、`Aop` の第 2 節は
**`∀ n, 1 ≤ n → M⟦n⟧ ∈ X`**（無限分岐）、第 3 節は **`∀ z ∈ Wfam m`**（無限量化）。
⟹ ⛔ **有限計算で `∈ W` は決められません**（既報の決定率 0%）。

## ★ 代わりに計算できる代替: **到達可能集合 `Reach`**

    `Reach` ＝ 中核 `D_v`（`diag(3,v,1)`）から `expand(·, n)` を `depth` 段まで辿った集合
              ＋ その **すべての接頭辞**（`W_dropLast : M ∈ W u → M.dropLast ∈ W u` に対応）
    ⟹ ★ `Reach ⊆ W`（健全）。⟹ ⛔ 逆は言えない（**非所属の証明にはならない**）
    ⟹ ⟹ ★ ですから「`Reach` に**入る**」は肯定的な証拠、「入らない」は**未確定**と書きます。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from trio import expand, diag
from collections import Counter
from r126 import srow
from r248 import hlocQ
from r254 import hloc_col


def reach(vs, ns, depth):
    seen = set(); frontier = [tuple(map(tuple, diag(3, v, 1))) for v in vs]
    for _ in range(depth):
        nxt = []
        for S in frontier:
            if S in seen: continue
            seen.add(S)
            for n in ns:
                T = tuple(map(tuple, expand([list(x) for x in S], n)))
                if T not in seen: nxt.append(T)
        frontier = nxt
    seen.update(frontier)
    out = set()
    for S in seen:                      # 接頭辞で閉じる
        for k in range(1, len(S) + 1): out.add(S[:k])
    return out


def shift0(S, k):
    return tuple((x - k, y, z) for x, y, z in S)


def main():
    B = ((0, 0, 0), (1, 2, 0), (2, 1, 0), (3, 9, 0))
    t0 = time.time()
    for depth, ns in ((4, (1, 2, 3)), (5, (1, 2, 3)), (4, (1, 2, 3, 4))):
        R = reach((1, 2, 3, 4), ns, depth)
        c = Counter(); ex = []
        # ---------- (WIN-W-b) ----------
        inR = B in R
        inRs = any(shift0(B, k) in R for k in range(0, 4))
        # ---------- (WIN-W) ＋ (BLK) ----------
        for S in R:
            if len(S) < 3: continue
            Sj = [tuple(x) for x in S]
            lastx = len(Sj) - 1
            p = trio.parent(Sj, srow(Sj, lastx), lastx)
            if p is None or lastx - p < 2: continue
            V = [tuple(x) for x in Sj[p:lastx]]
            c['窓'] += 1
            # 窓を entry B 0 p だけ下げて Reach に入るか
            Vs = shift0(tuple(V), V[0][0])
            if Vs in R: c['★ (WIN-W) 窓（行0を下げて）が Reach に入る'] += 1
            else:
                c['⛔ (WIN-W) Reach に見つからない'] += 1
                if len(ex) < 4: ex.append(('WIN-W', Sj, p, V))
            # hlocQ
            if hlocQ(V): c['★ hlocQ(V) が真'] += 1
            else:
                c['⛔ **hlocQ(V) が偽**'] += 1
                for tt in range(1, len(V)):
                    if hloc_col(V, tt): continue
                    if V[tt][2] > 0: c['   破れの行 2'] += 1; continue
                    c['(BLK) 行 1 の破れ'] += 1
                    if V[tt][1] <= V[0][1]: c['★ (BLK) 的はブロッカー'] += 1
                    else:
                        c['⛔ **(BLK) 的がブロッカーでない**'] += 1
                        ex.append(('BLK', Sj, p, V, tt))
        def pc(a, b): return f'{a} ({100*a/max(b,1):8.4f}%)'
        dn = c['窓']
        print(f'### Reach(D_1..D_4, n∈{ns}, depth={depth})  |Reach| = {len(R)}  '
              f'[{time.time()-t0:.1f}s]')
        print(f'  (WIN-W-b) **L3 の反例 B = {list(B)}**: Reach に入る? **{inR}**'
              f'（行 0 を 0..3 下げても: **{inRs}**）')
        print(f'  (WIN-W) 窓 {dn}  ★ **Reach に入る** '
              f'{pc(c["★ (WIN-W) 窓（行0を下げて）が Reach に入る"], dn)}  '
              f'⛔ 見つからない {c["⛔ (WIN-W) Reach に見つからない"]}')
        print(f'  ★★ **hlocQ(V) が真** {pc(c["★ hlocQ(V) が真"], dn)}  '
              f'⛔ **偽** {c["⛔ **hlocQ(V) が偽**"]}')
        db = c['(BLK) 行 1 の破れ']
        print(f'  ★★ (BLK) 行 1 の破れ {db}  ★ **的はブロッカー** '
              f'{pc(c["★ (BLK) 的はブロッカー"], db)}  '
              f'⛔ **ブロッカーでない** {c["⛔ **(BLK) 的がブロッカーでない**"]}'
              f'   （破れの行 2: {c["   破れの行 2"]}）')
        for x in ex[:4]:
            print(f'      ⛔ {x[0]} 例 S={x[1]} p={x[2]} V={x[3]}'
                  + (f' t={x[4]}' if len(x) > 4 else ''))
        print()


if __name__ == '__main__':
    main()
