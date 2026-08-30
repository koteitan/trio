# -*- coding: utf-8 -*-
"""**(ORPH-A)(ORPH-B)(ORPH-C) —— シート（ground truth）で `OrphOK0` の枝を測る。**

## ⚠ 母集団の作り方（1 行）

`psiI.json` の DBMS 列を `core.parse` で 3 行に読み重複を除いた **1,637 行列**。
各 `M`・各 `j`（`2 <= j < |M|`）で `B = M[:j+1]`、`s = srow(B,j) >= 1`、
`p = parent(B,s,j)`、`j - p >= 2` の窓 `V = B[p:j]`（**分母（窓）= 6,792**）。

## 器具

`trio.py` の `parent` / `is_ancestor`（L3 の `l3_sheet_hlocq.py` とは別実装）。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r263 import load, hloc_col


def main():
    t0 = time.time(); mats = load()
    c = Counter(); dist = Counter(); ex = []
    for M in mats:
        for j in range(2, len(M)):
            B = [tuple(x) for x in M[:j + 1]]
            s = srow(B, j)
            if s == 0: continue
            p = trio.parent(B, s, j)
            if p is None or j - p < 2: continue
            V = [tuple(x) for x in B[p:j]]
            coneP = trio.is_ancestor(B, 1, 0, p)     # 窓の根が B の錐の中か
            for t in range(1, len(V)):
                c['(ORPH-C) 分母（窓の全列）'] += 1
                ok = hloc_col(V, t)
                if ok: continue
                a = p + t
                sa = srow(B, a)
                pa = trio.parent(B[:a + 1], sa, a)
                c['★ (ORPH-C) 窓で孤児'] += 1
                if pa is None:
                    c['⛔ (ORPH-C) B でも孤児（本当の孤児）'] += 1; continue
                if pa >= p:
                    c['⚠ (ORPH-C) 親が窓の中'] += 1; continue
                c['★★ (ORPH-C) **窓で孤児かつ接頭辞に親**（＝ OrphOK0 の枝）'] += 1
                # ================= (ORPH-A) =================
                d = p - pa
                dist[d] += 1
                c[f'   (A-b) 親の srow={srow(B, pa)}'] += 1
                c[f'   (A-b) 孤児の srow={sa}'] += 1
                if pa == 0: c['   ★ (A-c) 親は接頭辞の根（番地 0）'] += 1
                else:       c['   ⛔ (A-c) 親は根でない'] += 1
                if d == p:  c['   （A-c) 距離が最大（＝ 根）'] += 1
                if trio.is_ancestor(B, 1, pa, a):
                    c['   ★★ (A-d) 親は `le1` の意味でも祖先'] += 1
                else:
                    c['   ⛔ (A-d) `le1` では繋がらない'] += 1
                    if len(ex) < 4: ex.append(('A-d', B, p, V, t, pa))
                # ================= (ORPH-B) =================
                if coneP: c['   ⛔ (B) **窓の根が錐の中**'] += 1
                else:     c['   ★ (B) 窓の根が錐の外'] += 1
                if trio.is_ancestor(B, 1, 0, a): c['   (B) 孤児自身が錐の中'] += 1
                else:                            c['   (B) 孤児自身が錐の外'] += 1
    def pc(a, b): return f'{a} ({100*a/max(b,1):8.4f}%)'
    dc = c['(ORPH-C) 分母（窓の全列）']
    do = c['★★ (ORPH-C) **窓で孤児かつ接頭辞に親**（＝ OrphOK0 の枝）']
    print(f'### シート 1,637 行列  [{time.time()-t0:.1f}s]')
    print(f'  ★★★ (ORPH-C) **分母（窓の全列）{dc}**')
    print(f'      ★ 窓で孤児 {pc(c["★ (ORPH-C) 窓で孤児"], dc)}   '
          f'⛔ B でも孤児 {c["⛔ (ORPH-C) B でも孤児（本当の孤児）"]}   '
          f'⚠ 親が窓の中 {c["⚠ (ORPH-C) 親が窓の中"]}')
    print(f'      ★★ **`OrphOK0` の枝 {pc(do, dc)}**')
    print(f'  ★★ (ORPH-A) 分母 {do}')
    print(f'      (a) 距離 p-parent: {dict(sorted(dist.items()))}')
    for k in sorted(c):
        if k.startswith('   '): print(f'      {k}: {pc(c[k], do)}')
    for x in ex:
        print(f'      ⛔ {x[0]} 例 B={x[1]} p={x[2]} V={x[3]} t={x[4]} 親={x[5]}')


if __name__ == '__main__':
    main()
