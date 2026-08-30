# -*- coding: utf-8 -*-
"""**(ORPH-SHEET) —— シート（ground truth）で、窓の孤児の親がどこにいるか。**

## ⚠ 母集団の作り方（1 行）

`tools/dbms/psiI.json` の **DBMS 列**を `core.parse` で 3 行に読み、重複を除き、
**`|M| <= 26` かつ全列 `行 2 <= 1`**（z<2 断片）に絞る。
各 `M` と各 `j`（`2 <= j < |M|`）について `B = M[:j+1]`、`s = srow(B,j)`、
`p = parent(B, s, j)`（**一意**）、`j - p >= 2` の窓 `V = B[p:j]` を取る。

## ⚠ 器具

**`trio.py` の `parent` / `is_ancestor`**（L3 の `l3_sheet_hlocq.py` は自前実装）
⟹ ★ **器具が違うので、L3 の 348 / 6792 を独立に検算できます**。
"""
import sys, os, json, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from core import parse
from r126 import srow


def hloc_col(X, t):
    """`hlocQ` の列 `t` の成分（真＝成立）。"""
    if X[t][2] > 0: return trio.parent(X[:t + 1], 2, t) is not None
    if X[t][1] == 0: return True
    return any(trio.is_ancestor(X, 0, y, t) and X[y][1] < X[t][1]
               for y in range(t))


def load():
    p = '/home/koteitan/proofs/dbms/tools/dbms/psiI.json'
    seen, mats = set(), []
    for r in json.load(open(p)):
        s = r.get('dbms')
        if not s or 'Empty' in s: continue
        try: M = parse(s)
        except Exception: continue
        if not M: continue
        cols = tuple(tuple(list(c) + [0, 0, 0])[:3] for c in M)
        if cols not in seen:
            seen.add(cols); mats.append([tuple(c) for c in cols])
    return mats


def main():
    t0 = time.time(); mats = load()
    c = Counter(); ex = []; srcs = set()
    for M in mats:
        if len(M) > 26 or any(x[2] > 1 for x in M): continue
        c['シートの行列（絞り込み後）'] += 1
        for j in range(2, len(M)):
            B = [tuple(x) for x in M[:j + 1]]
            s = srow(B, j)
            if s == 0: continue
            p = trio.parent(B, s, j)
            if p is None or j - p < 2: continue
            c['★ 分母（窓）'] += 1
            V = [tuple(x) for x in B[p:j]]
            broke = False
            for t in range(1, len(V)):
                if hloc_col(V, t): continue
                broke = True
                a = p + t                       # 絶対番地
                sa = srow(B, a)
                c['★★ (ORPH-SHEET) 分母（窓の孤児）'] += 1
                c[f'   孤児の srow={sa}'] += 1
                # ---------- 親を B の中で探す ----------
                pa = trio.parent(B[:a + 1], sa, a)
                if pa is None: loc = '⛔ どこにも無い（本当の孤児）'
                elif pa >= p:  loc = '⚠ 窓の中（矛盾）'
                else:          loc = '★★ 接頭辞の中'
                c[f'(ORPH-SHEET) 親の位置: {loc}'] += 1
                if pa is not None and pa < p:
                    c[f'   (b) 接頭辞の親の srow={srow(B, pa)}'] += 1
                    c[f'   (b) 接頭辞の親の距離 p-pa={min(p - pa, 5)}'] += 1
                # ---------- 行 1 の証人も B の中で探す ----------
                if V[t][2] == 0 and V[t][1] > 0:
                    ws = [y for y in range(a)
                          if trio.is_ancestor(B, 0, y, a) and B[y][1] < B[a][1]]
                    c['(行1) 分母'] += 1
                    if not ws: c['   ⛔ (行1) B でも証人が無い'] += 1
                    elif max(ws) >= p: c['   ⚠ (行1) 証人が窓の中（矛盾）'] += 1
                    else:
                        c['   ★★ (行1) 証人は接頭辞の中'] += 1
                        c[f'      (行1) 証人の距離 p-y={min(p - max(ws), 5)}'] += 1
                if len(ex) < 5:
                    ex.append((B, p, V, t, pa))
            if broke:
                c['⛔ 破れた窓'] += 1
                srcs.add(tuple(M))
    def pc(a, b): return f'{a} ({100*a/max(b,1):8.4f}%)'
    dn = c['★ 分母（窓）']; do = c['★★ (ORPH-SHEET) 分母（窓の孤児）']
    print(f'### シート（psiI.json の DBMS 列）  [{time.time()-t0:.1f}s]')
    print(f'  行列 {c["シートの行列（絞り込み後）"]}  ★ **分母（窓）{dn}**  '
          f'⛔ **破れた窓** {pc(c["⛔ 破れた窓"], dn)}  破れを出す行列 {len(srcs)}')
    print(f'  ★★ **(ORPH-SHEET) 分母（窓の孤児）{do}**')
    for k in sorted(c):
        if k.startswith('(ORPH-SHEET) 親の位置'):
            print(f'      {k}: {pc(c[k], do)}')
    for k in sorted(c):
        if k.startswith('   '): print(f'      {k}: {c[k]}')
    print(f'  (行1) 分母 {c["(行1) 分母"]}')
    for x in ex[:3]:
        print(f'      例 B={x[0]} p={x[1]} V={x[2]} t={x[3]} 親(絶対)={x[4]}')


if __name__ == '__main__':
    main()
