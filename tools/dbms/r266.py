# -*- coding: utf-8 -*-
"""**(CONE-T) —— 窓それ自身の根の錐。対照つき。**

## ⚠ 主語（今日いちばん大事なところ）

    ★ **`le1 V 0 t`** …… **窓 `V = B[p:j]` の中で、`V` の根から**測る（H12 の `hcone`）
    ⛔ `le1 B 0 (p+t)` … **`B` の根から**測る（§R240 で測ったのはこちら）
    ⟹ ★★ **根が違うので別の錐**。⟹ **両方を並べて出す**。

## 母集団（1 行）

`psiI.json` の DBMS 列 1,637 行列、`B = M[:j+1]`、`s = srow(B,j) >= 1`、`p = parent(B,s,j)`、
`j - p >= 2` の窓 `V = B[p:j]`。**分母（窓の全列）= 19,107**、**孤児 = 353**。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r263 import load, hloc_col


def main():
    t0 = time.time(); mats = load(); c = Counter(); ex = []
    for M in mats:
        for j in range(2, len(M)):
            B = [tuple(x) for x in M[:j + 1]]
            s = srow(B, j)
            if s == 0: continue
            p = trio.parent(B, s, j)
            if p is None or j - p < 2: continue
            V = [tuple(x) for x in B[p:j]]
            for t in range(1, len(V)):
                a = p + t
                inV = trio.is_ancestor(V, 1, 0, t)      # ★ 窓それ自身の根の錐
                inB = trio.is_ancestor(B, 1, 0, a)      # ⛔ B の根の錐
                orph = not hloc_col(V, t)
                c['(全列) 分母'] += 1
                if inV: c['(全列) ★ **V の錐の中**'] += 1
                if inB: c['(全列) ⛔ B の錐の中'] += 1
                # ---------- (A-d) の対照: B の親は le1 祖先か ----------
                pa = trio.parent(B[:a + 1], srow(B, a), a)
                if pa is not None:
                    c['(A-d対照) 親がいる列'] += 1
                    if trio.is_ancestor(B, 1, pa, a):
                        c['(A-d対照) ★ 親は le1 祖先'] += 1
                    else:
                        c['(A-d対照) ⛔ le1 では繋がらない'] += 1
                if not orph: continue
                c['★★ (孤児) 分母'] += 1
                if inV:
                    c['(孤児) ★★ **V の錐の中**'] += 1
                    if len(ex) < 3: ex.append(('中', B, p, V, t))
                else:
                    c['(孤児) ⛔ V の錐の外'] += 1
                    if len(ex) < 6: ex.append(('外', B, p, V, t))
                if inB: c['(孤児) ⛔ B の錐の中'] += 1
    def pc(a, b): return f'{a} ({100*a/max(b,1):8.4f}%)'
    d1 = c['(全列) 分母']; d2 = c['★★ (孤児) 分母']; d3 = c['(A-d対照) 親がいる列']
    print(f'### シート 1,637 行列  [{time.time()-t0:.1f}s]')
    print(f'  ★★★ (CONE-T) **対照＝窓の全列 {d1}**')
    print(f'      ★ **`le1 V 0 t`（窓の根の錐）の中**: {pc(c["(全列) ★ **V の錐の中**"], d1)}')
    print(f'      ⛔ `le1 B 0 (p+t)`（B の根の錐）の中: {pc(c["(全列) ⛔ B の錐の中"], d1)}')
    print(f'  ★★★ (CONE-T) **孤児 {d2}**')
    print(f'      ★★ **`le1 V 0 t` の中**: {pc(c["(孤児) ★★ **V の錐の中**"], d2)}   '
          f'⛔ 外: {pc(c["(孤児) ⛔ V の錐の外"], d2)}')
    print(f'      ⛔ `le1 B 0 (p+t)` の中: {pc(c["(孤児) ⛔ B の錐の中"], d2)}')
    print(f'  ⚠ (A-d) の対照: 親がいる列 {d3}  '
          f'★ 親は `le1` 祖先 {pc(c["(A-d対照) ★ 親は le1 祖先"], d3)}  '
          f'⛔ 繋がらない {c["(A-d対照) ⛔ le1 では繋がらない"]}')
    for x in ex:
        print(f'      ({x[0]}) B={x[1]} p={x[2]} V={x[3]} t={x[4]}')


if __name__ == '__main__':
    main()
