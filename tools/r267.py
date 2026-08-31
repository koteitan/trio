# -*- coding: utf-8 -*-
"""**(ROW1-ORPH-T) / (ORPH-AB) / (GAP-1) —— 母集団は「塔」で統一。**

## ⚠ 母集団（1 行）

    ★ **シート側**: `psiI.json` の DBMS 列の全接頭辞 `Q`（重複除去、`entry Q 2 0 = 0`）
    ⛔ **一様な箱側（対照）**: `Lift1 ((0,v,z) :: R) t` の `dropLast`（`R` 一様、`d>0`, `hr0`, `hz0`）
    どちらも `S = mTower Q d e n ++ block(Q,d,e,n).take (j+1)`。

## 測るもの

    **(ROW1-ORPH-T)** 分母 ＝ `entry S 1 c > 0` かつ `entry S 2 c = 0` の列
                      分子 ＝ **行 1 の孤児**（`parent (S.take (c+1)) 1 c` が無い）
    **(ORPH-AB)** 錐の外の孤児が **(a) 的自身がブロッカー** か **(b) 手前にブロッカー** か
    **(GAP-1)** 39 ポイントの差を **C4（`le0` で隣り合って行 1 が等しい列が無い）**で切る
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1, mTower
from r141 import block
from r169 import domT
from r201 import dOf, eOf
from r206 import hr0
from r257 import C4
from r265 import qs


def sheetQ(LQ):
    return qs(LQ)


def boxQ(L, R1, VS, ZS, TS):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    out = []
    for Rt in itertools.product(COL, repeat=L):
        R = list(Rt)
        if srow(R, len(R) - 1) != 2: continue
        if not any(domT(R, m) for m in range(4)): continue
        for v in VS:
            for z in ZS:
                if trio.parent([(0, v, z)] + R, 2, len(R)) is None: continue
                for t in TS:
                    M = [tuple(x) for x in Lift1([(0, v, z)] + R, t)]
                    Q = M[:-1]
                    if len(Q) < 2: continue
                    d, e = dOf(M), eOf(M)
                    if not (d > 0 and hr0(Q) and Q[0][2] == 0): continue
                    out.append((Q, d, e))
    return out


def scan(items, NS, tag, byC4=False):
    c = Counter(); ex = []; t0 = time.time()
    for Q, DS, ES in items:
        g = '★C4真' if C4([tuple(x) for x in Q]) else '⛔C4偽'
        for d in DS:
            for e in ES:
                for n in NS:
                    T = [tuple(x) for x in mTower(Q, d, e, n)]
                    B = [tuple(x) for x in block(Q, d, e, n)]
                    br = len(T)
                    for j in range(1, len(Q)):
                        S = T + B[:j + 1]
                        isb = lambda y: y != br and S[y][1] <= S[br][1]
                        for cc in range(1, len(S)):
                            # ---------- (ROW2-ORPH) 再掲 ----------
                            if S[cc][2] > 0:
                                c[f'[{g}] 行2 分母'] += 1
                                if trio.parent(S[:cc + 1], 2, cc) is None:
                                    c[f'[{g}] ⛔ 行2 の孤児'] += 1
                                continue
                            # ---------- (ROW1-ORPH-T) ----------
                            if S[cc][1] == 0: continue
                            c['★ (ROW1) 分母'] += 1
                            c[f'[{g}] 行1 分母'] += 1
                            if trio.parent(S[:cc + 1], 1, cc) is not None: continue
                            c['⛔ **(ROW1) 行 1 の孤児**'] += 1
                            c[f'[{g}] ⛔ 行1 の孤児'] += 1
                            # ---------- (ORPH-AB) ----------
                            if trio.is_ancestor(S, 1, 0, cc):
                                c['   (AB) 錐の中'] += 1; continue
                            c['★★ (AB) 分母（錐の外の孤児）'] += 1
                            if isb(cc): c['   ★ (AB-a) **的自身がブロッカー**'] += 1
                            elif any(isb(y) for y in range(br, cc)):
                                c['   ★ (AB-b) 手前にブロッカー（的は非ブロッカー）'] += 1
                            else:
                                c['   ⛔ (AB) どちらでもない'] += 1
                                if len(ex) < 4: ex.append((Q, d, e, n, j, cc, br, S))
    def pc(a, b): return f'{a} ({100*a/max(b,1):8.4f}%)'
    d1 = c['★ (ROW1) 分母']; d2 = c['★★ (AB) 分母（錐の外の孤児）']
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    print(f'  ★★ (ROW1-ORPH-T) 分母 {d1}  ⛔ **行 1 の孤児** '
          f'{pc(c["⛔ **(ROW1) 行 1 の孤児**"], d1)}   （錐の中 {c["   (AB) 錐の中"]}）')
    print(f'  ★★ (ORPH-AB) 分母（錐の外の孤児）{d2}')
    for k in sorted(c):
        if k.startswith('   ★ (AB') or k.startswith('   ⛔ (AB'):
            print(f'      {k}: {pc(c[k], d2)}')
    if byC4:
        print('  ★★★ (GAP-1) C4 で切る:')
        for g in ('★C4真', '⛔C4偽'):
            for r in ('行2', '行1'):
                dd = c[f'[{g}] {r} 分母']
                print(f'      [{g}] {r}: 分母 {dd}  ⛔ 孤児 '
                      f'{pc(c[f"[{g}] ⛔ {r} の孤児"], dd)}')
    for x in ex:
        print(f'      ⛔ (AB) どちらでもない例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} '
              f'j={x[4]} 列={x[5]} 塔長={x[6]}')
    print()


if __name__ == '__main__':
    scan([(Q, (1, 2), (0, 1)) for Q in sheetQ(6)], (1, 2, 3),
         '★ シート由来 Q（|Q|<=6, d∈{1,2}, e∈{0,1}, n∈{1,2,3}）', True)
    scan([(Q, (d,), (e,)) for Q, d, e in boxQ(4, 3, (0, 1, 2), (0, 1), (0, 1, 2))],
         (1, 2), '⛔ 一様な箱（対照）|R|=4 行1<3, n∈{1,2}', True)
