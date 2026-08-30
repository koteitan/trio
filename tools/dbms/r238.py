# -*- coding: utf-8 -*-
"""**課題 (BREAK) ＋ (SHAPE-b)。**

⚠ **(BREAK-b)「塔そのものが `W u` に入るか」は規則（`W` 所属の判定はしない）により行いません。**

⚠ **「268 件」は `|R|=3` の箱限定**です。`|R|=4` では深さ 3 以上も破れます（§R221）。
⟹ **両方の箱で、破れた全件**を分母にします。

## 測るもの

    (BREAK-a) 破れる列は **孤児**か（`V.take (j+1)` の中で）。孤児なら `snoc_orphan_W` で無料
    (BREAK-c) `Q` と `V` をそのまま貼る
    (BREAK-d) `|V| = 2` と `|V| = 3` を分ける ＋ **深さ**でも分ける
    (SHAPE-b) 破れなかった窓で「前件が空虚」な理由（`j=1` が錐の中 / 行1=0 / 行2>0）
"""
import sys, itertools, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import Lift1
from r169 import domT
from r171 import step_det
from r201 import dOf, eOf
from r206 import hr0
from r234 import h1out_bad


def run(L, R1, VS, ZS, TS, NS, depth, beam, seed, tag):
    COL = [(a, b, cc) for a in range(1, 4) for b in range(R1) for cc in (0, 1)]
    rnd = random.Random(seed); c = Counter(); ex = []; t0 = time.time()
    for Rt in itertools.product(COL, repeat=L):
        R = list(Rt)
        if srow(R, len(R) - 1) != 2: continue
        if not any(domT(R, m) for m in range(4)): continue
        for v in VS:
            for z in ZS:
                if trio.parent([(0, v, z)] + R, 2, len(R)) is None: continue
                for t in TS:
                    M = [tuple(x) for x in Lift1([(0, v, z)] + R, t)]
                    Q0 = M[:-1]
                    if len(Q0) < 2: continue
                    d, e = dOf(M), eOf(M)
                    if not (d > 0 and hr0(Q0) and Q0[0][2] == 0): continue
                    if h1out_bad(Q0): continue
                    front = [(tuple(Q0), d, e)]
                    for dep in range(1, depth + 1):
                        nxt = []
                        for (X, dd, ee) in front:
                            for n in NS:
                                for j in range(len(X)):
                                    r = step_det(list(X), dd, ee, n, j)
                                    if r is None or len(r[0]) < 2: continue
                                    V = [tuple(y) for y in r[0]]
                                    bad = h1out_bad(V)
                                    if bad:
                                        for jb in bad:
                                            c['★ 分母: 破れた列'] += 1
                                            c[('(BREAK-d) 深さ', dep)] += 1
                                            c[('(BREAK-d) |V|', min(len(V), 5))] += 1
                                            orph = trio.parent(V[:jb + 1],
                                                               srow(V, jb), jb) is None
                                            if orph:
                                                c['★ (BREAK-a) 破れる列は孤児'] += 1
                                            else:
                                                c['⛔ (BREAK-a) 親がいる'] += 1
                                                pp = trio.parent(V[:jb+1], srow(V, jb), jb)
                                                c[('  親の位置', 'V の中')] += 1
                                            c[('(BREAK) 破れる列の j', min(jb, 4))] += 1
                                            if len(ex) < 6:
                                                ex.append((dep, X, dd, ee, n, j, V, jb,
                                                           '孤児' if orph else '親あり'))
                                    else:
                                        nxt.append((tuple(V), r[1], r[2]))
                                        # (SHAPE-b) 前件が空虚な理由
                                        outs = [k for k in range(1, len(V))
                                                if not trio.is_ancestor(V, 1, 0, k)
                                                and V[k][2] == 0 and V[k][1] > 0]
                                        if not outs and len(V) >= 2:
                                            c['(SHAPE-b) 前件が空虚な窓'] += 1
                                            r1 = [k for k in range(1, len(V))
                                                  if trio.is_ancestor(V, 1, 0, k)]
                                            r2 = [k for k in range(1, len(V)) if V[k][2] > 0]
                                            r3 = [k for k in range(1, len(V)) if V[k][1] == 0]
                                            c[('(SHAPE-b) 理由',
                                               '全部錐の中' if len(r1) == len(V)-1 else
                                               ('行2>0 を含む' if r2 else
                                                ('行1=0 を含む' if r3 else 'その他')))] += 1
                        if not nxt: break
                        rnd.shuffle(nxt); front = nxt[:beam]
    D = c['★ 分母: 破れた列']
    print(f'### {tag} 深さ<={depth} ビーム{beam}  ★ 分母（破れた列）{D}  [{time.time()-t0:.1f}s]')
    for k in ['★ (BREAK-a) 破れる列は孤児', '⛔ (BREAK-a) 親がいる']:
        print(f'    {k:30s} {c[k]:9d} ({100*c[k]/max(D,1):8.4f}%)')
    for nm in ['(BREAK-d) 深さ', '(BREAK-d) |V|', '(BREAK) 破れる列の j']:
        print(f'    {nm}: ', dict(sorted((k[1], c[k]) for k in c
                                   if isinstance(k, tuple) and k[0] == nm)))
    print(f'    (SHAPE-b) 前件が空虚な窓 {c["(SHAPE-b) 前件が空虚な窓"]}: ',
          dict((k[1], c[k]) for k in c if isinstance(k, tuple) and k[0] == '(SHAPE-b) 理由'))
    for x in ex:
        print(f'      ⛔ 破れ例 深さ{x[0]} Q={x[1]} (d,e)=({x[2]},{x[3]}) n={x[4]} j={x[5]} '
              f'⟹ V={x[6]} 破れる列={x[7]}（{x[8]}）')
    print()


if __name__ == '__main__':
    run(3, 3, (0,1,2), (0,1), (0,1,2), (1,2,3), 5, 200, 981, '消費側 |R|=3 行1<3')
    run(3, 5, (0,1,2,3), (0,1), (0,1,2,3), (1,2), 4, 100, 983, '★ 消費側 |R|=3 行1<5')
