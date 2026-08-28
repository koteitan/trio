# -*- coding: utf-8 -*-
"""課題 R13 (3) の本体: **柱単調性 (CM) を「接頭辞 x 次の柱」で直接測る。**

述語（`copy_head` など）が上に閉じている必要は無い。要るのは
**出る柱が `collt` について単調非減少**であること。

    接頭辞 P を固定 -> 状態は決まる
    合法な次の柱 c を `collt` 昇順に並べる
    その列が出す**最初の柱** h(c) が非減少か

母数 = 接頭辞の数（行列の対をなめるより桁違いに小さく、しかも
**どの長さの母集団にも現れない破れまで拾える**）。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, provc, r7
from core import isstd
from collections import Counter


def legal_next(P, zcap=1):
    amax = P[-1][0] + 1
    out = []
    for a in range(amax + 1):
        for b in range(a + 1):
            for cz in range(min(b, zcap) + 1):
                if isstd(P + ((a, b, cz),), 'BMS'):
                    out.append((a, b, cz))
    return sorted(out)


def first_pillar(P, c):
    """`P ++ (c,)` の像で、第 |P| 列が出す**最初の**柱。"""
    j = len(P)
    C, PR = provc.b2d3p(list(P + (c,)))
    for i, e in enumerate(PR):
        if e[1] == j:
            return tuple(C[i]), e[0], e[2]
    return None, None, None


def run(pop, name, verbose=4):
    c = Counter(); ex = []
    seen = set(); t0 = time.time()
    for i, M in enumerate(pop):
        if i % 5000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        for j in range(1, len(M) + 1):
            P = tuple(M[:j])
            if P in seen:
                continue
            seen.add(P)
            cs = legal_next(P)
            if len(cs) < 2:
                continue
            hs = [first_pillar(P, x) for x in cs]
            c['_束'] += 1
            for t in range(len(cs) - 1):
                a, b = hs[t][0], hs[t + 1][0]
                if a is None or b is None:
                    c['柱を出さない（縮約に飲まれた）'] += 1
                    continue
                c['_隣'] += 1
                if a < b:
                    c['増'] += 1
                elif a == b:
                    c['同じ'] += 1
                else:
                    c['**減（CM の破れ）**'] += 1
                    if len(ex) < verbose:
                        ex.append((P, cs[t], hs[t], cs[t + 1], hs[t + 1]))
    print('== %s  接頭辞（束）%d  隣 %d  %.0fs'
          % (name, c['_束'], c['_隣'], time.time() - t0))
    for k in sorted(c, key=str):
        if not k.startswith('_'):
            print('   %-24s %d' % (k, c[k]))
    for P, c1, h1, c2, h2 in ex:
        print('   ### CM の破れ')
        print('      P  = %s' % ''.join(str(x).replace(' ', '') for x in P))
        print('      c1 = %s -> %s (%s, %s)' % (c1, h1[0], h1[1], h1[2]))
        print('      c2 = %s -> %s (%s, %s)' % (c2, h2[0], h2[1], h2[2]))
    return c


if __name__ == '__main__':
    W = sys.argv[1]
    if W == 'stts':
        P = r7.stts_pool(int(sys.argv[2]), int(sys.argv[3]))
        nm = 'ST_TS v<=%s len<=%s' % (sys.argv[2], sys.argv[3])
    else:
        from rows3 import gen3, key
        P = [tuple(map(tuple, M)) for M in sorted(gen3('BMS', int(W), zcap=1), key=key)]
        nm = 'gen3 <=%s の接頭辞' % W
    run(P, nm)
