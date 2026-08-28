# -*- coding: utf-8 -*-
"""課題 R13 (3): `copy_head` / `top_level` は**次の柱について collt で単調**か。

接頭辞 `P` を固定し、合法な次の柱 `c` を全部並べて（`collt` の昇順）、
述語の真偽が **偽 -> 真 の 1 回だけ変わる**（＝ 上に閉じている）かを見る。
`copy_head` は shallow 化する条項なので、上に閉じていないと柱単調性が壊れる。
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, r7
from rows3 import copy_head, top_level, term_top
from core import isstd
from collections import Counter


def legal_next(P, zcap=1):
    """`P` のあとに来られる BMS 標準形の列（列だけを返す）。"""
    amax = P[-1][0] + 1
    out = []
    for a in range(amax + 1):
        for b in range(a + 1):
            for cz in range(min(b, zcap) + 1):
                T = P + ((a, b, cz),)
                if isstd(T, 'BMS'):
                    out.append((a, b, cz))
    return sorted(out)


def run(pop, name, verbose=3):
    c = Counter(); ex = {}
    t0 = time.time()
    seen = set()
    for i, M in enumerate(pop):
        if i % 5000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        for j in range(1, len(M)):
            P = tuple(M[:j])
            if P in seen:
                continue
            seen.add(P)
            cs = legal_next(P)
            if len(cs) < 2:
                continue
            for nm, f in (('copy_head', lambda Mo, k: copy_head(Mo, k)),
                          ('top_level', lambda Mo, k: top_level(Mo, k)),
                          ('term_top', lambda Mo, k: term_top(Mo, k))):
                vals = [f(P + (x,), j) for x in cs]
                c['_%s 判定' % nm] += 1
                # 上に閉じている = 偽…偽真…真（真->偽 の落ちが無い）
                fall = any(vals[t] and not vals[t + 1] for t in range(len(vals) - 1))
                if fall:
                    c['**%s が上に閉じていない**' % nm] += 1
                    if nm not in ex:
                        ex[nm] = (P, cs, vals)
                else:
                    c['%s は上に閉じている' % nm] += 1
    print('== %s  接頭辞 %d 個  %.0fs' % (name, len(seen), time.time() - t0))
    for k in sorted(c, key=str):
        if not k.startswith('_'):
            print('   %-36s %d' % (k, c[k]))
    for nm, (P, cs, vals) in ex.items():
        print('   ### %s が落ちる例' % nm)
        print('      P = %s' % ''.join(str(x).replace(' ', '') for x in P))
        for x, vv in zip(cs, vals):
            print('        c=%s -> %s' % (x, vv))
    return c


if __name__ == '__main__':
    W = sys.argv[1]
    if W == 'stts':
        P = r7.stts_pool(int(sys.argv[2]), int(sys.argv[3]))
        nm = 'ST_TS v<=%s len<=%s' % (sys.argv[2], sys.argv[3])
    else:
        from rows3 import gen3, key
        P = [tuple(map(tuple, M)) for M in sorted(gen3('BMS', int(W), zcap=1), key=key)]
        nm = 'gen3 <=%s' % W
    run(P, nm)
