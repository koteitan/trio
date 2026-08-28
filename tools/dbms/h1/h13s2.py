# -*- coding: utf-8 -*-
"""H13 (5): `SandwichUT3` の (S2) `BadRootT3` の測定（仕様は lean/L1-NOTES §L12.5）。

    t  = srow A (|A|-1)          末尾列が崩れる行（pim の t）
    r  = parent A t (|A|-1)      バッドルート
    d0 = A[-1].0 - A[r].0        d1 = A[-1].1 - A[r].1
  像 B = conv3 A で同じ 4 つ (t', r', d0', d1') を取り

    (S2-a) t' = t   (S2-b) r' = img r   (S2-c) d1' = d1
    (S2-d) d0' = B[-1].0 - B[img r].0

`img j` = 入力の第 j 列の**本体柱**の像での添字。`g2/provc.py` の PROV
（柱ごとに (kind, off, why, ctx) を出力順に積む）から読む。

陽性対照 P1 = r'+1 / P2 = d1+1 / P3 = img を恒等写像に。
"""
import sys, time
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
import rows3, provc, core
from rows3 import gen3, key
from core import pim, show


def badroot(S):
    """(t, r) or None（末尾が孤児 / 全 0）。"""
    X = len(S)
    if X < 2:
        return None
    x = X - 1
    Y = len(S[0])
    if all(v == 0 for v in S[x]):
        return None
    t = max(y for y in range(Y) if S[x][y] > 0)
    r = pim(S)[x][t]
    if r == -1:
        return None
    return t, r


def imgmap(M):
    """(像, img)。img[j] = 入力の第 j 列の本体柱の像での添字（無ければ None）。"""
    C, PR = provc.b2d3p(list(M))
    img = [None] * len(M)
    for i, (kind, off, why, ctx) in enumerate(PR):
        if kind == 'body':
            img[off] = i
        elif img[off] is None:
            img[off] = i
    return C, img


def run(lim, mode='real', verbose=3):
    A = sorted(gen3('BMS', lim, zcap=1), key=key)
    c = Counter()
    ex = {}
    t0 = time.time()
    for i, M in enumerate(A):
        if i % 20000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
        S = tuple(map(tuple, M))
        br = badroot(S)
        if br is None:
            c['除外（末尾が孤児 / |A|<2）'] += 1
            continue
        t, r = br
        d0 = S[-1][0] - S[r][0]
        d1 = S[-1][1] - S[r][1]
        B, img = imgmap(S)
        br2 = badroot(B)
        if br2 is None:
            c['像の末尾が孤児'] += 1
            c['_母数'] += 1
            c['破れ t=%d' % t] += 1
            continue
        c['_母数'] += 1
        c['_t=%d' % t] += 1
        t2, r2 = br2
        ir = img[r]
        if mode == 'P1':
            ir = None if ir is None else ir + 1
        if mode == 'P3':
            ir = r
        d0p = B[-1][0] - B[r2][0]
        d1p = B[-1][1] - B[r2][1]
        bad = []
        if t2 != t:
            bad.append('a')
        if ir is None or r2 != ir:
            bad.append('b')
        if d1p != (d1 + 1 if mode == 'P2' else d1):
            bad.append('c')
        if ir is None or not (0 <= ir < len(B)) or d0p != B[-1][0] - B[ir][0]:
            bad.append('d')
        for k in bad:
            c['S2-%s の破れ (t=%d)' % (k, t)] += 1
        if bad:
            c['破れ t=%d' % t] += 1
            key2 = (tuple(bad), t)
            if key2 not in ex:
                ex[key2] = (S, B, t, r, d0, d1, t2, r2, d0p, d1p, ir)
    n = c['_母数']
    nb = sum(v for k, v in c.items() if k.startswith('破れ'))
    print('lim=%d mode=%s: 母数 %d（t=1 が %d / t=2 が %d、除外 %d）  破れ %d  (%.0fs)'
          % (lim, mode, n, c['_t=1'], c['_t=2'], c['除外（末尾が孤児 / |A|<2）'],
             nb, time.time() - t0))
    for k in sorted(c, key=str):
        if k.startswith('_') or k.startswith('除外'):
            continue
        print('   %-24s %d' % (k, c[k]))
    for k, e in list(ex.items())[:verbose]:
        S, B, t, r, d0, d1, t2, r2, d0p, d1p, ir = e
        print('   例 %s' % str(k))
        print('      A = %s' % show([list(x) for x in S]))
        print('      B = %s' % show([list(x) for x in B]))
        print('      (t,r,d0,d1) = (%d,%d,%d,%d)   (t\',r\',d0\',d1\') = (%d,%d,%d,%d)  img r = %s'
              % (t, r, d0, d1, t2, r2, d0p, d1p, ir))
    return c


if __name__ == '__main__':
    lim = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    for mode in (sys.argv[2:] or ['real', 'P1', 'P2', 'P3']):
        run(lim, mode)
        print()
