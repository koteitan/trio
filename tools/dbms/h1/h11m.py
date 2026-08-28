# -*- coding: utf-8 -*-
"""H11 (1): conv3 の `first` / `ps` / `split0` の切れ目は行列から読めるか。

行列から読める版:
    par0(Mo, j)      行 0 の親（rows3.par0）
    first_mat(j)  =  j == 0 or par0(Mo, j) == j - 1   （行 0 の親の第 1 子か）
    ps_mat(j)     =  par0 の (行1, 行2)、親が無ければ (0,0)
    nA_mat(j)     =  split0 が切る長さ（j の子孫の本数）… ただしブロックの
                     末尾で切れるので「M の中で」の値と比べる必要がある

conv3 が持ち回る値とこれを全部の柱で比べる。食い違えば **非同変な読み**。
"""
import sys
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import rows3, rows3F
from rows3 import par0
from core import expand, show


def first_mat(Mo, j):
    return j == 0 or par0(Mo, j) == j - 1


def ps_mat(Mo, j):
    i = par0(Mo, j)
    return (0, 0) if i < 0 else (Mo[i][1], Mo[i][2])


def nA_mat(Mo, j):
    """j の行 0 の子孫の本数（行列全体で見た split0 の切れ目）。"""
    i = j + 1
    while i < len(Mo) and Mo[i][0] > Mo[j][0]:
        i += 1
    return i - j - 1


def scan(Ms, tag=''):
    c = Counter()
    ex = {}
    for M in Ms:
        Mo = tuple(map(tuple, M))
        out, rec = rows3F.b2d3F(list(Mo))
        for R in rec:
            j = R['off']
            c['_柱'] += 1
            fm, pm, nm = first_mat(Mo, j), ps_mat(Mo, j), nA_mat(Mo, j)
            bad = []
            if R['first'] != fm:
                bad.append('first')
            if R['ps'] != pm:
                bad.append('ps')
            if R['nA'] != nm:
                bad.append('nA')
            k = (tuple(bad), R['ctx'])
            c[k] += 1
            if bad and k not in ex:
                ex[k] = (Mo, j, R['first'], fm, R['ps'], pm, R['nA'], nm)
    return c, ex


if __name__ == '__main__':
    lim = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    A = sorted(rows3.gen3('BMS', lim, zcap=1), key=rows3.key)
    Ms = [tuple(map(tuple, M)) for M in A]
    if nmax:
        E = []
        for M in Ms:
            for n in range(1, nmax + 1):
                x = [tuple(y) for y in expand(M, n)]
                if x:
                    E.append(tuple(x))
        Ms = Ms + E
    c, ex = scan(Ms)
    n = c['_柱']
    print('lim=%d 展開 n<=%d: 行列 %d 個 / 柱 %d 本' % (lim, nmax, len(Ms), n))
    for k, v in c.most_common():
        if k == '_柱':
            continue
        print('   %-46s %7d  (%.4f%%)' % (str(k), v, 100.0 * v / max(n, 1)))
    print()
    for k, e in list(ex.items())[:8]:
        Mo, j, f, fm, p, pm, na, nm = e
        print('=== %s' % str(k))
        print('   %s  off=%d 柱=%s' % (show([list(x) for x in Mo]), j, Mo[j]))
        print('   first %s vs %s / ps %s vs %s / nA %s vs %s'
              % (f, fm, p, pm, na, nm))
