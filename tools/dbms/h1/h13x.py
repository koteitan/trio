# -*- coding: utf-8 -*-
"""H13: 「右を遠くまで見る」素性を足したら分かれるか。

素性が完全に一致する正例/負例の対は **11 列の共通接頭辞**をもち、決定の場所は
その中（off=5）にある。ちがうのは 12 列目以降。だから近傍の素性では原理的に
分けられない。**次の項の頭より先を読む素性**を足して確かめる。
"""
import sys, os, pickle
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
from rows3 import term_top, par0, is_branch, is_w_col, ANCHOR, copy_head
from h6feat import atoms, next_term
from h11feat import extra


def far(Mo, off):
    """右を遠くまで見る素性。"""
    n = len(Mo)
    p = tuple(Mo[off])
    a = {}
    # 次の項の頭、その次の項の頭
    ths = [j for j in range(off + 1, n) if term_top(Mo, j)]
    for lv in (1, 2, 3):
        j = ths[lv - 1] if lv - 1 < len(ths) else None
        c = tuple(Mo[j]) if j is not None else (-9, -9, -9)
        a['f%d_none' % lv] = j is None
        for k, rn in ((0, 'r0'), (1, 'r1'), (2, 'r2')):
            a['f%d_%s_eq' % (lv, rn)] = c[k] == p[k]
            a['f%d_%s_lt' % (lv, rn)] = c[k] < p[k]
            a['f%d_%s_gt' % (lv, rn)] = c[k] > p[k]
        a['f%d_w' % lv] = is_w_col(c)
        a['f%d_br' % lv] = (c[1] == 1 and c[2] == 0 and c[0] >= 2)
        a['f%d_anch' % lv] = (c == ANCHOR)
        a['f%d_chead' % lv] = j is not None and copy_head(Mo, j)
    a['nth0'] = len(ths) == 0
    a['nth1'] = len(ths) == 1
    a['nth_ge3'] = len(ths) >= 3
    # 行列の末尾
    L = tuple(Mo[-1])
    for k, rn in ((0, 'r0'), (1, 'r1'), (2, 'r2')):
        a['last_%s_eq' % rn] = L[k] == p[k]
        a['last_%s_lt' % rn] = L[k] < p[k]
        a['last_%s_gt' % rn] = L[k] > p[k]
    a['last_w'] = is_w_col(L)
    a['last_br'] = (L[1] == 1 and L[2] == 0 and L[0] >= 2)
    a['last_z'] = L[2] > 0
    # この柱の属するユニット（前の項の頭 .. 次の項の頭）の外に何があるか
    th = max([j for j in range(off) if term_top(Mo, j)] + [0])
    nt = ths[0] if ths else n
    a['unit_len_ge4'] = nt - th >= 4
    a['unit_len_ge6'] = nt - th >= 6
    a['after_unit0'] = nt >= n
    a['after_unit_ge4'] = n - nt >= 4
    a['after_unit_ge8'] = n - nt >= 8
    # 次のユニットは今のユニットの写しか（行 0 のずらしが一定）
    same = False
    if ths and nt - th <= n - nt:
        d0 = Mo[nt][0] - Mo[th][0]
        same = all(Mo[nt + i][0] - Mo[th + i][0] == d0 and
                   Mo[nt + i][2] == Mo[th + i][2] for i in range(nt - th))
    a['next_unit_copy'] = same
    return a


names0, X0, Y0, META0 = pickle.load(open(sys.argv[1], 'rb'))
X, Y, names = [], [], None
for (Mo, off), y in zip(META0, Y0):
    a = atoms(Mo, off)
    a.update(extra(Mo, off))
    a.update(far(Mo, off))
    if names is None:
        names = sorted(a)
    X.append(tuple(bool(a[nm]) for nm in names))
    Y.append(y)
P = [i for i, y in enumerate(Y) if y]
N = [i for i, y in enumerate(Y) if not y]
nx = {}
for i in N:
    nx.setdefault(X[i], []).append(i)
coll = [i for i in P if X[i] in nx]
print('%s: 正例 %d / 負例 %d / 素性 %d -> **完全一致する正例 %d**'
      % (os.path.basename(sys.argv[1]), len(P), len(N), len(names), len(coll)))
pickle.dump((names, X, Y, META0), open(sys.argv[1].replace('.pkl', '_far.pkl'), 'wb'))
