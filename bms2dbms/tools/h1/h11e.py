# -*- coding: utf-8 -*-
"""H11 (3): 破れの現場の濃縮率。対照は「一致している対」の同じ場所。"""
import sys, pickle
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/g2')
import rows3, rows3F, provc
from rows3 import is_branch
from core import expand, show

rows = pickle.load(open('/tmp/h1work/h11rows.pkl', 'rb'))
print('破れ %d 対' % len(rows))
short = [r for r in rows if r['tag'] != 'ok']
ok = [r for r in rows if r['tag'] == 'ok']

# ---- (a) 「像が短い」70 対の正体
print()
print('=== 像が T の真の接頭辞になる %d 対 ===' % len(short))
c = Counter()
for r in short:
    S, T = r['A'], r['T']
    lens = []
    ncs = []
    for n in range(1, 9):
        E = [tuple(x) for x in expand(S, n)]
        if not E:
            break
        out, nc = rows3.b2d3n(list(E))
        lens.append(len(out))
        ncs.append(nc)
    r['lens'] = lens
    r['ncs'] = ncs
    r['LT'] = len(T)
    hit = [i + 1 for i, L in enumerate(lens) if L == len(T)]
    c['長さが合う n がある' if hit else '長さが合う n が無い'] += 1
    c['縮約が発火する n がある' if any(ncs) else '縮約は発火しない'] += 1
for k, v in c.most_common():
    print('   %-32s %d' % (k, v))
print()
for r in short[:6]:
    print('   A=%-40s m=%d  len(T)=%2d  像の長さ %s  縮約 %s'
          % (show([list(x) for x in r['A']]), r['m'], r['LT'],
             r['lens'], r['ncs']))

# ---- (b) 濃縮率
print()
print('=== 濃縮率（破れの現場 vs 対照） ===')


def feats(E, rec, PR, k, off):
    kind, o, why, ctx = PR[k]
    R = next((x for x in rec if x['off'] == o), None)
    f = {}
    f['ctx=cR'] = ('cR' in ctx)
    f['ctx!=()'] = bool(ctx)
    f['tie'] = (why == 'tie')
    f['branch'] = is_branch(E[o])
    f['why=None'] = (why is None)
    f['first'] = R['first'] if R else None
    f['nA=0'] = (R['nA'] == 0) if R else None
    f['kind!=body'] = (kind != 'body')
    f['ANCHOR'] = (tuple(E[o]) == (1, 1, 0))
    f['w_col'] = (E[o][1] == 0 and E[o][0] >= 1)
    f['lenL<=1'] = (len(R['L']) <= 1) if R else None
    f['v>=1'] = (E[o][1] >= 1)
    return f


N = Counter()
D = Counter()
for r in ok:
    E, PR, k = r['E'], None, r['k']
    C, PR = provc.b2d3p(list(E))
    out, rec = rows3F.b2d3F(list(E))
    for key, val in feats(E, rec, PR, k, r['off']).items():
        D[key] += 1
        if val:
            N[key] += 1
print('破れ側 %d 本:' % len(ok))
for key in sorted(D):
    print('   %-12s %3d / %3d  = %5.1f%%' % (key, N[key], D[key],
                                             100.0 * N[key] / D[key]))

# 対照: lim=6 の全行列を n<=2 展開し、conv3 が出した全部の柱
CN = Counter()
CD = 0
A = sorted(rows3.gen3('BMS', 6, zcap=1), key=rows3.key)
for M in A[:4000]:
    S = tuple(map(tuple, M))
    for n in (1, 2):
        E = [tuple(x) for x in expand(S, n)]
        if not E:
            continue
        C, PR = provc.b2d3p(list(E))
        out, rec = rows3F.b2d3F(list(E))
        for k in range(len(PR)):
            CD += 1
            for key, val in feats(tuple(E), rec, PR, k, PR[k][1]).items():
                if val:
                    CN[key] += 1
print()
print('対照 %d 本（lim=6 の 4000 個 x n<=2 の全柱）:' % CD)
for key in sorted(CN | Counter({k: 0 for k in D})):
    b = 100.0 * CN[key] / max(CD, 1)
    a = 100.0 * N[key] / max(D[key], 1)
    print('   %-12s 対照 %5.2f%%  破れ %5.1f%%  濃縮 %sx'
          % (key, b, a, ('%.1f' % (a / b)) if b > 0 else 'inf'))
