# -*- coding: utf-8 -*-
"""H12: 証人 70 件の破れの現場の濃縮率（対照 = lim=6 の全柱）。"""
import sys, pickle
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/g2')
import rows3, provc
from rows3 import is_branch, is_w_col
from core import expand

rows = pickle.load(open('/tmp/h1work/h12rows.pkl', 'rb'))


def feats(E, PR, k):
    kind, o, why, ctx = PR[k]
    w = str(why)
    return {
        'ctx=cR': 'cR' in ctx, 'ctx=cA': 'cA' in ctx, 'ctx=cB': 'cB' in ctx,
        'ctx=cU': 'cU' in ctx, 'ctx!=()': bool(ctx),
        'branch': is_branch(E[o]), 'w_col': is_w_col(E[o]),
        'why=tie': w == 'tie', 'why=after_w': w.startswith('after_w'),
        'why=closes': w.startswith('closes'), 'why=prev0': w.startswith('prev0'),
        'why=wchain': w.startswith('wchain'), 'why=None': w == 'None',
        'kind!=body': kind != 'body',
    }


N, D = Counter(), 0
for r in rows:
    C, PR = provc.b2d3p(list(r['B']))
    D += 1
    for kk, vv in feats(r['B'], PR, r['k']).items():
        if vv:
            N[kk] += 1
CN, CD = Counter(), 0
A = sorted(rows3.gen3('BMS', 6, zcap=1), key=rows3.key)
for M in A[:4000]:
    S = tuple(map(tuple, M))
    for n in (1, 2):
        E = [tuple(x) for x in expand(S, n)]
        if not E:
            continue
        C, PR = provc.b2d3p(list(E))
        for k in range(len(PR)):
            CD += 1
            for kk, vv in feats(tuple(E), PR, k).items():
                if vv:
                    CN[kk] += 1
print('証人 %d 件 / 対照 %d 柱' % (D, CD))
print('%-14s %8s %8s %8s' % ('読み', '対照', '破れ', '濃縮'))
out = []
for kk in N | Counter({k: 0 for k in CN}):
    b = 100.0 * CN[kk] / max(CD, 1)
    a = 100.0 * N[kk] / max(D, 1)
    out.append(((a / b) if b else 0, kk, b, a))
for e, kk, b, a in sorted(out, reverse=True):
    print('%-14s %7.2f%% %7.1f%% %7.1fx' % (kk, b, a, e))
