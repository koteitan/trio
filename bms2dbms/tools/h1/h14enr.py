# -*- coding: utf-8 -*-
"""H14 (1): 残る 18 個の濃縮表（対照 = lim=6 の全柱）。"""
import sys, pickle
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/g2')
import rows3, provc
from rows3 import is_branch, is_w_col, ANCHOR
from core import expand

rows = pickle.load(open('/tmp/h1work/h13rows.pkl', 'rb'))


def feats(E, PR, k):
    kind, o, why, ctx = PR[k]
    w = str(why)
    c = tuple(E[o])
    return {
        'ctx=cR': 'cR' in ctx, 'ctx=cA': 'cA' in ctx, 'ctx=cB': 'cB' in ctx,
        'ctx=cU': 'cU' in ctx, 'ctx!=()': bool(ctx),
        'branch': is_branch(c), 'w_col': is_w_col(c), 'ANCHOR': c == ANCHOR,
        'why=tie': w == 'tie', 'why=after_w': w.startswith('after_w'),
        'why=closes': w.startswith('closes'), 'why=prev0': w.startswith('prev0'),
        'why=plain': w.startswith('plain'), 'why=wchain': w.startswith('wchain'),
        'why=None': w == 'None', 'kind!=body': kind != 'body',
        'shallow': w.endswith('/shallow'), 'deep': w.endswith('/deep'),
    }


N, D = Counter(), 0
for r in rows:
    Bt = r[0]
    C, PR = provc.b2d3p(list(Bt))
    D += 1
    for kk, vv in feats(Bt, PR, r[3]).items():
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
