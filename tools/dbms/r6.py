# -*- coding: utf-8 -*-
"""L2 の最後の 2 本:
  (i)  側条件 a4 の**たるみ** slack = (rd + p.1) - (d + rest2.head.1) の分布
  (ii) `Bq.head.1 = p.1` か（`U.head.1 = p.1` と同じ形）
`rows3.py` は無改変（monkeypatch）。母数は `conv3` の全呼び出し。
"""
import sys, os, time, pickle
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rows3
from rows3 import gen3, key
from core import expand, isstd

_conv3 = rows3.conv3
_conv_resid = rows3.conv_resid
SRC = open(rows3.__file__).read().split('\n')
SITE = {}
for _i, _l in enumerate(SRC, 1):
    t = _l.strip()
    if t.startswith('cB = conv3(Bq, d,'):
        SITE[_i] = 'Bq'
    elif t.startswith('cB = conv3(B, d, LS'):
        SITE[_i] = 'B'
    elif t.startswith('cU = conv3(U, d + 1'):
        SITE[_i] = 'U'
    elif t.startswith('cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False'):
        SITE[_i] = 'A_contr'
    elif t.startswith('cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0'):
        SITE[_i] = 'A_plain'
assert len(set(SITE.values())) == 5, SITE

C = {}
EX = {}
CUR = [None]


def bump(k, n=1):
    C[k] = C.get(k, 0) + n


def ex(k, item, lim=5):
    L = EX.setdefault(k, [])
    if len(L) < lim:
        L.append(item)


def conv3_probe(*a, **kw):
    fr = sys._getframe(1)
    site = SITE.get(fr.f_lineno) if fr.f_code.co_name == 'conv3' else None
    M = a[0] if a else kw.get('M')
    if site and M:
        p = fr.f_locals.get('p')
        if p is not None:
            h = M[0][0]
            bump('%s_calls' % site)
            bump('%s_head-p = %+d' % (site, h - p[0]))
            if site in ('Bq', 'B') and h != p[0]:
                ex('NE_' + site, (CUR[0], tuple(p), tuple(M[0]), h - p[0]))
            if site == 'U' and h != p[0]:
                ex('NE_U', (CUR[0], tuple(p), tuple(M[0]), h - p[0]))
    return _conv3(*a, **kw)


def conv_resid_probe(rest, rd, Lr, ps, pw, st, nx, off):
    L = sys._getframe(1).f_locals
    p, d = L.get('p'), L.get('d')
    if rest and p is not None and d is not None:
        bump('a4_calls')
        slack = (rd + p[0]) - (d + rest[0][0])
        bump('a4_slack = %+d' % slack)
        if slack < 0:
            bump('a4_VIOL')
            ex('A4V', (CUR[0], tuple(p), tuple(rest[0]), rd, d, slack))
        if slack > 1:
            bump('a4_slack_gt1')          # (i) の問い: 2 以上が出るか
            ex('A4S', (CUR[0], tuple(p), tuple(rest[0]), rd, d, slack))
        if slack != 0:
            bump('a4_pc_slack0')          # 陽性対照（たるみ 0 を要求）
    return _conv_resid(rest, rd, Lr, ps, pw, st, nx, off)


rows3.conv3 = conv3_probe
rows3.conv_resid = conv_resid_probe


def run1(M):
    CUR[0] = tuple(M)
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0, 'rec': {}}
    return rows3.conv3(list(M), st=st)


def run(pop, name):
    t0 = time.time()
    for M in pop:
        run1(M)
    print('== %s  母数 %d  %.1fs' % (name, len(pop), time.time() - t0))
    for k in sorted(C):
        print('   %-20s %d' % (k, C[k]))
    for k in sorted(EX):
        print('   ### %s' % k)
        for x in EX[k][:3]:
            print('      ', x)
    return dict(C)


def pop_exp(lim=6, ns=(1, 2, 3), rounds=2, maxlen=24):
    base = set(tuple(M) for M in gen3('BMS', lim, zcap=1))
    seen = set(base); cur = set(base)
    for _ in range(rounds):
        nxt = set()
        for M in cur:
            for n in ns:
                E = expand(M, n)
                if E and len(E) <= maxlen and E not in seen and isstd(E, 'BMS'):
                    seen.add(E); nxt.add(E)
        cur = nxt
    return sorted(seen - base, key=key)


if __name__ == '__main__':
    w = sys.argv[1] if len(sys.argv) > 1 else '7'
    if w == 'exp':
        P = pop_exp(6); nm = '<=6 の展開閉包'
    else:
        P = [tuple(M) for M in sorted(gen3('BMS', int(w), zcap=1), key=key)]
        nm = 'gen3 <=%s' % w
    run(P, nm)
    pickle.dump({'c': dict(C), 'e': EX, 'n': len(P)},
                open('/home/koteitan/proofs/dbms/tools/dbms/r6_%s.pkl' % w, 'wb'))
