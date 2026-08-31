# -*- coding: utf-8 -*-
"""課題 L17/L18: 4 つの再帰の出口が **外側の `(d, p.1)` で揃った `Dm10`** を
満たすかを、呼び出し点ごとに測る。`rows3.py` は無改変（monkeypatch）。

    Dm10 d m (res) := ∀ j, m ≤ j < |res.2.dmap| → d + (j - m) ≤ res.2.dmap[j]

各再帰 `r*` について `Dm10 d_outer p.1 (r*.2)` を判定する。
陽性対照は `d_outer + 1` にした版。
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
    if t.startswith('cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False'):
        SITE[_i] = 'rA_contr'
    elif t.startswith('cU = conv3(U, d + 1'):
        SITE[_i] = 'rU'
    elif t.startswith('cB = conv3(Bq, d,'):
        SITE[_i] = 'rB_contr'
    elif t.startswith('cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0'):
        SITE[_i] = 'rA_plain'
    elif t.startswith('cB = conv3(B, d, LS'):
        SITE[_i] = 'rB_plain'
    elif t.startswith('cR = conv_resid('):
        SITE[_i] = 'rR'
assert len(set(SITE.values())) == 6, SITE

C = {}
EX = {}
CUR = [None]


def bump(k, n=1):
    C[k] = C.get(k, 0) + n


def chk(tag, st, d, m):
    dm = st['dmap']
    bump('%s_calls' % tag)
    for j in range(m, len(dm)):
        if not (d + (j - m) <= dm[j]):
            bump('%s_viol' % tag)
            L = EX.setdefault(tag, [])
            if len(L) < 5:
                L.append((CUR[0], d, m, j, list(dm)))
        if not (d + 1 + (j - m) <= dm[j]):
            bump('%s_pc' % tag)          # 陽性対照（外側の d を +1）


def conv3_probe(*a, **kw):
    fr = sys._getframe(1)
    site = SITE.get(fr.f_lineno) if fr.f_code.co_name == 'conv3' else None
    st = a[8] if len(a) > 8 else kw.get('st')
    r = _conv3(*a, **kw)
    if site and st is not None:
        L = fr.f_locals
        p, dout = L.get('p'), L.get('d')
        if p is not None and dout is not None:
            chk(site, st, dout, p[0])
    return r


def conv_resid_probe(rest, rd, Lr, ps, pw, st, nx, off):
    fr = sys._getframe(1)
    out = _conv_resid(rest, rd, Lr, ps, pw, st, nx, off)
    L = fr.f_locals
    p, dout = L.get('p'), L.get('d')
    if p is not None and dout is not None:
        chk('rR', st, dout, p[0])
    return out


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
        print('   %-16s %d' % (k, C[k]))
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
                open('/home/koteitan/proofs/dbms/bms2dbms/tools/r5_%s.pkl' % w, 'wb'))
