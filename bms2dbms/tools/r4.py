# -*- coding: utf-8 -*-
"""課題 L18 の 2 件: 節 9 はタイトか / `d+1+(p.1-U.head.1) <= dd2` は真か。

`rows3.py` は触らない（monkeypatch）。母数は **`conv3` の全呼び出し**。
"""
import sys, os, time, pickle
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rows3
from rows3 import gen3, key
from core import expand, isstd

_conv3 = rows3.conv3
SRC = open(rows3.__file__).read().split('\n')
CU_LINE = next(i for i, l in enumerate(SRC, 1)
               if l.strip().startswith('cU = conv3(U, d + 1'))

C = {}
EX = {}
CUR = [None]


def bump(k, n=1):
    C[k] = C.get(k, 0) + n


def ex(k, item, lim=6):
    L = EX.setdefault(k, [])
    if len(L) < lim:
        L.append(item)


def conv3_probe(*a, **kw):
    fr = sys._getframe(1)
    M = a[0] if a else kw.get('M')
    d = a[1] if len(a) > 1 else kw.get('d', 0)
    st = a[8] if len(a) > 8 else kw.get('st')
    dm0 = list(st['dmap']) if st is not None else None

    # ---- (2) `cU` の呼び出し点: d + 1 + (p.1 - U.head.1) <= dd2
    if (fr.f_code.co_name == 'conv3' and fr.f_lineno == CU_LINE
            and M and st is not None):
        L = fr.f_locals
        p, dd2, dout = L.get('p'), L.get('dd'), L.get('d')
        if p is not None and dd2 is not None:
            uh = M[0][0]
            bump('cU_calls')
            if uh == p[0]:
                bump('cU_Uhead_eq_p')
            elif uh < p[0]:
                bump('cU_Uhead_lt_p')
            else:
                bump('cU_Uhead_gt_p')
            need = dout + 1 + (p[0] - uh)
            if not (need <= dd2):
                bump('cU_dd2_viol')
                ex('CUDD', (CUR[0], tuple(p), uh, dout, dd2))
            if not (need <= dd2 - 1):
                bump('cU_dd2_pc')          # 陽性対照（dd2 を 1 小さく）
            if need == dd2:
                bump('cU_dd2_eq')          # 等号（タイトさ）

    r = _conv3(*a, **kw)

    # ---- (1) 節 9 の d / d+1 / d+2（全 k・k>m・k>=m で分けて数える）
    if M and st is not None:
        m = M[0][0]
        dm1 = st['dmap']
        bump('c9_calls')
        for k in range(len(dm1)):
            keep = k < len(dm0) and dm1[k] == dm0[k]
            for lab, base in (('d', d), ('d1', d + 1), ('d2', d + 2)):
                ok = (base <= dm1[k]) or keep
                if not ok:
                    bump('c9_%s_all' % lab)
                    if k > m:
                        bump('c9_%s_kgtm' % lab)
                        ex('C9GT_' + lab,
                           (CUR[0], tuple(M[0]), k, m, d, dm0, list(dm1)))
                    if k >= m:
                        bump('c9_%s_kgem' % lab)
                    if k == m:
                        bump('c9_%s_keqm' % lab)
                    if k < m:
                        bump('c9_%s_kltm' % lab)
                        ex('C9LT_' + lab,
                           (CUR[0], tuple(M[0]), k, m, d, dm0, list(dm1)))
    return r


rows3.conv3 = conv3_probe


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
        print('   %-18s %d' % (k, C[k]))
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
                open('/home/koteitan/proofs/dbms/bms2dbms/tools/r4_%s.pkl' % w, 'wb'))
