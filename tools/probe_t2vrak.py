"""Measure the residual T2VRAK KAG (V3T2VRAK.lean) and VDomF on t = 2 matrices strictly below SRO, n = 2, 3.
N = M[n], P = M[n-1], x = last column, r = P_2(x), L = x - r, V = v_P(r), V' = v_N(r + L), f = shf V V'.
At every guarded copy frame of P (i >= r, le1 P r i, every child c of CL P i, o(c) = psi s y 0), every level
u in {v_P(i)} + path levels of P at i (PathLvAll) with u <= V:
  KA : forall d in comps u a, exists d' in comps u (f a), d <= d'        (a = v_P(i))
  KG : V < s -> forall g in compsAN V u (sub s V), g <= Omega_s or g <= B   (B = spArg a 0 (sumN Lc))
       compsAN = the components at moving positions (under subscripts > V only).
  VD : VDomF V V' a at u' in {0} + indices of V', f a  (t0's shared condition; for reference).
Usage: nice -n 15 python3 probe_t2vrak.py --output DIR [SET ...]   (at most 4 workers)
"""
import sys
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/ytosk-handoff/probes/t2-1016b')
from probe_inv2 import SRO, main
from probe_inv3_prefix import Ctx, Z, lt, le, comps
from vracopy import sh, shf, frames
from lhd_exact import indices
import trio
import ytosk_eval as Y


def compsA(V, u, t):
    out = []
    while t:
        s0, y, c = t
        if not lt(s0, u) and lt(V, s0):
            out.append(y); out += compsA(V, u, y); out += compsA(V, u, Y.sub(s0, V))
        t = c
    return out


def le1(C, r, i):
    t = i
    while t is not None and t > r: t = C.e.par(1, t)
    return t == r


def measure(matrix):
    M = list(matrix)
    cnt, ex = Counter(input=1), {}
    if not M < SRO:
        cnt['outside_SRO'] += 1; return cnt, ex
    x = len(M) - 1
    if x < 1 or M[x][2] == 0:
        return cnt, ex
    C = Ctx(M)
    if not C.ok:
        cnt['eval_failed'] += 1; return cnt, ex
    r = C.e.par(2, x)
    if r is None:
        return cnt, ex
    cnt['t2'] += 1
    L = x - r
    for n in (2, 3):
        N = trio.expand(M, n); P = trio.expand(M, n - 1)
        CN, CP = Ctx(N), Ctx(P)
        if not (CN.ok and CP.ok):
            cnt['eval_failed_N'] += 1; continue
        _, pP = frames(CP)
        V = CP.v(r); V2 = CN.v(r + L)
        for i in range(r, len(P)):
            if not le1(CP, r, i): continue
            a = CP.v(i); fa = shf(V, V2, a)
            us2 = {Z}; indices(V2, us2); indices(fa, us2)
            for u2 in us2:
                if lt(fa, u2): continue
                cfa2 = comps(u2, fa)
                cnt['VD.cases'] += 1
                if not all(le(g, (fa, Z, Z)) or any(le(g, d) for d in cfa2) for g in comps(u2, V2)):
                    cnt['VD.failures'] += 1
                    ex.setdefault('VD', {'matrix': M, 'n': n, 'i': i, 'u': Y.tstr(u2)})
            cl = CP.CL(i)
            for idx, c in enumerate(cl):
                s, y, _ = CP.o(c); B = CP.pre(i, cl[:idx])
                for u in pP[i] | {a}:
                    if not le(u, V): continue
                    cfa = comps(u, fa)
                    cnt['KA.cases'] += 1
                    if not all(any(le(d, d2) for d2 in cfa) for d in comps(u, a)):
                        cnt['KA.failures'] += 1
                        ex.setdefault('KA', {'matrix': M, 'n': n, 'i': i, 'c': c, 'u': Y.tstr(u)})
                    if lt(V, s):
                        cnt['KG.cases'] += 1
                        if not all(le(g, (s, Z, Z)) or le(g, B) for g in compsA(V, u, Y.sub(s, V))):
                            cnt['KG.failures'] += 1
                            ex.setdefault('KG', {'matrix': M, 'n': n, 'i': i, 'c': c, 'u': Y.tstr(u)})
    return cnt, ex


if __name__ == '__main__':
    main(measure, fields=('KA', 'KG', 'VD'), case_unit='guarded copy frame / level',
         definitions=('V3T2VRAK.lean KAG', 'V3RwClSh.lean VDomF'))
