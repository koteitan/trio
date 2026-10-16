"""Measure the residuals of t2VRAV2_of (V3T2VRA.lean) on t = 2 matrices strictly below SRO, n = 2, 3.
N = M[n], P = M[n-1], x = last column, r = P_2(x), L = x - r, V = v_P(r), V' = v_N(r + L).
Seed columns (T2SeedCol): q = P_0 x; if q = r then {r} else {q, P_0 q}.
Path levels: PathLvAll (V3VSRAll.lean) computed by the frames in column order (frames() of t2's vracopy.py).
  T2VRAPre : k < x, k not a seed column, u a path level of N at k  ==>  u a path level of M at k.
  T2VRACopy: i >= r in P, a rewriting frame (i + L, c) of N with hi(y) != 0, u in {v_N(i+L)} + path levels of N
             at i + L, not v_N(i+L) < u, comps u s != []  ==>  u in {v_P(i)} + path levels of P at i, and u <= V.
  T2VRASeed: seed column i, every counted child frame of N at i, every u in {v_N(i)} + levels  ==>  QVRAt.
  QVRAsh   : instances at guarded copy frames of P (i >= r, le1 P r i, V <= v_P(i)), u <= V among the levels of P
             at i, 0, and the indices of the frame's terms:  QVRAt (P data) u -> QVRAt (sigma data) u.
Usage: nice -n 15 python3 probe_t2vra.py --output DIR [SET ...]   (at most 4 workers)
"""
import sys
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/ytosk-handoff/probes/t2-1016b')
from probe_inv2 import SRO, main
from probe_inv3_prefix import Ctx, Z, lt, le, comps, split, succ
from vracopy import sh, shf, frames
from lhd_exact import indices
import trio
import ytosk_eval as Y


def qvrat(a, B, cv, u):
    s, y, _ = cv
    if not (lt(B, y) and lt((a, Z, Z), (s, y, Z))): return True
    if split(y, (succ(s), Z, Z))[0] == Z: return True
    if lt(a, u): return True
    ca = comps(u, a)
    for g in comps(u, s):
        if not (le(g, (s, Z, Z)) or le(g, B) or any(le(g, d) for d in ca)): return False
    return True


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
    q = C.e.par(0, x)
    seed = {r} if q == r else {q, C.e.par(0, q)}
    fM, pM = frames(C)
    for n in (2, 3):
        N = trio.expand(M, n); P = trio.expand(M, n - 1)
        CN, CP = Ctx(N), Ctx(P)
        if not (CN.ok and CP.ok):
            cnt['eval_failed_N'] += 1; continue
        fN, pN = frames(CN); fP, pP = frames(CP)
        V = CP.v(r); V2 = CN.v(r + L)
        # T2VRAPre
        for k in range(x):
            if k in seed: continue
            for u in pN[k]:
                cnt['T2VRAPre.cases'] += 1
                if u not in pM[k]:
                    cnt['T2VRAPre.failures'] += 1
                    ex.setdefault('T2VRAPre', {'matrix': M, 'n': n, 'k': k, 'u': Y.tstr(u)})
        # T2VRACopy
        for (k, c, B, s, y) in fN:
            i = k - L
            if i < r or i >= len(P): continue
            if split(y, (succ(s), Z, Z))[0] == Z: continue
            aN = CN.v(k); UP = pP[i] | {CP.v(i)}
            for u in pN[k] | {aN}:
                if lt(aN, u) or not comps(u, s): continue
                cnt['T2VRACopy.cases'] += 1
                if not (u in UP and le(u, V)):
                    cnt['T2VRACopy.failures'] += 1
                    ex.setdefault('T2VRACopy', {'matrix': M, 'n': n, 'i': i, 'u': Y.tstr(u)})
        # T2VRASeed
        for i in seed:
            cl = CN.CL(i); a = CN.v(i)
            for idx, c in enumerate(cl):
                B = CN.pre(i, cl[:idx]); cv = CN.o(c)
                for u in pN[i] | {a}:
                    cnt['T2VRASeed.cases'] += 1
                    if not qvrat(a, B, cv, u):
                        cnt['T2VRASeed.failures'] += 1
                        ex.setdefault('T2VRASeed', {'matrix': M, 'n': n, 'i': i, 'c': c, 'u': Y.tstr(u)})
        # QVRAsh on instances
        for (i, d, B, s, y) in fP:
            if i < r or not le1(CP, r, i): continue
            aP = CP.v(i)
            if not le(V, aP): continue
            aS = shf(V, V2, aP); BS = sh(V, V2, B); cS = sh(V, V2, (s, y, Z))
            us = set(pP[i]) | {aP, Z}
            indices(aP, us); indices(s, us); indices(y, us); indices(B, us)
            for u in us:
                if not le(u, V) or not qvrat(aP, B, (s, y, Z), u): continue
                cnt['QVRAsh.cases'] += 1
                if not qvrat(aS, BS, cS, u):
                    cnt['QVRAsh.failures'] += 1
                    ex.setdefault('QVRAsh', {'matrix': M, 'n': n, 'i': i, 'd': d, 'u': Y.tstr(u)})
    return cnt, ex


if __name__ == '__main__':
    main(measure, fields=('T2VRAPre', 'T2VRACopy', 'T2VRASeed', 'QVRAsh'), case_unit='level / frame-level',
         definitions=('V3T2VRA.lean',))
