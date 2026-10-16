"""Exact measurement of the drop residuals (DropResR / Res3R / HardArg) on matrices strictly below SRO.

Lean source: the drop worktree Ytosk/lean/Ytosk (file:line below).  N = M (the matrix), x = |M| - 1,
sigma = Ctx(M) (the value of M), sigma' = Ctx(M[:-1]) (the value of M.take x).  The Lean statements quantify
over `drop1 M x rk` / any `sigma'` with `Cons (M.take x) sigma'`; by uniqueness of Cons these agree with
Ctx(M[:-1]) on every column < x, and only columns < x are read (checked per field below).

Field (counter prefix)  Lean definition                      correspondence notes
----------------------  -----------------------------------  ------------------------------------------------
HardArg                 V3DropStrong.lean:139 HardArg        one case = (i < x, cs = last of CL(M.take x) i) with
                                                             o'(cs)=psi s y' 0, o(cs)=psi s y 0 (same s), v(i)<s,
                                                             both triggers, hi(y') < hi(y); conclusion over
                                                             comps (v i) y' (fixed level, finite).
VSmallNew               V3DropMain.lean:32 VSmallNew         case = (i, cs) with v'(cs) != v(cs); fixed level v(i).
BumpWeakSrc             V3BumpDrop.lean BumpWeakSrc (2026-10-17: = BumpWeakShapeSrc ∧ WeakCS; the counter BumpWeakSrc
                        is the shape part, WeakCS the other)  case = (i, j, k) with e1,e2 != 0, j bump child, k
                                                             child of j, o(k)=psi w 0 0 (w != 0), and the
                                                             disjunction (k=x & ch j=[x] & not v'(i) |>= v(i)) or
                                                             (k<x & o'(k)!=o(k) & not v'(k) |>= v(k)).  WCSP
                                                             (V3DropMain.lean:58), WCS/CS (V3DropRel.lean:60/17),
                                                             NBPar (V3DropMain.lean:52) translated as newpv3.py.
BumpAbsC                V3BumpDrop.lean:588 BumpAbsC         case = (i, r): e1,e2 != 0, collapse guard, guard
                                                             (StrongG(:571) or XParNB(:566) or v(x)=0), r summand
                                                             of v(P_1 i), not r < W' (W' = bumpW (M.take x)
                                                             sigma' i), r < W (= bumpW M sigma i); conclusion
                                                             exact Lhd z r W.  StrongG's exists sigma' = Ctx(M[:-1]).
                                                             BRelS = V3BumpDrop.lean:95 (Closed z X' = comps z X'
                                                             all <= X', since not z<u forces u = z).
BumpAbsS (info)         V3BumpDrop.lean:576 BumpAbsS         the strong form with x = |M|-1 regardless of srow
                                                             (sanity field only; Res3R uses it through AbsSR.S).
AbsSR.S                 V3BumpDrop.lean:608 AbsSR, conj 1    srow M x = 2 (TRIO.srow, lean/Trio.lean:81:
                                                             entry 2 x > 0) -> BumpAbsS M x sigma.
AbsSR.Lo                V3BumpDrop.lean:608 AbsSR, conj 2    r = P_0(x), entry M 1 x = 0 -> BumpAbsLo M r sigma
                                                             (V3BumpDrop.lean:601): i < r, e1,e2 != 0, s summand
                                                             of v(P_1 i), not s < w^2, s < W -> Lhd z s W.
SeedR                   V3DropRH.lean:101 SeedR              case = (r, a'-class): P_1 x = P_0 x = r, sf(v'(r)) <
                                                             v(r), a' <= v(r), isOT(psi a' B' 0) with
                                                             B' = qrB + Om(v(r)+1), qrB = V3QRFinal2.lean:14
                                                             (preState over children of r before x, cnt of M,
                                                             nzs).  Conclusion: comps a' o'(r) all < qrB ++ o'(r).
VSmallNewR              V3DropR.lean:35 VSmallNewR           case = (i, cs) with v'(cs) != v(cs), o(cs) = psi s y 0
                                                             triggering, not (hi(y) = B and v(i) < v'(cs));
                                                             conclusion over all u <= v(i) (finite reduction).
ShadowC                 V3DropR.lean:45 ShadowC              case = (i, cs): o(cs)=psi s y 0 triggers,
                                                             o'(cs)=psi s' y' 0 does not, B not a summand-prefix
                                                             of hi(y); conclusion over all u <= v(i).

hi(y) := (split y Om(succ s)).1 ; B := spArg (v i) 0 (sumN (Lc.map o)) with Lc the counted children of
M.take x before cs, mapped by sigma (as in Lean).  `<` = lt = true, `<=` = lt or = (Order.lean:13-14).

Finite reductions of the infinite quantifiers (all exact):
 * `forall u, not v(i) < u -> forall g in comps u X, P(g, comps u v(i))` (VSmallNewR, ShadowC; WCS):
   comps u t depends only on which indices v of t satisfy v < u.  Let S = {0, v(i)} u indices(X) u
   indices(v(i)), sorted u_0 = 0 < u_1 < ... .  For u in (u_{k-1}, u_k] the truth of v < u equals that of
   v < u_k for every v in S, so comps u X and comps u v(i) are those at u_k; v(i) in S makes every class
   lie wholly below or above v(i).  Evaluating at the u in S with u <= v(i) is therefore exact.
 * SeedR `forall a', not v(r) < a' -> isOT(psi a' B' 0) -> forall g in comps a' o'(r), g < ...`:
   classes {0}, (u_{k-1}, u_k] for S = {0} u indices(o'(r)); comps a' o'(r) is constant on a class.  On a
   class the premise set is {a' <= v(r)} n {isOT a'} n {isOT B'} n {comps a' B' all < B'}; the last is
   upward closed in a' (comps u t shrinks as u grows), so the class has an admissible a' iff
   m = min(u_k, v(r)) lies in the class and m satisfies the premise, provided isOT m.  m is isOT when o'(r)
   and v(r) are standard (indices of a standard term are standard); if isOT m fails the class is counted
   as `SeedR.inexact` (never seen in tests).
 * Lhd: exact decision (lhd_exact.py).
Usage: nice -n 15 python3 probe_dropres.py [SET ...] --output DIR [--data DIR] [--limit N] [--workers 1..4]
"""
import argparse
import json
import os
import pickle
import sys
import time
from collections import Counter
from multiprocessing import Pool
from pathlib import Path

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
from lhd_exact import lhd, lhdE, comps, indices                       # noqa: E402
from probe_inv3_prefix import Ctx, Z, ONE, lt, le, isOT, split, succ, app, sumN, spa  # noqa: E402
import ytosk_eval as Y                                                # noqa: E402

SRO = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (2, 0, 0)]
SETS = ('Cprime', 't0ext', 'd3s', 'deep2', 'deep3', 'ext1', 'ext1x', 't2ext', 'ext2', 'expP', 'std_a')
FIELDS = ('HardArg', 'VSmallNew', 'BumpWeakSrc', 'WeakCS', 'BumpAbsC', 'BumpAbsS', 'AbsSR.S', 'AbsSR.Lo', 'SeedR',
          'VSmallNewR', 'ShadowC')
OM1 = (ONE, Z, Z)
E0 = (Z, OM1, Z)
TWO = (Z, Z, ONE)
W2 = (Z, TWO, Z)          # psi z two z = omega^2


def Om(t): return (t, Z, Z)


def summands(t):
    out = []
    while t:
        out.append((t[0], t[1], Z)); t = t[2]
    return out


def H(s, y):
    """SP.lean:17."""
    t = Y.cut(Y.add(s, ONE), y)
    return Y.add(t, Y.sub((s, y, Z), (s, t, Z)))


def hi(s, y): return split(y, Om(succ(s)))[0]


def CS(t): return all(lt(g, OM1) for g in comps(Z, t))


def tmax(l):
    m = Z
    for g in l:
        if lt(m, g): m = g
    return m


def levels(a, *ts):
    """{0, a} u indices(a) u indices(t) : the exact breakpoints of `forall u, not a < u -> ...`."""
    us = {Z, a}
    indices(a, us)
    for t in ts: indices(t, us)
    return [u for u in us if not lt(a, u)]


def WCS(a, w):
    """V3DropRel.lean:60: forall u, not a < u -> forall g in comps u w, g < Om 1 or exists d in comps u a, g <= d."""
    for u in levels(a, w):
        mx = tmax(comps(u, a))
        for g in comps(u, w):
            if not (lt(g, OM1) or le(g, mx)): return False
    return True


def closedZ(X): return all(le(g, X) for g in comps(Z, X))


def BRelS(X1, X):
    """V3BumpDrop.lean:95."""
    E = lhdE(X1, X)
    if E and lt(X, E0): return True
    if E and not lt(X1, E0) and X1 and X and X1[0] == X[0]: return True
    if E and lt(X1, E0) and closedZ(X1) and not lt(X, E0) and X and X[0] == Z: return True
    if X1 and X and X1[1] == Z and X1[2] == Z and lhdE(X1[0], X[0]) and le(ONE, X1[0]): return True
    return False


def is_prefix(B, h):
    """exists R, h = app B R  <=>  summands(B) is a prefix of summands(h)."""
    while B:
        if not h or B[0] != h[0] or B[1] != h[1]: return False
        B, h = B[2], h[2]
    return True


def mstr(M): return ''.join('(%d,%d,%d)' % tuple(q) for q in M)


def measure(matrix):
    """Exact DropResR/Res3R/HardArg fields of one matrix (see module docstring)."""
    M = [tuple(c) for c in matrix]
    cnt = Counter(input=1)
    ex = {}
    if not M < SRO:
        cnt['outside_SRO'] += 1; return cnt, ex
    if len(M) < 2:
        cnt['short'] += 1; return cnt, ex
    t0 = time.process_time()
    C = Ctx(M); T = Ctx(M[:-1]); x = len(M) - 1; n = len(M)
    if not (C.ok and T.ok):
        cnt['eval_failed'] += 1; ex['eval_failed'] = {'matrix': mstr(M)}; return cnt, ex
    cnt['measured'] += 1

    def note(f, ok, **info):
        cnt[f + '.cases'] += 1
        if not ok:
            cnt[f + '.failures'] += 1
            if f not in ex:
                ex[f] = dict(matrix=mstr(M), **{k: (Y.tstr(v) if isinstance(v, tuple) else v)
                                                 for k, v in info.items()})

    def e(r, i): return M[i][r] if 0 <= i < n else 0
    def par0(i): return C.e.par(0, i)
    def par1(i): return C.e.par(1, i)
    def vOpt(p): return C.v(p) if p is not None else Z
    def chM(i): return C.ch(i) if 0 <= i < n else []
    def chT(i): return T.ch(i) if 0 <= i < x else []
    def bumpM(i): return (e(0, i) + 1, e(1, i), 1)
    upgt = set(k for k in (C.upg(j) for j in range(n)) if k is not None)

    def nbpar(i):
        p = par0(i)
        if p is None: return True
        g = par0(p)
        return g is None or M[p] != bumpM(g)

    def wcsp(i, w): return CS(w) or (WCS(vOpt(par0(i)), w) and nbpar(i) and i not in upgt)

    def bumpW_M(i):
        return Y.omega(sumN([ONE] + [Y.omega(sumN([C.o(k) for k in chM(j)])) if M[j] == bumpM(i) else Z
                                     for j in chM(i)]))

    def bumpW_T(i):
        # bump (M.take x) i = bump M i for i < x; for i >= x the take has no children of i.
        return Y.omega(sumN([ONE] + [Y.omega(sumN([T.o(k) for k in chT(j)])) if M[j] == bumpM(i) else Z
                                     for j in chT(i)]))

    def CLT(i): return [d for d in chT(i) if T.counted(i, d)]

    # XParNB M x (V3BumpDrop.lean:566)
    q = par0(x)
    xparnb = True
    if q is not None:
        g = par0(q)
        if g is not None and M[q] == bumpM(g): xparnb = False

    def strongG(i):
        """V3BumpDrop.lean:571, sigma' = Ctx(M[:-1])."""
        for jl in chT(i):
            if M[jl] != bumpM(i): continue
            if not BRelS(sumN([T.o(k) for k in chT(jl)]), sumN([C.o(k) for k in chM(jl)])): return False
        return True

    # ---- frames of M.take x: HardArg, VSmallNew, VSmallNewR, ShadowC ----
    for i in range(x):
        cl = CLT(i)
        if not cl: continue
        cs = cl[-1]; Lc = cl[:-1]
        vi = C.v(i)
        B = spa(vi, sumN([C.o(d) for d in Lc]))
        oc, oc1 = C.o(cs), T.o(cs)
        vc, vc1 = C.v(cs), T.v(cs)

        def trig(s, y): return lt(B, y) and lt(Om(vi), (s, y, Z))
        single = bool(oc) and oc[2] == Z
        single1 = bool(oc1) and oc1[2] == Z
        # HardArg
        if single and single1 and oc[0] == oc1[0]:
            s, y, y1 = oc[0], oc[1], oc1[1]
            if lt(vi, s) and trig(s, y1) and trig(s, y) and lt(hi(s, y1), hi(s, y)):
                h = H(s, y1)
                bad = [g for g in comps(vi, y1) if not le(g, h)]
                note('HardArg', not bad, i=i, cs=cs, s=s, y1=y1, y=y, g=bad[0] if bad else Z)
        if vc1 != vc:
            # VSmallNew
            bad = [g for g in comps(vi, vc1) if not (le(g, Om(vc1)) or le(g, B))]
            note('VSmallNew', not bad, i=i, cs=cs, v1=vc1, g=bad[0] if bad else Z)
            # VSmallNewR
            if single:
                s, y = oc[0], oc[1]
                if trig(s, y) and not (hi(s, y) == B and lt(vi, vc1)):
                    badu = None
                    for u in levels(vi, vc1):
                        cu = comps(u, vi)
                        for g in comps(u, vc1):
                            if not (le(g, Om(vc1)) or le(g, B) or any(le(g, d) for d in cu)):
                                badu = (u, g); break
                        if badu: break
                    note('VSmallNewR', badu is None, i=i, cs=cs, v1=vc1,
                         u=badu[0] if badu else Z, g=badu[1] if badu else Z)
        # ShadowC
        if single and single1:
            s, y, s1, y1 = oc[0], oc[1], oc1[0], oc1[1]
            if trig(s, y) and not trig(s1, y1) and not is_prefix(B, hi(s, y)):
                X = app(B, (s1, y1, Z))
                badu = None
                for u in levels(vi, X):
                    cu = comps(u, vi)
                    for g in comps(u, X):
                        if not (lt(g, X) or any(le(g, d) for d in cu)):
                            badu = (u, g); break
                    if badu: break
                note('ShadowC', badu is None, i=i, cs=cs, X=X, u=badu[0] if badu else Z,
                     g=badu[1] if badu else Z)

    # ---- bump columns: BumpWeakSrc, BumpAbsC, BumpAbsS ----
    vx_zero = C.v(x) == Z
    for i in range(n):
        if e(1, i) == 0 or e(2, i) == 0: continue
        V = vOpt(par1(i))
        bj = [j for j in chM(i) if M[j] == bumpM(i)]
        for j in bj:
            for k in chM(j):
                ok_ = C.o(k)
                if not (ok_ and ok_[0] != Z and ok_[1] == Z and ok_[2] == Z): continue
                a1 = k == x and chM(j) == [x] and not lhdE(T.v(i), C.v(i))
                a2 = k < x and T.o(k) != ok_ and not lhdE(T.v(k), C.v(k))
                if not (a1 or a2): continue
                okc = chM(i) == [j] and chM(j)[:1] == [k]       # BumpWeakShapeSrc (2026-10-17)
                note('BumpWeakSrc', okc, i=i, j=j, k=k)
    # WeakCS (2026-10-17, the second half of BumpWeakSrc): every weakly changed v' has CS or WCS (v(P_0 i))
    for i in range(x):
        if T.v(i) == C.v(i) or lhdE(T.v(i), C.v(i)): continue
        note('WeakCS', CS(T.v(i)) or WCS(vOpt(par0(i)), T.v(i)), i=i)
        if not all(chM(j) != [x] or vx_zero for j in bj): continue
        W = bumpW_M(i)
        guard = xparnb or vx_zero or strongG(i)
        if guard:
            W1 = bumpW_T(i)
            for r in summands(V):
                if not lt(r, W1) and lt(r, W):
                    note('BumpAbsC', lhd(r, W), i=i, r=r, W=W, W1=W1)
            for r in summands(V):
                if not lt(r, W2) and lt(r, W):
                    ok = lhd(r, W)
                    note('BumpAbsS', ok, i=i, r=r, W=W)
                    if e(2, x) > 0: note('AbsSR.S', ok, i=i, r=r, W=W)
    # AbsSR conj 2: BumpAbsLo M r (r = P_0 x, entry M 1 x = 0)
    rr = par0(x)
    if rr is not None and e(1, x) == 0:
        for i in range(rr):
            if e(1, i) == 0 or e(2, i) == 0: continue
            W = bumpW_M(i)
            for s in summands(vOpt(par1(i))):
                if not lt(s, W2) and lt(s, W):
                    note('AbsSR.Lo', lhd(s, W), i=i, r=rr, s=s, W=W)

    # ---- SeedR ----
    r = par1(x)
    if r is not None and par0(x) == r:
        vr = C.v(r); o1 = T.o(r)
        if lt(Y.sf(T.v(r)), vr):
            L = [d for d in chM(r) if d < x]
            qrB = spa(vr, sumN([t for t in (C.o(d) if C.counted(r, d) else Z for d in L) if t != Z]))
            B1 = app(qrB, Om(succ(vr)))
            rhs = app(qrB, o1)
            if isOT(B1):
                S = {Z}; indices(o1, S)
                S = sorted(S, key=lambda t: _Key(t))
                for k, uk in enumerate(S):
                    m = uk if (k == 0 or le(uk, vr)) else vr
                    if k > 0 and not lt(S[k - 1], m): continue          # class has no a' <= v(r)
                    if not isOT(m):
                        cnt['SeedR.inexact'] += 1; continue
                    if not all(lt(g, B1) for g in comps(m, B1)): continue
                    bad = [g for g in comps(m, o1) if not lt(g, rhs)]
                    note('SeedR', not bad, r=r, a=m, qrB=qrB, o1=o1, g=bad[0] if bad else Z)
    cnt['cpu_ms'] += int(1000 * (time.process_time() - t0))
    return cnt, ex


class _Key:
    def __init__(s, t): s.t = t
    def __lt__(s, o): return lt(s.t, o.t)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('sets', nargs='*', default=list(SETS))
    ap.add_argument('--data', type=Path, default=Path('/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets'))
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--workers', type=int, choices=range(1, 5), default=4)
    ap.add_argument('--limit', type=int, default=0, help='first N matrices only (0 = all)')
    ap.add_argument('--stride', type=int, default=1, help='take every k-th matrix')
    a = ap.parse_args()
    a.output.mkdir(parents=True, exist_ok=True)
    with Pool(a.workers) as pool:
        for name in a.sets:
            t0 = time.monotonic()
            mats = pickle.load(open(a.data / (name + '.pkl'), 'rb'))[::a.stride]
            if a.limit: mats = mats[:a.limit]
            tot, exs = Counter(), {}
            for c, e in pool.imap_unordered(measure, mats, chunksize=50):
                tot.update(c)
                for k, v in e.items(): exs.setdefault(k, v)
            rep = {'set': name, 'n': len(mats), 'seconds': round(time.monotonic() - t0, 2),
                   'counts': dict(sorted(tot.items())), 'examples': exs, 'fields': FIELDS}
            (a.output / (name + '.json')).write_text(json.dumps(rep, ensure_ascii=False, indent=1) + '\n')
            print(json.dumps(rep, ensure_ascii=False), flush=True)


if __name__ == '__main__':
    main()
