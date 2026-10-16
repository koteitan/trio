"""Measure, with the exact Lhd (lhd_exact.py), on matrices strictly below SRO:
  * UpgAbsXW N x σ  (V3MainT1D, branch dropfix-wkx eb0cca69), at i = x − 1, for every W with add V W = v(k);
    split into: strong (UpgAbsX) holds / strong fails and the weak alternative holds / FAIL.
    upgx2 := strong fails ⇒ entry N 2 x ≠ 0.
  * the drop conclusion ∀ i < x, PO σ σ' i ∧ PV N σ σ' i  (V3DropMain on dropfix-wkx), σ' = value of N.take x.
Usage: nice -n 15 python3 newpv3.py SETNAME...   (4 workers)
"""
import sys, os, pickle, json, time
from collections import Counter
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
from lhd_exact import lhd, lhdE, comps, indices
from probe_inv3_prefix import Ctx, Z, ONE, lt, le, isOT
import ytosk_eval as Y

SRO = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (2, 0, 0)]
SETS = ('Cprime', 't0ext', 'd3s', 'deep2', 'deep3', 'ext1', 'ext1x', 't2ext', 'ext2', 'expP')
SETDIR = '/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets'
OUTDIR = '/home/koteitan/proofs/trio/tmp/ytosk-handoff/results/drop'
OM1 = (ONE, Z, Z)


def summands(t):
    out = []
    while t:
        out.append((t[0], t[1], Z)); t = t[2]
    return out


def sumL(l):
    t = Z
    for p in reversed(l): t = (p[0], p[1], t)
    return t


def CS(t): return all(lt(g, OM1) for g in comps(Z, t))


def WCS(a, w):
    """∀ u, ¬ a < u → ∀ g ∈ comps u w, g < Ω_1 ∨ ∃ d ∈ comps u a, g ≤ d.
    comps u · is constant between consecutive indices, so u ∈ indices(w) ∪ indices(a) ∪ {z, a} suffices."""
    us = {Z, a}; indices(w, us); indices(a, us)
    for u in us:
        if lt(a, u): continue
        ca = comps(u, a)
        mx = Z
        for d in ca:
            if lt(mx, d): mx = d
        for g in comps(u, w):
            if not (lt(g, OM1) or le(g, mx)): return False
    return True


def single(t): return bool(t) and not t[2] and isOT(t)


def WkVA(w1, w): return lt(w1, w) and le(ONE, w1) and isOT(w1)


def WkOA(t1, t):
    return bool(t1) and bool(t) and t1[1] == Z and t1[2] == Z and t[2] == Z and WkVA(t1[0], t[0])


def mstr(M): return ''.join('(%d,%d,%d)' % q for q in M)


def go(M):
    M = list(M)
    cnt = Counter(input=1); ex = []
    if not M < SRO:
        cnt['outside_SRO'] += 1; return cnt, ex
    if len(M) < 2:
        cnt['short'] += 1; return cnt, ex
    C = Ctx(M); T = Ctx(M[:-1]); x = len(M) - 1
    if not (C.ok and T.ok):
        cnt['eval_failed'] += 1; ex.append(('eval_failed', mstr(M))); return cnt, ex
    cnt['measured'] += 1
    upgt = set(k for k in (C.upg(j) for j in range(len(M))) if k is not None)

    def par0(i): return C.e.par(0, i)

    def vOpt(p): return C.v(p) if p is not None else Z

    def nbpar(i):
        p = par0(i)
        if p is None: return True
        g = par0(p)
        return g is None or M[p] != C.e.bump(g)

    def wcsp(i, w): return CS(w) or (WCS(vOpt(par0(i)), w) and nbpar(i) and i not in upgt)

    def Ws(i):
        """(V, [W]) with add V W = v(k), W ≠ z, for the upgrade i → k; None if no upgrade."""
        k = C.upg(i)
        if k is None: return None
        V = vOpt(C.e.par(1, i)); vk = C.v(k); sk = summands(vk)
        return V, [sumL(sk[j:]) for j in range(len(sk)) if Y.add(V, sumL(sk[j:])) == vk]

    def strong(V, W): return all(lhd(r, W) for r in summands(V) if lt(r, W))

    # UpgAbsXW at i = x − 1
    i = x - 1
    r = Ws(i)
    upgbad = False
    if r is not None:
        V, WL = r
        for W in WL:
            if strong(V, W):
                cnt['UA.strong'] += 1; continue
            upgbad = True
            cnt[('UA.strongFails', 't', M[x][2])] += 1
            if M[x][2] == 0:
                cnt['upgx2.failures'] += 1; ex.append(('upgx2', mstr(M)))
            if wcsp(i, Y.add(V, ONE)) and nbpar(i) and M[x][2] != 0:
                cnt['UA.weak'] += 1
            else:
                cnt['UAW.failures'] += 1; ex.append(('UAW', mstr(M)))

    def cntx(i):
        cc = [c for c in C.ch(i) if C.counted(i, c)]
        if not cc: return True
        return all(c == x for c in cc) and nbpar(i) and (i == x - 1 and upgbad)

    for i in range(x):
        v, v1, o, o1 = C.v(i), T.v(i), C.o(i), T.o(i)
        # PV
        if v1 == v or lhdE(v1, v):
            kv = 'lhd'
        elif WkVA(v1, v) and wcsp(i, v1) and cntx(i):
            kv = 'weak' if not [c for c in C.ch(i) if C.counted(i, c)] else 'weakX'
        else:
            kv = 'FAIL'
        if not isOT(v1): kv = 'FAIL'
        if v1 != v: cnt['PV.' + kv] += 1
        if kv == 'FAIL':
            cnt['PV.failures'] += 1; ex.append(('PV', i, mstr(M)))
        # PO
        if o1 == o or lhdE(o1, o):
            ko = 'lhd'
        elif WkOA(o1, o) and (o[1] == Z or not lhdE(v1, v)):
            ko = 'weak' if o[1] == Z else 'weakX'
        else:
            ko = 'FAIL'
        if not single(o1): ko = 'FAIL'
        if o1 != o: cnt['PO.' + ko] += 1
        if ko == 'FAIL':
            cnt['PO.failures'] += 1; ex.append(('PO', i, mstr(M)))
    return cnt, ex[:3]


if __name__ == '__main__':
    out = {}
    os.makedirs(OUTDIR, exist_ok=True)
    names = sys.argv[1:] or SETS
    for name in names:
        t0 = time.time()
        mats = pickle.load(open(os.path.join(SETDIR, name + '.pkl'), 'rb'))
        tot = Counter(); exs = []
        with Pool(4) as p:
            for c, e in p.imap_unordered(go, mats, chunksize=200):
                tot.update(c)
                if len(exs) < 20: exs += e
        res = {str(k): v for k, v in sorted(tot.items(), key=lambda kv: str(kv[0]))}
        print(name, round(time.time() - t0), res, flush=True)
        for e in exs[:6]: print('  EX', e, flush=True)
        out[name] = {'counts': res, 'examples': exs[:20]}
        json.dump(out, open(os.path.join(OUTDIR, 'newpv3_%s.json' % '_'.join(names)), 'w'), indent=1)
