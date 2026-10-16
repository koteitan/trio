"""Candidate generalisation of the drop lemma's weak branch (2026-10-17, drop).
WCSP2 M ρ i w := CS w ∨ (WCS (vOpt ρ (P_0 i)) w ∧ WCS (vOpt ρ (P_1 i)) w)   (no NBPar, no "not an upgrade target").
Measured on matrices strictly below SRO, x = |M| − 1, σ = value of M, σ' = value of M.take x (exact Lhd):
  F1  PV2 at every i < x with v' ⋬ v:  WkVA v' v ∧ WCSP2 i v' ∧ CntX i            (CntX as in probe_newpv3)
  F2  imp10 at every column i: WCS (vOpt (P_0 i)) (vOpt (P_1 i));  F2u the same at the upgrade sources i
  F3  for a weakly changed k < x whose parent j is a bump child of i:  WCSP2 i v'(k), and the row-1 relation
      e1(k) vs e1(i) (counter F3.e1.<lt|eq|gt>)
  F4  BumpWeakSrc2: BumpWeakSrc (V3BumpDrop) with its last conjunct WCSP replaced by WCSP2
  F0  the old PV (WCSP) for reference
  F5  WeakCS: every weakly changed i < x has CS v'(i) ∨ WCS (vOpt (P_0 i)) v'(i)
  F6  the shape part of BumpWeakSrc only (children i = [j], first child of j is k)
  F7  PV with WCSP := CS ∨ WCS (vOpt (P_0 i)) (no NBPar, no upgrade-target condition): WkVA ∧ that ∧ CntX
Usage: nice -n 15 python3 probe_pv2.py [SET ...]   (4 workers; default all ten sets)"""
import sys, os, pickle, json, time
from collections import Counter
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import probe_newpv3 as P
from lhd_exact import lhdE

OUTDIR = '/home/koteitan/proofs/trio/tmp/ytosk-handoff/results/drop/pv2'


def go(M):
    M = list(M)
    cnt = Counter(input=1); ex = []
    if not M < P.SRO or len(M) < 2:
        return cnt, ex
    C = P.Ctx(M); T = P.Ctx(M[:-1]); x = len(M) - 1
    if not (C.ok and T.ok):
        cnt['eval_failed'] += 1; return cnt, ex
    cnt['measured'] += 1
    n = len(M)
    upgt = set(k for k in (C.upg(j) for j in range(n)) if k is not None)
    par0 = lambda j: C.e.par(0, j)
    par1 = lambda j: C.e.par(1, j)
    vOpt = lambda p: C.v(p) if p is not None else P.Z

    def nbpar(j):
        p = par0(j)
        if p is None: return True
        g = par0(p)
        return g is None or M[p] != C.e.bump(g)

    def wcsp(j, w): return P.CS(w) or (P.WCS(vOpt(par0(j)), w) and nbpar(j) and j not in upgt)

    def wcsp2(j, w): return P.CS(w) or (P.WCS(vOpt(par0(j)), w) and P.WCS(vOpt(par1(j)), w))

    def note(f, ok, *info):
        cnt[f + '.cases'] += 1
        if not ok:
            cnt[f + '.failures'] += 1
            if len(ex) < 12: ex.append((f,) + info + (P.mstr(M),))

    # UpgBad / CntX as in probe_newpv3
    i1 = x - 1
    upgbad = False
    k1 = C.upg(i1)
    if k1 is not None:
        V = vOpt(par1(i1)); vk = C.v(k1); sk = P.summands(vk)
        for W in [P.sumL(sk[j:]) for j in range(len(sk)) if P.Y.add(V, P.sumL(sk[j:])) == vk]:
            if not all(P.lhd(r, W) for r in P.summands(V) if P.lt(r, W)):
                upgbad = True

    def cntx(j):
        cc = [c for c in C.ch(j) if C.counted(j, c)]
        if not cc: return True
        return all(c == x for c in cc) and nbpar(j) and (j == x - 1 and upgbad)

    for i in range(n):
        if par0(i) is not None and par1(i) is not None:
            ok = P.WCS(vOpt(par0(i)), vOpt(par1(i)))
            note('F2', ok, i)
            if C.upg(i) is not None:
                note('F2u', ok, i)
    weak = {}
    for i in range(x):
        v, v1 = C.v(i), T.v(i)
        if v1 == v or lhdE(v1, v): continue
        wk = P.WkVA(v1, v) and P.isOT(v1)
        weak[i] = v1
        note('F0', wk and wcsp(i, v1) and cntx(i), i)
        note('F1', wk and wcsp2(i, v1) and cntx(i), i)
        cs0 = P.CS(v1) or P.WCS(vOpt(par0(i)), v1)
        note('F5', cs0, i)
        note('F7', wk and cs0 and cntx(i), i)
    for k, v1 in weak.items():
        j = par0(k)
        if j is None: continue
        i = par0(j)
        if i is None or M[j] != C.e.bump(i) or M[i][1] == 0 or M[i][2] == 0: continue
        rel = 'lt' if M[k][1] < M[i][1] else ('eq' if M[k][1] == M[i][1] else 'gt')
        cnt['F3.e1.' + rel] += 1
        note('F3', wcsp2(i, v1), k, i)
    # F4: BumpWeakSrc2
    for i in range(n):
        if M[i][1] == 0 or M[i][2] == 0: continue
        for j in C.ch(i):
            if M[j] != C.e.bump(i): continue
            for k in C.ch(j):
                o = C.o(k)
                if not (o and o[1] == P.Z and o[2] == P.Z and o[0] != P.Z): continue
                fire = False
                if k == x and C.ch(j) == [x] and not lhdE(T.v(i), C.v(i)): fire = True
                if k < x and T.o(k) != C.o(k) and not lhdE(T.v(k), C.v(k)): fire = True
                if not fire: continue
                shape = C.ch(i) == [j] and C.ch(j)[:1] == [k]
                note('F4', shape and wcsp2(i, vOpt(par1(i))), i, j, k)
                note('F6', shape, i, j, k)
    return cnt, ex


if __name__ == '__main__':
    os.makedirs(OUTDIR, exist_ok=True)
    for name in sys.argv[1:] or P.SETS:
        t0 = time.time()
        mats = pickle.load(open(os.path.join(P.SETDIR, name + '.pkl'), 'rb'))
        tot = Counter(); exs = []
        with Pool(4) as p:
            for c, e in p.imap_unordered(go, mats, chunksize=200):
                tot.update(c)
                if len(exs) < 24: exs += e
        res = dict(sorted(tot.items()))
        print(name, round(time.time() - t0), res, flush=True)
        for e in exs[:8]: print('  EX', e, flush=True)
        json.dump({'counts': res, 'examples': exs[:24]}, open(os.path.join(OUTDIR, name + '.json'), 'w'), indent=1)
