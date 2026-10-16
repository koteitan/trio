"""UpgAbsXW at i = x − 1 (V3MainT1D on branch drop-wkx2) with the third conjunct of the weak alternative
`entry M 2 x ≠ 0` (current) or `entry M 1 x ≠ 0` (proposed, t ≠ 0), exact Lhd (lhd_exact.py).
WCSP is the 2026-10-17 form CS w ∨ WCS (vOpt (P_0 i)) w (V3DropMain on drop-wkx2); NBPar as probe_newpv3.
Counters: UA.strong, UA.strongFails.<row1 x>.<row2 x>, UA.strongFails.t1.qr=<P_1 x = P_0 x>.rxm1=<P_1 x = x − 1>, UAW2.failures (current), UAW1.failures (proposed),
weakCore.failures (WCSP ∧ SmallSelf (V + 1) ∧ NBPar fails; SmallSelf.failures separately).  Only M < SRO.
Usage: nice -n 15 python3 probe_uaw1.py [SET ...]   (4 workers; default all ten sets)"""
import sys, os, pickle, json, time
from collections import Counter
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import probe_newpv3 as P
import ytosk_eval as Y

OUTDIR = '/home/koteitan/proofs/trio/tmp/ytosk-handoff/results/drop/uaw1'


def go(M):
    M = list(M)
    cnt = Counter(input=1); ex = []
    if not M < P.SRO or len(M) < 2:
        return cnt, ex
    C = P.Ctx(M); x = len(M) - 1
    if not C.ok:
        cnt['eval_failed'] += 1; return cnt, ex
    cnt['measured'] += 1
    i = x - 1
    k = C.upg(i)
    if k is None:
        return cnt, ex
    upgt = set(t for t in (C.upg(j) for j in range(len(M))) if t is not None)

    def par0(j): return C.e.par(0, j)

    def vOpt(p): return C.v(p) if p is not None else P.Z

    def nbpar(j):
        p = par0(j)
        if p is None: return True
        g = par0(p)
        return g is None or M[p] != C.e.bump(g)

    def wcsp(j, w): return P.CS(w) or P.WCS(vOpt(par0(j)), w)   # WCSP (V3DropMain, 2026-10-17)

    V = vOpt(C.e.par(1, i)); vk = C.v(k); sk = P.summands(vk)
    WL = [P.sumL(sk[j:]) for j in range(len(sk)) if Y.add(V, P.sumL(sk[j:])) == vk]
    for W in WL:
        if all(P.lhd(r, W) for r in P.summands(V) if P.lt(r, W)):
            cnt['UA.strong'] += 1; continue
        cnt['UA.strongFails.%d.%d' % (int(M[x][1] != 0), int(M[x][2] != 0))] += 1
        if M[x][1] != 0 and M[x][2] == 0:
            r1, q0 = C.e.par(1, x), C.e.par(0, x)
            cnt['UA.strongFails.t1.qr=%d.rxm1=%d' % (int(r1 == q0), int(r1 == i))] += 1
        V1 = Y.add(V, P.ONE)
        ss = all(P.lt(g, (V1, P.Z, P.Z)) for g in P.comps(P.Z, V1))   # SmallSelf (V + 1)
        if not ss:
            cnt['SmallSelf.failures'] += 1; ex.append(('SmallSelf', P.mstr(M)))
        core = wcsp(i, V1) and ss and nbpar(i)
        if not core:
            cnt['weakCore.failures'] += 1; ex.append(('core', P.mstr(M)))
        if not (core and M[x][2] != 0):
            cnt['UAW2.failures'] += 1
        if not (core and M[x][1] != 0):
            cnt['UAW1.failures'] += 1; ex.append(('UAW1', P.mstr(M)))
        elif M[x][2] == 0 and len(ex) < 3:
            ex.append(('t1weak', P.mstr(M)))
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
                if len(exs) < 20: exs += e
        res = dict(sorted(tot.items()))
        print(name, round(time.time() - t0), res, flush=True)
        for e in exs[:6]: print('  EX', e, flush=True)
        json.dump({'counts': res, 'examples': exs[:20]}, open(os.path.join(OUTDIR, name + '.json'), 'w'), indent=1)
