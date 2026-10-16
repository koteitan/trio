"""t = 0: the strong BumpAbsLo M r ρ versus the weak AbsWN M N r ρ σ (V3AbsW) for N = M[n], n = 2, 3.
AbsWN M N bnd ρ σ: ∀ i < bnd, e1 i ≠ 0, e2 i ≠ 0, ∀ q ∈ summands vOpt ρ (P_1 i), ¬ q < ω², ¬ q < bumpW N σ i,
  q < bumpW M ρ i → Lhd z q (bumpW M ρ i).      (exact Lhd, lhd_exact.py)
t = 0: x = |M| − 1, entry 1 x = 0, P_0 x = r (x ≠ (0,0,0)).  Only M < SRO.
Counters: strong (BumpAbsLo), strongByWchg (split by bumpW N i ≠ bumpW M i), weak (AbsWN),
weakD (AbsWN at i with v_N(i) ≠ v_M(i)), mono (bumpW (M.take x) i ≤ bumpW N i), WN=WT, absC (the drop-side
BumpAbsC premise ¬ q < bumpW (M.take x) i, with the Lhd verdict).
Usage: nice -n 15 python3 probe_abswn_t0.py [SET ...]   (4 workers; default: all ten sets)"""
import sys, pickle
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
from lhd_exact import lhd
from probe_inv3_prefix import Ctx, Z, ONE, lt
import trio as TR
SRO = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (2, 0, 0)]
W2 = (Z, (Z, Z, ONE), Z)


def summands(t):
    out = []
    while t:
        out.append((t[0], t[1], Z)); t = t[2]
    return out


def mstr(M): return ''.join('(%d,%d,%d)' % tuple(q) for q in M)


def go(M):
    M = [tuple(c) for c in M]
    cnt = Counter(); ex = []
    if not M < SRO or len(M) < 2: return cnt, ex
    x = len(M) - 1
    if M[x][1] != 0 or M[x] == (0, 0, 0): return cnt, ex
    C = Ctx(M)
    if not C.ok: return cnt, ex
    r = C.e.par(0, x)
    if r is None: return cnt, ex
    cnt['t0'] += 1
    CT = Ctx(M[:x])
    if not CT.ok: return cnt, ex
    for n in (2, 3):
        N = [tuple(c) for c in TR.expand([list(c) for c in M], n)]
        CN = Ctx(N)
        if not CN.ok:
            cnt['evalN_failed'] += 1; continue
        for i in range(r):
            if M[i][1] == 0 or M[i][2] == 0: continue
            p1 = C.e.par(1, i)
            V = C.v(p1) if p1 is not None else Z
            W = C.bumpW(i); WN = CN.bumpW(i); WT = CT.bumpW(i)
            mono = not lt(WN, WT)
            cnt[('mono', mono)] += 1
            cnt[('WN=WT', WN == WT)] += 1
            if WN != WT and len(ex) < 4: ex.append(('WNneWT', n, i, mstr(M)))
            if not mono and len(ex) < 10: ex.append(('mono', n, i, mstr(M)))
            # BumpAbsC route: summands not < WT
            chg = CN.v(i) != C.v(i)
            if WN != W:
                cnt['Wchg'] += 1; cnt[('Wchg.lt', lt(WN, W))] += 1
            for q in summands(V):
                if lt(q, W2) or not lt(q, W): continue
                ok = lhd(q, W)
                cnt[('strong', ok)] += 1
                cnt[('strongByWchg', WN != W, ok)] += 1
                if not lt(q, WT): cnt[('absC', ok)] += 1
                if lt(q, WN): continue
                cnt[('weak', ok)] += 1
                if chg: cnt[('weakD', ok)] += 1
                if not ok and len(ex) < 6: ex.append(('weak', n, i, chg, mstr(M)))
    return cnt, ex


if __name__ == '__main__':
    import json, os
    out = '/home/koteitan/proofs/trio/tmp/ytosk-handoff/results/drop/abswn_t0'
    os.makedirs(out, exist_ok=True)
    names = sys.argv[1:] or ['Cprime', 't0ext', 'd3s', 'deep2', 'deep3', 'ext1', 'ext1x', 't2ext', 'ext2', 'expP', 'std_a']
    for name in names:
        mats = pickle.load(open('/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets/%s.pkl' % name, 'rb'))
        tot = Counter(); exs = []
        with Pool(4) as p:
            for c, e in p.imap_unordered(go, mats, chunksize=200):
                tot.update(c)
                if len(exs) < 20: exs += e
        res = {str(k): v for k, v in sorted(tot.items(), key=lambda kv: str(kv[0]))}
        print(name, res, flush=True)
        for e in exs[:8]: print(' ', e, flush=True)
        open(os.path.join(out, name + '.json'), 'w').write(json.dumps({'counts': res, 'examples': exs[:20]}, indent=1))
