"""TP1LeafG and TP1WLeafG (V3TP1CutG.lean) on every frame of N, below SRO.

Lean (N, σ):  ∀ i < |N|, ∀ L c R, CL N i = L ++ c :: R, σ.o c = ψ_s(y), B := stB σ i L ≠ 0,
  B < y, ψ_{v(i)}(0) < ψ_s(y), (split y Ω_{s+1}).2 = 0, OHole y:
  TP1LeafG : ∀ k, CPairG s B y s k → ¬isSucc k → OHole k → s < k → s < fsD k (ψ_{holeLev y}(1))
  TP1WLeafG (also cof y = ω):
     (∀ t' k, CPairG s B y t' k → isSucc k → t' < k → ψ_{t'}(0) < 1)  -- i.e. no such pair
   ∧ (∀ k, CPairG s B y s k → ¬isSucc k → OHole k → s < k → s < fsD k 1)
stB σ i L = spArg (v i) z (sumN (L.map o))  (probe: spa(v(i), sumN(o of L))).
CPairG / HPairG are enumerated structurally (pairs()), constructors top/sub/arg/rest.
The probe is run on N = M (the matrices of a set, or the derived set of prefixes M.take x).
"""
import sys, os, pickle, json, time
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
from probe_inv3_prefix import (Ctx, Z, ONE, lt, le, fsD, ohole, holelev, cof, isSucc, split, succ,
                               spa, sumN)

SRO = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (2, 0, 0)]


def hpairs(t, x):
    """All (t', k) with HPairG s t x t' k (s is not used by the constructors)."""
    out = []
    if not t or not x: return out
    if t[1] == Z and t[2] == Z and x[1] == Z and x[2] == Z:
        out.append((t[0], x[0]))                                   # top
        if not isSucc(x[0]): out += hpairs(t[0], x[0])             # sub
    if t[2] == Z and x[2] == Z and t[0] == x[0]:
        out += hpairs(t[1], x[1])                                  # arg
    if t[0] == x[0] and t[1] == x[1]:
        out += hpairs(t[2], x[2])                                  # rest
    return out


def cpairs(B, y):
    """All (t', k) with CPairG s B y t' k."""
    out = []
    if not B or not y: return out
    if B[1] == Z and B[2] == Z and y[1] == Z and y[2] == Z:
        out.append((B[0], y[0]))                                   # top
        if not isSucc(y[0]): out += hpairs(B[0], y[0])             # sub
    if B[2] == Z and y[2] == Z and B[0] == y[0]:
        out += hpairs(B[1], y[1])                                  # arg
    if B[0] == y[0] and B[1] == y[1]:
        out += cpairs(B[2], y[2])                                  # rest
    return out


def mstr(M): return ''.join('(%d,%d,%d)' % q for q in M)


def measure(matrix):
    M = list(matrix)
    cnt = Counter(input=1); ex = {}
    if not M < SRO:
        cnt['outside_SRO'] += 1; return cnt, ex
    C = Ctx(M)
    if not C.ok:
        cnt['eval_failed'] += 1; ex['eval_failed'] = mstr(M); return cnt, ex
    cnt['measured'] += 1

    def note(f, ok, **info):
        cnt[f + '.cases'] += 1
        if not ok:
            cnt[f + '.failures'] += 1
            ex.setdefault(f, dict(matrix=mstr(M), **info))

    for i in range(len(M)):
        vi = C.v(i); cl = C.CL(i)
        for idx, c in enumerate(cl):
            o = C.o(c)
            if not o or o[2] != Z: continue
            s, y, _ = o
            B = spa(vi, sumN([C.o(d) for d in cl[:idx]]))
            if B == Z or not lt(B, y) or not lt((vi, Z, Z), (s, y, Z)): continue
            if split(y, (succ(s), Z, Z))[1] != Z or not ohole(y): continue
            cnt['frames'] += 1
            P = cpairs(B, y)
            eta = (holelev(y), ONE, Z)
            w = cof(y)[0] == 'omega'
            for (t1, k) in P:
                if t1 == s and not isSucc(k) and ohole(k) and lt(s, k):
                    note('TP1LeafG', lt(s, fsD(k, eta)), i=i, c=c)
                    if w: note('TP1WLeafG.lim', lt(s, fsD(k, ONE)), i=i, c=c)
                if w and isSucc(k) and lt(t1, k):
                    note('TP1WLeafG.succ', lt((t1, Z, Z), ONE), i=i, c=c)
    return cnt, ex


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('sets', nargs='+')
    ap.add_argument('--data', default='/home/koteitan/proofs/trio/tmp/ytosk-handoff/sets')
    ap.add_argument('--output', required=True)
    a = ap.parse_args()
    os.makedirs(a.output, exist_ok=True)
    with Pool(4) as p:
        for name in a.sets:
            t0 = time.time()
            mats = pickle.load(open(os.path.join(a.data, name + '.pkl'), 'rb'))
            tot = Counter(); exs = {}
            for c, e in p.imap_unordered(measure, mats, chunksize=200):
                tot.update(c)
                for k, v in e.items(): exs.setdefault(k, v)
            rep = {'set': name, 'data': a.data, 'counts': dict(tot), 'examples': exs,
                   'seconds': round(time.time() - t0)}
            open(os.path.join(a.output, name + '.json'), 'w').write(json.dumps(rep, indent=1))
            print(json.dumps(rep), flush=True)
