"""Measure the fields of SeedPFResV3 (V3SeedPFAll.lean) on all t = 2 source frames of the 86 input sets.
Only M (ρ) and T = M.take x (τ) are needed.  Infinite quantifiers over k are checked for k <= KMAX.
Configurations (t2_seed_frames_of): qr (q = r, no upgrade into x, CL M r = Lc ++ [x]), sv (q = r,
upg(x−1) = x), qn (q ≠ r, CL M r = Lc ++ [q]), C1 / C2 (q ≠ r, otherwise; upg(x−1) none / some)."""
import sys, json, collections
from multiprocessing import Pool
R = '/home/koteitan/proofs/trio'
sys.path.insert(0, R + '/tools'); sys.path.insert(0, R + '/tmp/codex')
import inv3v3_inputs_audit_20261101 as Aud
from probe_inv3_prefix import Y
from lhd_exact import lt, Z
from probe_fdsh import sh, shf, H

ONE = (Z, Z, Z)
KMAX = 6


def app(x, y):
    if not x: return y
    return (x[0], x[1], app(x[2], y))
from probe_inv3_prefix import sumN   # Lean sumN = foldl (fun a b => sf (add a b)) z
def summ(t):
    out = []
    while t: out.append((t[0], t[1], Z)); t = t[2]
    return out
def natT(k): return Z if k == 0 else (Z, Z, natT(k - 1))
def succ(t): return app(t, ONE)
def spa(a, S): return Aud.A.spa(a, S) if hasattr(Aud.A, 'spa') else __import__('probe_inv3_prefix').spa(a, S)
def step5(a, b, s, y, c):
    if lt(b, y) and lt((a, Z, Z), (s, y, c)): return H(s, y)
    return Y.add(b, (s, y, Z))
def shIt(V, V2, X, k):
    for _ in range(k): X = sh(V, V2, X)
    return X


def work(mats):
    cnt = collections.Counter(); ex = {}
    def bad(key, M):
        cnt[key + '.false'] += 1
        if key not in ex or len(M) < len(ex[key]): ex[key] = M
    for raw in mats:
        M = list(map(tuple, raw)); x = len(M) - 1
        if x < 1 or M[x][1] == 0 or M[x][2] == 0: continue
        try:
            C = Aud.A.ctx(M); T = Aud.A.ctx(M[:x])
            if not (C.ok and T.ok): cnt['unresolved'] += 1; continue
            r = C.e.par(2, x); q = C.e.par(0, x)
            if r is None or q is None: continue
            vr = C.v(r); clM = C.CL(r); clT = T.CL(r); tvr = T.v(r)
            X1 = spa(tvr, sumN([T.o(d) for d in clT]))
            if q == r:
                if C.upg(x - 1) == x:
                    cnt['sv.frames'] += 1
                    for k in range(KMAX + 1):
                        Yk = sh(vr, succ(vr), shIt(vr, succ(vr), X1, k))
                        if step5(vr, X1, succ(vr), Yk, Z) != Yk: bad('sv.rw', M); break
                elif all(C.upg(i) != x for i in range(len(M))) and clM and clM[-1] == x:
                    cnt['qr.frames'] += 1
                    Lc = clM[:-1]
                    if any(not lt(app(vr, natT(k)), C.v(x)) for k in range(4 * KMAX + 1)): bad('qr.ks', M)
                    B = spa(vr, sumN([C.o(d) for d in Lc]))
                    W1 = sh(tvr, succ(vr), X1)
                    if lt(B, W1): bad('qr.w1', M)
                else:
                    cnt['qeqr.other'] += 1
                continue
            S = Y.add(vr, Y.omega(sumN([ONE] + [C.bumpTerm(q, d) for d in C.ch(q) if d < x])))
            if clM and clM[-1] == q:
                cnt['qn.frames'] += 1
                B = spa(vr, sumN([C.o(d) for d in clM[:-1]]))
                if sh(vr, S, B) != B: bad('qn.sigmaB', M)
                if any(lt(g, (succ(S), Z, Z)) for g in summ(B)): bad('qn.Bc', M)
                sX, sB = summ(X1), summ(B)
                if not (len(sX) == len(sB) + 1 and sX[:-1] == sB and sX[-1][1] == Z):
                    bad('qn.base.form', M)
                else:
                    t = sX[-1][0]
                    for k in range(KMAX + 1):
                        if not lt(vr, t) or lt(shf(vr, S, t), succ(S)): bad('qn.base.k', M); break
                        t = shf(vr, S, t)
                continue
            if C.upg(x - 1) is not None:
                cnt['C2.frames'] += 1
                continue
            cnt['C1.frames'] += 1
            if clT:
                oc = T.o(clT[-1])
                if not (oc[2] == Z and lt(S, oc[0])): bad('C1.decP', M)
            if T.v(q) != S: bad('C1.vqP', M)
            for k in range(KMAX + 1):
                Yk = sh(vr, S, shIt(vr, S, X1, k))
                if step5(vr, X1, S, step5(S, Z, S, Yk, Z), Z) != Yk: bad('C1.rw', M); break
            for d in T.ch(r):
                if d < q and not T.counted(r, d) and not lt(S, T.v(d)): bad('C1.big', M); break
        except Exception as e:
            cnt['exception'] += 1
            if 'exception' not in ex: ex['exception'] = [M, repr(e)]
    return cnt, ex


if __name__ == '__main__':
    sets = json.loads(open(R + '/tmp/codex/inv3v3_inputs_sets_20261101.json').read())
    tot = collections.Counter(); exs = {}
    with Pool(4) as pool:
        for f in sets:
            try: ms = Aud.A.load(f)
            except Exception: tot['load_fail'] += 1; continue
            chunks = [ms[i:i + 2000] for i in range(0, len(ms), 2000)]
            for c, e in pool.imap_unordered(work, chunks):
                tot.update(c)
                for k, v in e.items():
                    if k not in exs: exs[k] = v
            print(f.split('/')[-1], json.dumps({k: v for k, v in tot.items()}), flush=True)
    print('FINAL', json.dumps(dict(tot)))
    print('EX', json.dumps(exs))
