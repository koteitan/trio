"""WfCofL: split EvalFSNZ 2 into an engine bound and a seed bound, with a concrete index zeta.

usage: nice -n 15 python3 probe.py OUT.json NMAX PKL...
For A (std, nonzero last column, value defined), n = 2..NMAX, k = n - 2, x = len(A) - 1, r = bad root:
  candidates zeta: Y = o_{A[n]}(x), C = o_{A[n]}(r)
  E(zeta): fsD(tA, zeta) <= val(A[n])        (engine side)
  S(zeta): IdxLB(tA, k, zeta)                 (seed side; Lean WfCofL1.IdxLB)
  F: fs(tA, k) <= val(A[n])                   (EvalFSNZ 2 itself)
Counts per (type t of last column, path kind of tA, candidate, E, S).
"""
import sys, json, pickle, collections, random, os
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfCof')
from fsprobe import *
import trio

def fsD(t, eta):
    if not t: return Z
    if t[2]: return (t[0], t[1], fsD(t[2], eta))
    a, b, _ = t
    if not b:
        if not a: return Z
        if isSucc(a): return eta
        return (fsD(a, eta), Z, Z)
    if isSucc(b): return mulT((a, init(b), Z), cnt(eta))
    c = cof(b)
    if c[0] == 'big': return (a, fs(b, eta), Z)
    return (a, fsD(b, eta), Z)

def path(t):
    """Lean omega_path: ('diag', a, b, mu) / ('succ', a, b) / None."""
    if not t: return None
    if t[2]: return path(t[2])
    a, b, _ = t
    if not b:
        if not a or isSucc(a): return None
        return path(a)
    if isSucc(b): return ('succ', a, b)
    c = cof(b)
    if c[0] == 'big':
        return None if lt(c[1], a) else ('diag', a, b, c[1])
    if c[0] == 'omega': return path(b)
    return None

def gam(mu, b, k):
    g = Z
    for _ in range(k): g = (mu, fs(b, g), Z)
    return g

def idxlb(tA, k, zeta):
    p = path(tA)
    if p is None: return True
    if p[0] == 'succ': return k <= cnt(zeta)
    return le(gam(p[3], p[2], k), zeta)

def ttype(A):
    c = A[-1]
    return 2 if c[2] > 0 else (1 if c[1] > 0 else 0)

def badroot(A):
    S = [list(c) for c in A]
    x = len(S) - 1
    t = max(y for y in range(3) if S[x][y] > 0)
    return trio.parent(S, t, x)

if __name__ == '__main__':
    out, NMAX = sys.argv[1], int(sys.argv[2])
    S = collections.Counter(); EX = {}
    CAP = int(os.environ.get('CAP', '20000'))
    for pk in sys.argv[3:]:
        data = pickle.load(open(pk, 'rb'))
        if isinstance(data, dict): data = list(data)
        if len(data) > CAP: random.seed(7); data = random.sample(list(data), CAP)
        for A in data:
            A = tuple(tuple(c) for c in A)
            if len(A) < 2 or A[-1] == (0, 0, 0): continue
            vA = val(A)
            if vA is None: continue
            t = ttype(A); x = len(A) - 1; r = badroot(A)
            p = path(vA); pk_ = 'none' if p is None else p[0]
            S[('mat', t, pk_)] += 1
            for n in range(2, NMAX + 1):
                N = [tuple(c) for c in trio.expand([list(c) for c in A], n)]
                try:
                    ev = Y.Ev(N); tN = ev.value()
                except RecursionError:
                    tN = None
                if tN is None: S['Nnoval'] += 1; continue
                k = n - 2
                F = le(fs(vA, k), tN)
                for name, col in (('Y', x), ('C', r)):
                    if col is None or col >= len(N): continue
                    zeta = Y.sf(ev.o(col))
                    E = le(fsD(vA, zeta), tN); Sd = idxlb(vA, k, zeta)
                    key = (t, pk_, name, E, Sd)
                    S[key] += 1
                    if not (E and Sd):
                        kk = (t, pk_, name, E, Sd)
                        if kk not in EX or len(A) < len(EX[kk][0]): EX[kk] = (''.join('(%d,%d,%d)' % c for c in A), n)
                S[(t, pk_, 'F', F)] += 1
    json.dump({'stats': {str(k): v for k, v in sorted(S.items(), key=str)},
               'ex': {str(k): v for k, v in EX.items()}}, open(out, 'w'), indent=1)
    for k, v in sorted(S.items(), key=str): print(k, v)
    for k, v in EX.items(): print('EX', k, v)
