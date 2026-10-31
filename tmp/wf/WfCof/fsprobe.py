"""WfCof: compare eval(A[n]) with the fundamental sequence eval(A)[k] (Lean FS.fs, eta = natT k).

usage: nice -n 15 python3 fsprobe.py OUT.json NMAX PKL...
For each A (std, len >= 2, value defined) and n = 0..NMAX:
  vN = eval(A[n]);  L(n) = max k <= KMAX with fs(vA, k) <= vN;  eq(n) = {k : fs(vA,k) == vN}
Reports histograms of L(n) - n, of the exact-equality shift, cof(vA), and failures of vN < vA.
"""
import sys, json, pickle, collections, functools
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
sys.setrecursionlimit(100000)
import ytosk_eval as Y, trio
Z, ONE, lt = Y.Z, Y.ONE, Y.lt
Y.sf = functools.lru_cache(maxsize=1 << 18)(Y.sf)

def app(x, y):
    if not x: return y
    return (x[0], x[1], app(x[2], y))
def last(t):
    while t and t[2]: t = t[2]
    return (t[0], t[1], Z) if t else Z
def init(t):
    if not t or not t[2]: return Z
    return (t[0], t[1], init(t[2]))
def isSucc(t): return last(t) == ONE
def cof(t):
    if not t: return ('zero',)
    if t[2]: return cof(t[2])
    a, b, _ = t
    if not b:
        if not a: return ('succ',)
        if isSucc(a): return ('big', init(a))
        return cof(a)
    if isSucc(b): return ('omega',)
    c = cof(b)
    if c[0] == 'big': return c if lt(c[1], a) else ('omega',)
    return c
def mulT(t, n):
    r = Z
    for _ in range(n): r = app(t, r)
    return r
def natT(n): return mulT(ONE, n)
def fs(t, k):
    """Lean fs t (natT k) when k is int; eta a term in the big branches."""
    if not t: return Z
    if t[2]: return (t[0], t[1], fs(t[2], k))
    a, b, _ = t
    if not b:
        if not a: return Z
        if isSucc(a): return natT(k) if isinstance(k, int) else k
        return (fs(a, k), Z, Z)
    if isSucc(b): return mulT((a, init(b), Z), k if isinstance(k, int) else cnt(k))
    c = cof(b)
    if c[0] == 'big':
        mu = c[1]
        if lt(mu, a): return (a, fs(b, k), Z)
        g = Z
        for _ in range(k if isinstance(k, int) else cnt(k)): g = (mu, fs(b, g), Z)
        return (a, fs(b, g), Z)
    return (a, fs(b, k), Z)
def cnt(t):
    n = 0
    while t: n += 1; t = t[2]
    return n
def le(x, y): return x == y or lt(x, y)
def val(M):
    try: return Y.Ev(list(M)).value()
    except RecursionError: return None

KMAX = 12
def one(A, NMAX):
    vA = val(A)
    if vA is None: return None
    rows = []
    for n in range(NMAX + 1):
        N = trio.expand([list(c) for c in A], n)
        vN = val([tuple(c) for c in N])
        if vN is None: rows.append(None); continue
        fk = [fs(vA, k) for k in range(KMAX + 1)]
        L = max([k for k in range(KMAX + 1) if le(fk[k], vN)], default=-1)
        eq = [k for k in range(KMAX + 1) if fk[k] == vN]
        rows.append((L, eq, lt(vN, vA)))
    return (cof(vA)[0], rows)

if __name__ == '__main__':
    out, NMAX = sys.argv[1], int(sys.argv[2])
    H = collections.Counter(); EQ = collections.Counter(); C = collections.Counter(); bad = []
    minshift = collections.Counter(); ex = {}; DEF = collections.Counter()
    for pk in sys.argv[3:]:
        data = pickle.load(open(pk, 'rb'))
        if isinstance(data, dict): data = list(data)
        import random, os
        CAP = int(os.environ.get('CAP', '150000'))
        if len(data) > CAP: random.seed(7); data = random.sample(list(data), CAP); C['sampled:' + os.path.basename(pk)] = CAP
        for A in data:
            A = tuple(tuple(c) for c in A)
            if len(A) < 2: continue
            r = one(A, NMAX)
            if r is None: C['noval'] += 1; continue
            c, rows = r
            C[c] += 1
            ms = None
            for n, row in enumerate(rows):
                if row is None: C['Nnoval'] += 1; continue
                L, eq, dec = row
                if not dec: bad.append((A, n))
                H[(c, n, L - n if L < KMAX else 'top')] += 1
                EQ[(c, n, tuple(e - n for e in eq))] += 1
                if n >= 1 and L < KMAX:
                    ms = L - n if ms is None else min(ms, L - n)
                key = ('L-n', c, n, L - n)
                if key not in ex: ex[key] = (A, n)
            dd = [n - row[0] for n, row in enumerate(rows) if n >= 1 and row is not None and row[0] < KMAX]
            md = max(dd, default=None)
            minshift[(c, ms)] += 1
            DEF[(c, md)] += 1
            mono = all(rows[n] is not None and rows[n+1] is not None and (rows[n][0] < rows[n+1][0] or rows[n][0] >= KMAX) for n in range(1, len(rows)-1))
            if c == 'omega' and not mono: C['L_not_strict_mono_n>=1'] += 1
            mk = ('maxdef', c, md)
            if mk not in ex: ex[mk] = A
    json.dump({'cof': dict(C), 'hist': {str(k): v for k, v in sorted(H.items(), key=str)},
               'eq': {str(k): v for k, v in sorted(EQ.items(), key=str)},
               'minshift_n>=1': {str(k): v for k, v in sorted(minshift.items(), key=str)},
               'maxdef_n>=1': {str(k): v for k, v in sorted(DEF.items(), key=str)}, 'notdec': [str(b) for b in bad[:50]], 'n_notdec': len(bad),
               'ex': {str(k): str(v) for k, v in ex.items()}}, open(out, 'w'), indent=1)
    print(json.dumps({'cof': dict(C), 'maxdef': {str(k): v for k, v in sorted(DEF.items(), key=str)}, 'minshift': {str(k): v for k, v in sorted(minshift.items(), key=str)}, 'n_notdec': len(bad)}))
