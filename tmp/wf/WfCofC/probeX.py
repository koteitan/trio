"""WfCofC: measure the residuals of WfCofC (HCntPath0, the t = 2 count, HCID pieces).

usage: CAP=.. nice -n 15 python3 probeX.py OUT.json NMAX PKL...
x = |A|-1, r = bad root, Rt = last root (last (0,0,0) column), path(t) as Lean omega_path.
 t = 0, succ type:   P0: Rt < r -> fsD(o_A(Rt), k) <= o_{A[k+2]}(Rt);  R0: Rt = r (root case, proved in Lean)
 t = 2, succ type:   R2: roots(A[n]) = roots(A), values of roots < Rt unchanged; C2: fsD(o_A(Rt), k) <= o_N(Rt)
                     V2: fsD(v_A(x), k) <= v_N(last column of N); VL: path(v_A(x)) = path(tA)
                     VP: for every row-1 ancestor c of x (c >= Rt): fsD(v_A(c), k) <= v_N(c) when path(v_A(c)) is succ
 t = 1, diag type:   CI: o_A(r) = psi_mu(b);  DL: path(o_A(r)) = ('diag', mu, b, mu)
                     DT: path(o_A(c)) = path(tA) for every row-0 ancestor c of x with Rt <= c <= r
 any t, succ type with t = 1: S1 count
"""
import sys, json, pickle, collections, random, os
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfCofL')
from probe import *

def natT(k):
    t = Z
    for _ in range(k): t = (Z, Z, t)
    return t

if __name__ == '__main__':
    out, NMAX = sys.argv[1], int(sys.argv[2])
    S = collections.Counter(); EX = {}
    CAP = int(os.environ.get('CAP', '1000'))
    def ex(key, A, n, c):
        if key not in EX or len(A) < len(EX[key][0]): EX[key] = (''.join('(%d,%d,%d)' % q for q in A), n, c)
    def cnt(key, ok, A, n=0, c=None):
        S[key + (ok,)] += 1
        if not ok: ex(key, A, n, c)
    for pk in sys.argv[3:]:
        data = pickle.load(open(pk, 'rb'))
        if isinstance(data, dict): data = list(data)
        if len(data) > CAP: random.seed(11); data = random.sample(list(data), CAP)
        for A in data:
            A = tuple(tuple(c) for c in A)
            if len(A) < 2 or A[-1] == (0, 0, 0): continue
            try:
                vA = val(A)
                if vA is None: continue
                p = path(vA)
                if p is None: continue
                t = ttype(A); x = len(A) - 1; r = badroot(A)
                Sl = [list(c) for c in A]
                evA = Y.Ev(list(A)); evA.value()
                oA = [Y.sf(evA.o(c)) for c in range(len(A))]
                vv = [Y.sf(evA.v(c)) for c in range(len(A))]
            except RecursionError:
                S['rec'] += 1; continue
            Rt = max(c for c in range(x + 1) if A[c] == (0, 0, 0))
            anc0 = []; h = x
            while h is not None:
                anc0.append(h); h = trio.parent(Sl, 0, h)
            S[('mat', t, p[0])] += 1
            if p[0] == 'diag':
                a, b, mu = p[1], p[2], p[3]
                cnt(('CI', t), oA[r] == (mu, b, Z), A)
                cnt(('DL', t), path(oA[r]) == ('diag', mu, b, mu), A)
                for c in anc0:
                    if Rt <= c <= r:
                        pc = path(oA[c]); kind = 'r' if c == r else ('Rt' if c == Rt else 'mid')
                        cnt(('DT', t, kind), pc == p, A, 0, c)
                        cnt(('DB', t, kind), pc is not None and pc[0] == 'diag' and pc[2:] == p[2:], A, 0, c)
                continue
            if t == 2:
                cnt(('VL', t), path(vv[x]) == p, A)
                anc1 = []; h = x
                while h is not None and h >= Rt:
                    anc1.append(h); h = trio.parent(Sl, 1, h) if A[h][1] > 0 else None
            for n in range(2, NMAX + 1):
                k = n - 2
                try:
                    N = [tuple(q) for q in trio.expand([list(q) for q in A], n)]
                    ev = Y.Ev(N); tN = ev.value()
                    if tN is None: S['Nnoval'] += 1; continue
                    oN = lambda c: Y.sf(ev.o(c))
                    vN = lambda c: Y.sf(ev.v(c))
                    if t == 0:
                        if Rt < r: cnt(('P0', n), le(fsD(oA[Rt], natT(k)), oN(Rt)), A, n, Rt)
                        else: S[('R0', n)] += 1
                        cnt(('F0', n), le(fsD(vA, natT(k)), tN), A, n)
                    elif t == 2:
                        rN = [c for c in range(len(N)) if N[c] == (0, 0, 0)]
                        rA = [c for c in range(len(A)) if A[c] == (0, 0, 0)]
                        cnt(('R2roots', n), rN == rA, A, n)
                        cnt(('R2pre', n), all(oN(c) == oA[c] for c in rA if c < Rt), A, n)
                        cnt(('C2', n), le(fsD(oA[Rt], natT(k)), oN(Rt)), A, n, Rt)
                        cnt(('V2', n), le(fsD(vv[x], natT(k)), vN(len(N) - 1)), A, n)
                        for c in anc1:
                            if c == x: continue
                            pc = path(vv[c])
                            if pc is not None and pc[0] == 'succ':
                                cnt(('VP', n), le(fsD(vv[c], natT(k)), vN(c)), A, n, c)
                        cnt(('F2', n), le(fsD(vA, natT(k)), tN), A, n)
                    else:
                        S[('S1', n)] += 1
                except RecursionError:
                    S['rec'] += 1
    json.dump({'stats': {str(k): v for k, v in sorted(S.items(), key=str)},
               'ex': {str(k): v for k, v in EX.items()}}, open(out, 'w'), indent=1)
    for k, v in sorted(S.items(), key=str): print(k, v)
    for k, v in EX.items(): print('EX', k, v)
