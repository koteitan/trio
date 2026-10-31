"""WfCof: EvalFS split by the type t of the last column (0: row 1 = 0, 1: row 2 = 0, 2: row 2 > 0).

usage: nice -n 15 python3 fsprobe2.py OUT.json NMAX PKL...
Per A: def(n) = n - L(n), L(n) = max k with fs(vA, k) <= val(A[n]).
Reports, per (t, cof): max def over n >= 1 and over n >= 2, the minimal uniform c (all n >= c: def(n) <= c),
monotonicity val(A[n]) < val(A[n+1]) (n >= 1), and for zero last columns val(A.take x) + 1 = val(A).
"""
import sys, json, pickle, collections, random, os
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfCof')
from fsprobe import *

def ttype(A):
    c = A[-1]
    return 0 if c == (0, 0, 0) else (2 if c[2] > 0 else (1 if c[1] > 0 else 0)) if c != (0, 0, 0) else 'zero'

if __name__ == '__main__':
    out, NMAX = sys.argv[1], int(sys.argv[2])
    S = collections.Counter(); EX = {}
    for pk in sys.argv[3:]:
        data = pickle.load(open(pk, 'rb'))
        if isinstance(data, dict): data = list(data)
        CAP = int(os.environ.get('CAP', '150000'))
        if len(data) > CAP: random.seed(7); data = random.sample(list(data), CAP)
        for A in data:
            A = tuple(tuple(c) for c in A)
            if len(A) < 2: continue
            vA = val(A)
            if vA is None: S['noval'] += 1; continue
            t = 'zero' if A[-1] == (0, 0, 0) else ttype(A)
            c = cof(vA)[0]
            vs = []
            for n in range(NMAX + 1):
                N = [tuple(x) for x in trio.expand([list(x) for x in A], n)]
                vs.append(val(N))
            if any(v is None for v in vs): S['Nnoval'] += 1; continue
            if t == 'zero':
                S[('zero', c, app(vs[1], ONE) == vA)] += 1
                continue
            fk = [fs(vA, k) for k in range(NMAX + 3)]
            d = []
            for n in range(NMAX + 1):
                L = max([k for k in range(NMAX + 3) if le(fk[k], vs[n])], default=-1)
                d.append(n - L)
            cmin = min(cc for cc in range(0, NMAX + 1) if all(d[n] <= cc for n in range(cc, NMAX + 1)))
            S[('cmin', t, c, cmin)] += 1
            S[('maxdef_n>=2', t, c, max(d[2:]))] += 1
            mono = all(lt(vs[n], vs[n + 1]) for n in range(1, NMAX))
            S[('mono_n>=1', t, c, mono)] += 1
            k = ('cmin', t, c, cmin)
            if k not in EX or len(A) < len(EX[k]): EX[k] = A
            if not mono:
                k = ('nonmono', t)
                if k not in EX or len(A) < len(EX[k]): EX[k] = A
    json.dump({'stats': {str(k): v for k, v in sorted(S.items(), key=str)},
               'ex': {str(k): ''.join('(%d,%d,%d)' % x for x in v) for k, v in EX.items()}}, open(out, 'w'), indent=1)
    print(json.dumps({str(k): v for k, v in sorted(S.items(), key=str)}))
