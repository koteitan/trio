"""WfCofH: measure the engine path bound HEngPath and HDiagT1.

usage: nice -n 15 python3 probeH.py OUT.json NMAX PKL...
  T1   : path(tA) = diag  =>  type t of the last column is 1        (HDiagT1)
  P    : for every row-0 ancestor c of x with c <= r (bad root), n = 2..NMAX:
         fsD(sf(o_A(c)), Y_n) <= sf(o_{A[n]}(c)),  Y_n = sf(o_{A[n]}(x))     (HEngPath)
  P1   : the same for all t = 1 matrices (not only the diagonal type)
"""
import sys, json, pickle, collections, random, os
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfCofL')
from probe import *

if __name__ == '__main__':
    out, NMAX = sys.argv[1], int(sys.argv[2])
    S = collections.Counter(); EX = {}
    CAP = int(os.environ.get('CAP', '2000'))
    def ex(key, A, n, c):
        if key not in EX or len(A) < len(EX[key][0]): EX[key] = (''.join('(%d,%d,%d)' % q for q in A), n, c)
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
            p = path(vA); kind = 'none' if p is None else p[0]
            S[('T1', kind, t)] += 1
            if kind == 'diag' and t != 1: ex(('T1',), A, 0, None)
            if r is None or t != 1: continue
            Sl = [list(c) for c in A]
            anc = []; c = x
            while c is not None:
                if c <= r: anc.append(c)
                c = trio.parent(Sl, 0, c)
            try:
                evA = Y.Ev(list(A)); evA.value()
                oA = {c: Y.sf(evA.o(c)) for c in anc}
            except RecursionError:
                continue
            for n in range(2, NMAX + 1):
                N = [tuple(q) for q in trio.expand([list(q) for q in A], n)]
                try:
                    ev = Y.Ev(N); tN = ev.value()
                    if tN is None: S['Nnoval'] += 1; continue
                    Yn = Y.sf(ev.o(x))
                    for c in anc:
                        ok = le(fsD(oA[c], Yn), Y.sf(ev.o(c)))
                        key = ('P' if kind == 'diag' else 'P1', 'root' if A[c] == (0, 0, 0) else ('r' if c == r else 'mid'), ok)
                        S[key] += 1
                        if not ok: ex(key, A, n, c)
                except RecursionError:
                    S['rec'] += 1
    json.dump({'stats': {str(k): v for k, v in sorted(S.items(), key=str)},
               'ex': {str(k): v for k, v in EX.items()}}, open(out, 'w'), indent=1)
    for k, v in sorted(S.items(), key=str): print(k, v)
    for k, v in EX.items(): print('EX', k, v)
