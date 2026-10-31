"""WfCofC: t = 0 split of HCntPath0 (WfCofC5): G0 = bound at g = P_0(r); E0 = each edge c = P_0(d), d a strict
ancestor of r on the path: [fsD(o_A(d), k) <= o_N(d)] -> [fsD(o_A(c), k) <= o_N(c)] (records antecedent and result).
usage: CAP=.. nice -n 15 python3 probeY.py OUT.json NMAX PKL...
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
    def cnt(key, ok, A, n=0, c=None):
        S[key + (ok,)] += 1
        if not ok and (key not in EX or len(A) < len(EX[key][0])):
            EX[key] = (''.join('(%d,%d,%d)' % q for q in A), n, c)
    for pk in sys.argv[3:]:
        data = pickle.load(open(pk, 'rb'))
        if isinstance(data, dict): data = list(data)
        if len(data) > CAP: random.seed(11); data = random.sample(list(data), CAP)
        for A in data:
            A = tuple(tuple(c) for c in A)
            if len(A) < 2 or A[-1] == (0, 0, 0): continue
            try:
                if ttype(A) != 0: continue
                vA = val(A)
                if vA is None: continue
                p = path(vA)
                if p is None or p[0] != 'succ': continue
                x = len(A) - 1; r = badroot(A)
                Sl = [list(c) for c in A]
                g = trio.parent(Sl, 0, r)
                if g is None: continue
                evA = Y.Ev(list(A)); evA.value()
                oA = [Y.sf(evA.o(c)) for c in range(len(A))]
                path0 = []; h = g
                while h is not None:
                    path0.append(h); h = trio.parent(Sl, 0, h)
                for n in range(2, NMAX + 1):
                    k = n - 2
                    N = [tuple(q) for q in trio.expand([list(q) for q in A], n)]
                    ev = Y.Ev(N); ev.value()
                    B = {h: le(fsD(oA[h], natT(k)), Y.sf(ev.o(h))) for h in path0}
                    cnt(('G0', n), B[g], A, n, g)
                    for i in range(len(path0) - 1):
                        d, c = path0[i], path0[i + 1]
                        if B[d]: cnt(('E0', n), B[c], A, n, c)
                        else: S[('E0vac', n)] += 1
                    S[('mat', n)] += 1
            except RecursionError:
                S['rec'] += 1
    json.dump({'stats': {str(k): v for k, v in sorted(S.items(), key=str)},
               'ex': {str(k): v for k, v in EX.items()}}, open(out, 'w'), indent=1)
    for k, v in sorted(S.items(), key=str): print(k, v)
    for k, v in EX.items(): print('EX', k, v)
