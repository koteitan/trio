"""WfCofH: locate the successor-argument node (HCountS, t = 0, 2).

usage: nice -n 15 python3 probeC.py OUT.json NMAX PKL...
For A with path(tA) = ('succ', a, b):
  LOC  : the columns c with sf(o_A(c)) == psi_a(b); relation to x, r (bad root), q = P_0(x)
  CP   : for every row-0 ancestor h of the node column c (h <= c), n = 2..NMAX, k = n - 2:
         fsD(sf(o_A(h)), k) <= sf(o_{A[n]}(h))      (count path bound; at h = the last root it gives HCountS
         up to the root sum)
  HOLE : number of columns c' of A[n] with sf(o_{A[n]}(c')) == psi_a(init b)
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
            p = path(vA)
            if p is None or p[0] != 'succ': continue
            t = ttype(A); x = len(A) - 1; r = badroot(A)
            Sl = [list(c) for c in A]
            q = trio.parent(Sl, 0, x)
            node = (p[1], p[2], Z)
            try:
                evA = Y.Ev(list(A)); evA.value()
                oA = [Y.sf(evA.o(c)) for c in range(len(A))]
            except RecursionError:
                continue
            locs = [c for c in range(len(A)) if oA[c] == node]
            def subs(t, acc):
                while t:
                    acc.add((t[0], t[1], Z)); subs(t[0], acc); subs(t[1], acc); t = t[2]
                return acc
            try:
                vA_ = [Y.sf(evA.v(c)) for c in range(len(A))]
            except Exception:
                vA_ = None
            if not locs:
                where = 'none'
                P1x = trio.parent(Sl, 1, x) if A[x][1] > 0 else None
                cs = [c for c in range(len(A)) if node in subs(oA[c], set())]
                if cs:
                    c = max(cs)
                    where = 'o-sub:' + '/'.join(nm for nm, cc in (('x', x), ('r', r), ('q', q), ('P1x', P1x)) if cc == c) if c in (x, r, q, P1x) else 'o-sub:other'
                    if A[x][2] > 0 or where == 'o-sub:other': ex(('WHEREc', t, where), A, 0, c)
                if where == 'none' and vA_ is not None:
                    for c in range(len(A)):
                        if node in subs(vA_[c], set()):
                            where = 'v-sub:' + ('x' if c == x else ('r' if c == r else 'other')); break
                S[('WHERE', t, where)] += 1
                if where.startswith('v-sub:other') or where == 'none': ex(('WHERE', t, where), A, 0, None)
            rel = tuple(sorted(set(('r' if c == r else '') + ('q' if c == q else '') or 'other' for c in locs))) or ('none',)
            S[('LOC', t, rel)] += 1
            if 'other' in rel or rel == ('none',): ex(('LOC', t, rel), A, 0, locs)
            if not locs: continue
            c0 = max(locs)
            anc = []; h = c0
            while h is not None:
                anc.append(h); h = trio.parent(Sl, 0, h)
            hole = (p[1], init(p[2]), Z)
            for n in range(2, NMAX + 1):
                N = [tuple(q_) for q_ in trio.expand([list(q_) for q_ in A], n)]
                try:
                    ev = Y.Ev(N); tN = ev.value()
                    if tN is None: S['Nnoval'] += 1; continue
                    for h in anc:
                        if h >= len(N): S[('CPout', t)] += 1; continue
                        ok = le(fsD(oA[h], natT(n - 2)), Y.sf(ev.o(h)))
                        key = ('CP', t, 'root' if A[h] == (0, 0, 0) else ('node' if h == c0 else 'mid'), ok)
                        S[key] += 1
                        if not ok: ex(key, A, n, h)
                    nh = sum(1 for c in range(len(N)) if Y.sf(ev.o(c)) == hole)
                    S[('HOLE', t, n, min(nh, n + 1))] += 1
                except RecursionError:
                    S['rec'] += 1
    json.dump({'stats': {str(k): v for k, v in sorted(S.items(), key=str)},
               'ex': {str(k): v for k, v in EX.items()}}, open(out, 'w'), indent=1)
    for k, v in sorted(S.items(), key=str): print(k, v)
    for k, v in EX.items(): print('EX', k, v)
