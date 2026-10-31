"""WfCofL: the diagonal-type case (path(tA) = diag a b mu) with zeta_n = Y_n = sf(o_{A[n]}(x)).

usage: nice -n 15 python3 probe2.py OUT.json NMAX PKL...
  E   : fsD(tA, Y_n) <= val(A[n])                    (n >= 2)
  S   : gam(mu, b, n-2) <= Y_n                         (n >= 2)
  R1  : psi_mu(b[Y_n]) <= Y_{n+1}                      (n >= 2)  (then S follows by induction)
  R1b : psi_mu(b[Y_n]) <= Y_{n+1}                      (n = 1, Y_1 = sf(o_{A[1]}(r)) seed of the chain)
  SH  : Y_{n+1} == sf(o_{A[n]}(r))                     (copy shift)
  CH  : Y_{n+1} == fsD(sf(o_A(r)), Y_n)                (chain c_n = fsD(c_inf, c_{n-1}))
  CHle: psi_mu(b[Y_n]) <= fsD(sf(o_A(r)), Y_n)
  Also for the succ-type case: C0: fs(tA, n-2) <= val(A[n]) (the counting claim).
"""
import sys, json, pickle, collections, random, os
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfCofL')
from probe import *

if __name__ == '__main__':
    out, NMAX = sys.argv[1], int(sys.argv[2])
    S = collections.Counter(); EX = {}
    CAP = int(os.environ.get('CAP', '20000'))
    def ex(key, A, n):
        if key not in EX or len(A) < len(EX[key][0]): EX[key] = (''.join('(%d,%d,%d)' % c for c in A), n)
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
            p = path(vA)
            if r is None: S['noroot'] += 1; continue
            try:
                evA = Y.Ev(list(A)); evA.value(); cinf = Y.sf(evA.o(r))
            except RecursionError:
                continue
            Ys = {}; tNs = {}; Cs = {}
            ok = True
            for n in range(1, NMAX + 2):
                N = [tuple(c) for c in trio.expand([list(c) for c in A], n)]
                try:
                    ev = Y.Ev(N); tN = ev.value()
                except RecursionError:
                    tN = None
                if tN is None: ok = False; break
                tNs[n] = tN
                Cs[n] = Y.sf(ev.o(r)) if r < len(N) else None
                Ys[n] = Y.sf(ev.o(x)) if x < len(N) else None
            if not ok: S['Nnoval'] += 1; continue
            if p is None or p[0] == 'succ':
                for n in range(2, NMAX + 1):
                    c0 = le(fs(vA, n - 2), tNs[n]); S[('C0', t, 'none' if p is None else p[0], c0)] += 1
                    if not c0: ex(('C0', t), A, n)
                continue
            _, a, b, mu = p
            S[('mat', t)] += 1
            S[('CI', t, cinf == (mu, b, Z))] += 1
            if cinf != (mu, b, Z): ex(('CI', t), A, 0)
            for n in range(2, NMAX + 1):
                Yn = Ys[n]
                for nm, val_ in (('E', le(fsD(vA, Yn), tNs[n])), ('S', le(gam(mu, b, n - 2), Yn)),
                                 ('R1', le((mu, fs(b, Yn), Z), Ys[n + 1])),
                                 ('SH', Ys[n + 1] == Cs[n]),
                                 ('R1eq', (mu, fs(b, Yn), Z) == Ys[n + 1]),
                                 ('CH', Ys[n + 1] == fsD(cinf, Yn)),
                                 ('CHle', le((mu, fs(b, Yn), Z), fsD(cinf, Yn)))):
                    S[(nm, t, val_)] += 1
                    if not val_: ex((nm, t), A, n)
            # seed of the chain: Y_2 = c_1 = sf(o_{A[1]}(r))
            S[('SH1', t, Ys[2] == Cs[1])] += 1
            S[('R1b', t, le((mu, fs(b, Cs[1]), Z), Ys[2]))] += 1
            g1 = le(gam(mu, b, 1), Ys[2]); S[('S2slack', t, g1)] += 1
    json.dump({'stats': {str(k): v for k, v in sorted(S.items(), key=str)},
               'ex': {str(k): v for k, v in EX.items()}}, open(out, 'w'), indent=1)
    for k, v in sorted(S.items(), key=str): print(k, v)
    for k, v in EX.items(): print('EX', k, v)
