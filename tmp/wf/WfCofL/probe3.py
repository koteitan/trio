"""WfCofL: the counting case (no diagonal point; measured: always SuccAt a b, b successor).

usage: nice -n 15 python3 probe3.py OUT.json NMAX PKL...
fsD(tA, m) = frame(psi_a(init b) * m). m_n = max m <= MM with fsD(tA, natT m) <= val(A[n]).
  C0   : m_n >= n - 2                       (n >= 2; = HCount)
  REC  : m_{n+1} >= m_n + 1                 (n >= 2)
  REC1 : m_{n+1} >= m_n + 1                 (n = 1)
  BASE : m_2 >= 0  (fsD(tA, 0) <= val(A[2]))
  EXm  : exact equality val(A[n]) == fsD(tA, natT m) for some m; histogram of m - n
  M1   : m_1 (value of A[1]) histogram
"""
import sys, json, pickle, collections, random, os
sys.path.insert(0, '/home/koteitan/proofs/trio/tmp/wf/WfCofL')
from probe import *

MM = 14
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
            p = path(vA)
            if p is not None and p[0] == 'diag': continue
            t = ttype(A)
            if p is None: S[('nopath', t)] += 1; ex(('nopath', t), A, 0); continue
            S[('mat', t)] += 1
            fk = [fsD(vA, natT(m)) for m in range(MM + 1)]
            ms = {}
            for n in range(1, NMAX + 2):
                N = [tuple(c) for c in trio.expand([list(c) for c in A], n)]
                tN = val(N)
                if tN is None: ms = None; break
                ms[n] = max([m for m in range(MM + 1) if le(fk[m], tN)], default=-1)
                eq = [m for m in range(MM + 1) if fk[m] == tN]
                S[('EXm', t, n, eq[0] - n if eq else None)] += 1
            if ms is None: S['Nnoval'] += 1; continue
            S[('M1', t, ms[1])] += 1
            S[('BASE', t, ms[2] >= 0)] += 1
            S[('REC1', t, ms[2] >= ms[1] + 1)] += 1
            for n in range(2, NMAX + 1):
                c0 = ms[n] >= n - 2; S[('C0', t, c0)] += 1
                if not c0: ex(('C0', t), A, n)
                rec = ms[n + 1] >= ms[n] + 1 or ms[n] >= MM
                S[('REC', t, rec)] += 1
                if not rec: ex(('REC', t), A, n)
    json.dump({'stats': {str(k): v for k, v in sorted(S.items(), key=str)},
               'ex': {str(k): v for k, v in EX.items()}}, open(out, 'w'), indent=1)
    for k, v in sorted(S.items(), key=str): print(k, v)
    for k, v in EX.items(): print('EX', k, v)
