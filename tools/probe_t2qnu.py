"""t = 2, q != r, x - 1 upgrades (upg(x-1) = k): measure the hypotheses of T2QNU (V3T2Top) and the n <= 1 drop.

usage: python3 probe_t2qnu.py SEEDS.pkl [maxlen] [rounds]
  SEEDS.pkl: a list of standard matrices (e.g. the prefix closure C').  Matrices of the case are collected from
  the prefixes of M[2], M[3] and of their M[2], M[3]; then the set is grown by the same step from the prefixes of
  the found matrices.  Everything stays standard (expansions and prefixes of standard matrices).
Seeds SQU = {v(q), o(q), o(pq), v(x-1)}; checks p1, p1a, qsh, dv, os, vsh, the root drop of M.take x, that the
changed values of M.take x are in D, CL(pq) != [] and that o(pq) changes (seed1).
"""
import sys, pickle
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio, ytosk_eval as Y, ytosk_eval2 as Y2
from collections import Counter
from multiprocessing import Pool
MAXL = int(sys.argv[2]) if len(sys.argv) > 2 else 26

def kind(M):
    x = len(M) - 1
    if x < 1 or M[x] == (0, 0, 0) or M[x][2] == 0: return None
    e = Y2.Ev2(M)
    r = e.par(2, x); q = e.par(0, x)
    if r is None or q == r: return None
    return 'up' if e._upg[x - 1] is not None else 'nn'

def exps(M):
    out = []
    if not M or M[-1] == (0, 0, 0): return out
    for n in (2, 3):
        N = trio.expand(M, n)
        for j in range(len(M), min(len(N), MAXL) + 1): out.append(N[:j])
    return out

def grow(m):
    M = list(m); res = set()
    for j in range(2, len(M) + 1):
        for Q in exps(M[:j]):
            if kind(Q) == 'up': res.add(tuple(Q))
            for R in exps(Q):
                if kind(R) == 'up': res.add(tuple(R))
    return res

def counted(e, M, i, c): return M[c] != e.bump(i) and not (c in e.upgs and e.topped(c))

def deps(e, M, b, i):
    out = []
    if b == 'o':
        out.append(('v', i))
        for c in e.children[i]:
            if counted(e, M, i, c): out.append(('o', c))
    else:
        if M[i][1] == 0: return out
        p = e.par(1, i)
        if p is not None: out.append(('v', p))
        if M[i][2] == 0:
            u = e._upg[i]
            if u is not None: out.append(('v', u))
        else:
            for j in e.children[i]:
                if M[j] == e.bump(i):
                    for k in e.children[j]: out.append(('o', k))
    return out

def depS(e, M, seeds):
    D = set(seeds); ch = True
    while ch:
        ch = False
        for i in range(len(M)):
            for b in ('o', 'v'):
                if (b, i) not in D and any(d in D for d in deps(e, M, b, i)): D.add((b, i)); ch = True
    return D

def measure(M):
    c = Counter(); ex = {}
    def bad(k): c[k] += 1; ex.setdefault(k, M)
    M = list(M); x = len(M) - 1
    e = Y2.Ev2(M); vm = e.value()
    q = e.par(0, x); pq = e.par(0, q); a = x - 1
    S = {('v', q), ('o', q), ('o', pq), ('v', a)}
    D = depS(e, M, S)
    CL = lambda i: [d for d in e.children[i] if counted(e, M, i, d)]
    for t, i in (('p1', q), ('p1a', a)):
        m = e.par(1, i)
        if m is not None and ('v', m) in D: bad(t)
    chq = e.children[q]
    if len(chq) < 2 or chq[-1] != x or not e.children[chq[-2]]: bad('qsh.shape')
    else:
        d = chq[-2]
        if any(('o', f) in D for f in e.children[d][:-1]): bad('qsh.Kb')
        if any(('o', f) in D for dd in chq[:-2] for f in e.children[dd]): bad('qsh.Lb')
    for i in range(x):
        if ('v', i) in D and CL(i): bad('dv')
        if ('o', i) in D and ('o', i) not in S and ('v', i) not in D:
            cl = CL(i)
            if not cl or ('o', cl[-1]) not in D or any(('o', f) in D for f in cl[:-1]): bad('os')
        if ('v', i) in D and ('v', i) not in S:
            m = e.par(1, i)
            if m is not None and ('v', m) in D: bad('vsh.p')
            if M[i][2] != 0:
                ch = e.children[i]
                if not ch or M[ch[-1]] != e.bump(i) or not e.children[ch[-1]]: bad('vsh.shape'); continue
                j = ch[-1]
                if any(('o', f) in D for f in e.children[j][:-1]): bad('vsh.Kb')
                if any(('o', f) in D for dd in ch[:-1] for f in e.children[dd]): bad('vsh.Lb')
    T = Y2.Ev2(M[:x]); vt = T.value()
    if not Y.lt(vt, vm): bad('root')
    for i in range(x):
        if T.o(i) != e.o(i) and ('o', i) not in D: bad('chg.o')
        if T.v(i) != e.v(i) and ('v', i) not in D: bad('chg.v')
    if not CL(pq): bad('clpq')
    if T.o(pq) == e.o(pq): bad('seed1')
    c['total'] += 1
    return dict(c), ex

if __name__ == '__main__':
    seeds = pickle.load(open(sys.argv[1], 'rb'))
    rounds = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    found = set()
    with Pool(26) as p:
        for r in p.imap_unordered(grow, [m for m in seeds if len(m) <= 22], chunksize=50): found |= r
        for _ in range(rounds):
            new = set()
            for r in p.imap_unordered(grow, sorted(found), chunksize=1): new |= r
            if new <= found: break
            found |= new
        tot = Counter(); exs = {}
        for cc, ee in p.imap_unordered(measure, sorted(found), chunksize=20):
            tot.update(cc)
            for k, v in ee.items(): exs.setdefault(k, v)
    print(dict(tot))
    for k, M in exs.items(): print(k, ''.join('(%d,%d,%d)' % t for t in M))
