# -*- coding: utf-8 -*-
"""Step 1 split for the Ytosk route: the value R(M) before the standard form (sf).

  python3 tools/probe_raw.py [walks] [maxcols] [seed]

R(M) = sum of o(i) over the (0,0,0) columns, without sf (eval(M) = sf(R(M))). Random walks of BM4 expansion
from SRO. Reports: sums in R not descending, sf(R) != eval, R not injective, sf not strictly monotone on the
image of R, R(M[n]) < R(M) failing, and common columns i < x whose o or v (before sf) grows.
"""
import os, sys, random
from functools import cmp_to_key
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import trio, ytosk_eval as Y

SRO = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (2, 0, 0)]

def summands(t):
    out = []
    while t: out.append((t[0], t[1], ())); t = t[2]
    return out

def descending(t):
    s = summands(t)
    if any(Y.lt(s[i], s[i + 1]) for i in range(len(s) - 1)): return False
    return all(descending(a) and descending(b) for a, b, _ in s)

def evaluated(M):
    ev = Y.Ev(list(M))
    try:
        for i in range(ev.n): ev.o(i)
    except Y.Cycle:
        return None
    return ev

def raw(ev):
    s = Y.Z
    for i in range(ev.n):
        if ev.M[i] == (0, 0, 0): s = Y.add(s, ev.o(i))
    return s

def main(walks=800, maxcols=40, seed=7):
    random.seed(seed)
    pairs = set()
    for _ in range(walks):
        m = SRO
        for _ in range(60):
            n = random.randint(0, 4)
            m2 = trio.expand(m, n)
            if not m2 or len(m2) > maxcols: continue
            pairs.add((tuple(m), n, tuple(m2)))
            m = m2
    mats = {p[2] for p in pairs}
    ev = {m: evaluated(m) for m in mats | {tuple(SRO)}}
    R = {m: raw(e) for m, e in ev.items() if e is not None}
    nondesc = sum(1 for m in mats if not descending(R[m]))
    neq = sum(1 for m in mats if Y.sf(R[m]) != ev[m].value())
    vals = sorted(set(R[m] for m in mats), key=cmp_to_key(lambda a, b: -1 if Y.lt(a, b) else (1 if Y.lt(b, a) else 0)))
    S = [Y.sf(x) for x in vals]
    nonmono = sum(1 for i in range(len(S) - 1) if not Y.lt(S[i], S[i + 1]))
    dfail = sum(1 for a, n, b in pairs if list(a) != SRO and not Y.lt(R[b], R[a]))
    grow = cols = 0
    for a, n, b in pairs:
        if list(a) == SRO: continue
        ea, eb = ev[a], ev[b]
        for i in range(min(len(a) - 1, len(b))):
            cols += 1
            if Y.lt(ea.o(i), eb.o(i)) or Y.lt(ea.v(i), eb.v(i)): grow += 1
    print('pairs', len(pairs), 'matrices', len(mats))
    print('non-descending sums', nondesc, '| sf(R) != eval', neq, '| distinct R', len(vals),
          '| sf not strictly monotone', nonmono, '| R(M[n]) < R(M) fails', dfail,
          '| common columns', cols, 'growing', grow)

if __name__ == '__main__':
    a = [int(x) for x in sys.argv[1:]]
    main(*a)
