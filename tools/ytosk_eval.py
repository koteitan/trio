# -*- coding: utf-8 -*-
"""Python port of Ytosk.Eval (Ytosk/lean/Ytosk/Eval.lean), with per-column data for analysis.

Terms are tuples: () = 0, (a, b, c) = psi_a(b) + c. The order `lt` is the lexicographic one.
  ev = Ev(M); ev.o(i), ev.v(i), ev.par(r, i), ev.upg(i); ev.value() = sf(sum of o over the roots)
Cycles of v/o give None (as `eval = none` in Lean).
"""
import sys
sys.setrecursionlimit(100000)

Z = ()
ONE = (Z, Z, Z)

def lt(x, y):
    if not y: return False
    if not x: return True
    if x[0] != y[0]: return lt(x[0], y[0])
    if x[1] != y[1]: return lt(x[1], y[1])
    return lt(x[2], y[2])

def head(x): return () if not x else (x[0], x[1], Z)

def add(x, y):
    if not x: return y
    if not y: return x
    if lt((x[0], x[1], Z), (y[0], y[1], Z)): return y
    return (x[0], x[1], add(x[2], y))

def sub(x, y):
    if not x: return Z
    if not y: return x
    if lt((y[0], y[1], Z), (x[0], x[1], Z)): return x
    return sub(x[2], y[2])

def split(x, t):
    if not x: return (Z, Z)
    if lt((x[0], x[1], Z), t): return (Z, x)
    r = split(x[2], t)
    return ((x[0], x[1], r[0]), r[1])

def omega(x):
    if lt(x, (Z, (ONE, Z, Z), Z)): return (Z, x, Z)
    s, b = x[0], x[1]
    p = split(b, (add(s, ONE), Z, Z))[0]
    return (s, add(p, sub(x, (s, p, Z))), Z)

def last(x):
    if not x: return Z
    if not x[2]: return (x[0], x[1], Z)
    return last(x[2])

def cut(w, x):
    if not x: return Z
    r = cut(w, x[2])
    if not r and lt((x[0], x[1], Z), (w, Z, Z)): return Z
    return (x[0], x[1], r)

def sp(a, b, c):
    while c:
        s, y, rest = c
        if lt(b, y) and lt((a, Z, Z), c):
            t = cut(add(s, ONE), y)
            b = add(t, sub((s, y, Z), (s, t, Z)))
        else:
            b = add(b, (s, y, Z))
        c = rest
    return (a, b, Z)

def sf(x):
    if not x: return Z
    return add(sp(sf(x[0]), Z, sf(x[1])), sf(x[2]))

def tstr(t):
    if not t: return '0'
    out = []
    while t:
        a, b, t = t
        out.append('1' if not a and not b else 'p' + ('' if not a else '_{%s}' % tstr(a)) + '(%s)' % tstr(b))
    return '+'.join(out)

class Cycle(Exception): pass

class Ev:
    def __init__(self, M):
        self.M = [tuple(c) for c in M]
        self.n = len(self.M)
        self._par = {}
        self._v, self._o = {}, {}
        self._path = set()
        self.children = [[] for _ in range(self.n)]
        for i in range(self.n):
            p = self.par(0, i)
            if p is not None: self.children[p].append(i)
        self._upg = [self.upg(i) for i in range(self.n)]
        self.upgs = set(u for u in self._upg if u is not None)

    def e(self, r, i): return self.M[i][r] if 0 <= i < self.n else 0

    def par(self, r, i):
        key = (r, i)
        if key in self._par: return self._par[key]
        step = (lambda q: q - 1 if q > 0 else None) if r == 0 else (lambda q: self.par(r - 1, q))
        q = step(i)
        while q is not None and not (self.e(r, q) < self.e(r, i)):
            q = step(q)
        self._par[key] = q
        return q

    def upg(self, i):
        if self.e(1, i) == 0 or self.e(2, i) == 1 or i + 1 == self.n: return None
        m = self.par(1, i)
        if m is None: return None
        L = (self.e(0, m) + 1, self.e(1, i), self.e(2, m) + 1)
        if self.par(1, i + 1) == m and self.M[i + 1] == L: return i + 1
        q = self.par(0, i)
        while q is not None:
            if self.par(1, q) == m and self.M[q] == L and self.e(0, q) < self.e(0, i + 1): return q
            q = self.par(0, q)
        return None

    def bump(self, i): return (self.e(0, i) + 1, self.e(1, i), 1)

    def topped(self, i):
        ch = self.children[i]
        return not ch or self.M[ch[-1]] == self.bump(i)

    def v(self, i):
        if i is None: return Z
        if i in self._v: return self._v[i]
        if ('v', i) in self._path: raise Cycle
        self._path.add(('v', i))
        if self.e(1, i) == 0: res = Z
        elif self.e(2, i) == 0:
            u = self._upg[i]
            res = add(self.v(self.par(1, i)), last(self.v(u)) if u is not None else ONE)
        else:
            p = ONE
            for j in self.children[i]:
                if self.M[j] == self.bump(i):
                    q = Z
                    for k in self.children[j]: q = add(q, self.o(k))
                    p = add(p, omega(q))
            res = add(self.v(self.par(1, i)), omega(p))
        self._path.discard(('v', i))
        self._v[i] = res
        return res

    def o(self, i):
        if i in self._o: return self._o[i]
        if ('o', i) in self._path: raise Cycle
        self._path.add(('o', i))
        S = Z
        for c in self.children[i]:
            if self.M[c] == self.bump(i): continue
            if c in self.upgs and self.topped(c): continue
            S = add(S, self.o(c))
        res = (self.v(i), S, Z)
        self._path.discard(('o', i))
        self._o[i] = res
        return res

    def value(self):
        try:
            for i in range(self.n): self.o(i)
        except Cycle:
            return None
        s = Z
        for i in range(self.n):
            if self.M[i] == (0, 0, 0): s = add(s, self.o(i))
        return sf(s)

if __name__ == '__main__':
    import re
    for line in sys.stdin:
        cs = [tuple(int(v) for v in c.split(',')) for c in re.findall(r'\((\d+,\d+,\d+)\)', line)]
        v = Ev(cs).value()
        print('none' if v is None else tstr(v))
