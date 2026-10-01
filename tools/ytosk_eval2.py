# -*- coding: utf-8 -*-
"""Stepwise-normalized variant of the Ytosk evaluator: every o and v is put in standard form (sf) when
it is formed, so all intermediate values are standard terms. Agrees with ytosk_eval.Ev on 11,383 of
11,385 test matrices (all sheet rows included)."""
import ytosk_eval as Y

class Ev2(Y.Ev):
    def v(self, i):
        if i is None: return Y.Z
        if i in self._v: return self._v[i]
        if ('v', i) in self._path: raise Y.Cycle
        self._path.add(('v', i))
        if self.e(1, i) == 0: res = Y.Z
        elif self.e(2, i) == 0:
            u = self._upg[i]
            res = Y.sf(Y.add(self.v(self.par(1, i)), Y.last(self.v(u)) if u is not None else Y.ONE))
        else:
            p = Y.ONE
            for j in self.children[i]:
                if self.M[j] == self.bump(i):
                    q = Y.Z
                    for k in self.children[j]: q = Y.sf(Y.add(q, self.o(k)))
                    p = Y.sf(Y.add(p, Y.omega(q)))
            res = Y.sf(Y.add(self.v(self.par(1, i)), Y.omega(p)))
        self._path.discard(('v', i)); self._v[i] = res; return res

    def o(self, i):
        if i in self._o: return self._o[i]
        if ('o', i) in self._path: raise Y.Cycle
        self._path.add(('o', i))
        S = Y.Z
        for c in self.children[i]:
            if self.M[c] == self.bump(i): continue
            if c in self.upgs and self.topped(c): continue
            S = Y.sf(Y.add(S, self.o(c)))
        res = Y.sf((self.v(i), S, Y.Z))
        self._path.discard(('o', i)); self._o[i] = res; return res

    def value(self):
        try:
            for i in range(self.n): self.o(i)
        except Y.Cycle: return None
        s = Y.Z
        for i in range(self.n):
            if self.M[i] == (0, 0, 0): s = Y.sf(Y.add(s, self.o(i)))
        return s
