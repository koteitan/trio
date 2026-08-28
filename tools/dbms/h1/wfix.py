# -*- coding: utf-8 -*-
"""**有界宇宙の上で `W u = lfpS (Aset (Wf u) u)` を不動点反復で正確に解く。**

`h1/inw2.py` の Kleene 段版は `k`（段の予算）が要り、`k` を上げるコストが
爆発した。ここでは

  1. 種から `oper(.,n)`（節 2）と `graft(.,z)`（節 3）で**到達可能な節点**を
     長さ `maxlen` 以下に限って集める（有限）。長さ超過の節点は**恒久的に False**。
  2. その有限集合の上で `X_0 = 空`, `X_{j+1} = Aset(X_j)` を**動かなくなるまで**回す。

有限集合なので必ず止まり、**その宇宙の中では正確**（`k` の予算は消える）。

近似の向きは 3 つだけ:
  * `maxlen` 超過を False にする    ⟹ **下から**（False 側に安全）
  * 節 2 の `forall n` を `NS` で切る ⟹ 上から
  * 節 3 の `forall z` を pool で切る ⟹ 上から
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
from inw2 import lev, levM, srow, has_parent, domT, graft, based, oper, _cands


class Wfix(object):
    MAXNODES = 400000

    def __init__(self, u, maxlen=14, ns=(1, 2), zx=2, zb=2, zl=2, pools=None):
        self.u, self.maxlen, self.ns = u, maxlen, ns
        self.cap = False
        self.cand = _cands(zx, zb, zl)
        # W m (m < u) の based pool を**下の段から順に**作る
        self.pool = {}
        if pools is None:
            for m in range(u):
                sub = Wfix(m, maxlen, ns, zx, zb, zl, pools=dict(self.pool))
                self.pool[m] = tuple(z for z in self.cand if sub.mem(z))
        else:
            self.pool = pools
        self.nodes = {}          # S -> (子_節2, [(m, 子_節3), ...]) / True は底
        self.X = set()
        self._solved = False

    def _norm(self, S):
        return tuple(tuple(c) for c in S)

    def _explore(self, S):
        """節点 S を展開して子を登録。長さ超過なら None（恒久 False）。"""
        st = [self._norm(S)]
        while st:
            T = st.pop()
            if T in self.nodes or len(T) > self.maxlen:
                continue
            if len(self.nodes) >= self.MAXNODES:
                self.cap = True
                break
            if len(T) <= 1 and levM(T, 0) == 0:
                self.nodes[T] = True                       # 節 1（底）
                continue
            c2 = [self._norm(oper(T, n)) for n in self.ns]
            c3 = []
            for m in range(self.u):
                if domT(T, m):
                    c3.append([self._norm(graft(T, z)) for z in self.pool[m]])
            self.nodes[T] = (c2, c3)
            for ch in c2:
                st.append(ch)
            for g in c3:
                for ch in g:
                    st.append(ch)

    def _ok(self, T):
        return T in self.X

    def solve(self):
        """X_0 = 空 から動かなくなるまで反復。"""
        while True:
            add = set()
            for T, v in self.nodes.items():
                if T in self.X:
                    continue
                if v is True:
                    add.add(T)
                    continue
                c2, c3 = v
                if all(ch in self.X for ch in c2):
                    add.add(T)
                    continue
                if any(all(ch in self.X for ch in g) for g in c3):
                    add.add(T)
            if not add:
                break
            self.X |= add
        self._solved = True

    def mem(self, S):
        T = self._norm(S)
        if len(T) > self.maxlen:
            return False
        if T not in self.nodes:
            self._explore(T)
            self._solved = False
        if not self._solved:
            self.solve()
        return T in self.X

    def seed(self, Ss):
        for S in Ss:
            if len(self._norm(S)) <= self.maxlen:
                self._explore(S)
        self.solve()
