# -*- coding: utf-8 -*-
"""BumpAbsW（BumpAbs を弱い閉包の外の列でだけ）と BWS‴（BWS′ に「v′(i) ⋪ v(i)」を加えたもの）を測る。

  python3 probe_bumpw.py <mats.pkl>...

弱い閉包: 崩れの枠（段の子の子が最後の列 x だけで v(x) ≠ 0）の v から、o ← o(子) を通さず、o ← v(自分) は数える
子がないときだけ通して、依存の辺を逆にたどった呼び出し。C′（A∪B∪C の接頭辞閉包、404051 個）で両方とも例外 0。
"""
import sys, pickle
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_dropres_single import *
from collections import Counter
from multiprocessing import Pool
def weakClosureNodes(C):
    M = C.M; x = len(M) - 1
    src = [('v', i) for i in range(len(M)) if C.e12(i) and C.v(x) != Z and
           any(M[j] == C.e.bump(i) and C.ch(j) == [x] for j in C.ch(i))]
    rev = {}
    for i in range(len(M)):
        for nd, ds in rhs_deps(C, i).items():
            for d, k in ds:
                if k == 'o<-o(child)': continue
                if k == 'o<-v(self)' and C.CL(nd[1]): continue
                rev.setdefault(d, []).append(nd)
    out = set(src); todo = list(src)
    while todo:
        nd = todo.pop()
        for nx in rev.get(nd, []):
            if nx not in out: out.add(nx); todo.append(nx)
    return out
def lhdE(a, b): return a == b or lhd(a, b)
def go(M):
    M = list(M); cnt = Counter(); ex = {}
    if len(M) < 2: return cnt, ex
    C = Ctx(M); T = Ctx(M[:-1]); x = len(M) - 1
    if not (C.ok and T.ok): return cnt, ex
    W = weakClosureNodes(C)
    def note(k, ok, info):
        cnt[(k, ok)] += 1
        if not ok and len(ex.setdefault(k, [])) < 2: ex[k].append((''.join('(%d,%d,%d)' % t for t in M), info))
    for i in range(len(M)):
        if not C.e12(i): continue
        V = C.vOpt1(i); Wt = C.bumpW(i)
        if ('v', i) not in W:
            for r in summ(V):
                if not lt(r, W2) and lt(r, Wt): note('BumpAbsW', lhd(r, Wt), (i,))
        for j in C.ch(i):
            if M[j] != C.e.bump(i): continue
            kids = C.ch(j)
            for idx, k in enumerate(kids):
                ok_ = C.o(k)
                if not (ok_[1] == Z and ok_[2] == Z and ok_[0] != Z): continue
                fire = (k == x and kids == [x]) or (k < x and T.o(k) != ok_ and not lhdE(T.v(k), C.v(k)))
                if not fire: continue
                if i < x and lhdE(T.v(i), C.v(i)): note("BWS''' (skipped: v'(i) lhd v(i))", True, ()); continue
                note("BWS'''", C.ch(i) == [j] and idx == 0 and all(lt(g, OM1) for g in comps(Z, V)), (i, j, k))
    return cnt, ex
if __name__ == '__main__':
    mats = []
    for f in sys.argv[1:]: mats += pickle.load(open(f, 'rb'))
    tot = Counter(); exs = {}
    with Pool(24) as p:
        for c, e in p.imap_unordered(go, mats, chunksize=50):
            tot.update(c)
            for k, v in e.items():
                if len(exs.setdefault(k, [])) < 2: exs[k].extend(v[:2 - len(exs[k])])
    for k in sorted(tot, key=str): print(k, tot[k])
    for k, v in exs.items():
        for e in v: print('EX', k, e)
