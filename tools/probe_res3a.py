# -*- coding: utf-8 -*-
"""Res3A（Ytosk/lean/Ytosk/V3TopB.lean）の各欄を Lean の文の通りに測る。

  python3 probe_res3a.py <mats.pkl>... [--n 2,3,4]

欄（x = 最後の列、ρ = M の評価、ρ' = drop1 M x = M.take x の評価、σ = M[n] の評価）:
- drop.*   : DropRes M x ρ ρ'（argT・VSmallNew・BumpWeakSrc（46d767db の形: k < x ∧ o′ ≠ o ∧ v′ ⋪ v）・
             UpgAbsX・BumpAbsC）。
- seed     : r = P_1(x) = P_0(x)、sf(v′(r)) < v(r) なら comps u o′(r) の元はすべて < o′(r)。
- t0.hVr   : x の行 1 が 0、r = P_0(x)、o′(r) = ψ_{s′}(y′)、s′ ≠ v(r)、g = P_0(r)、CL M g = Lc ++ [r]、
             o(r) = ψ_s(y) が g の枠で書き換えるなら VSmallV s′。
- t0.hG'   : 同じ r で、g = P_0(r)、col r = bump g、g の行 1・2 が 0 でないなら
             sumN (children (M.take x) r の o′) = sumN (同じ子の o)。
- t0.VSNN  : 同じ r で、n ≥ 2、σ = M[n]（= gexp M r L 0 0 n）の評価: i < r、CL M i = Lc ++ [cs]、σ.v cs ≠ v(cs)、
             cs が M の枠で書き換えるなら VSmallV (σ.v cs)。
添字の範囲: どの欄も ρ'（M.take x の評価）を x 未満でしか読まない（cs ∈ CL(M.take x)、r < x、
children (M.take x) r）。σ は cs < r + L ≤ |M[n]| でしか読まない。それも数えて確かめる。
◁ は標本の近似（BumpWeakSrc の v′ ⋪ v の判定だけで使う）。
"""
import sys, os, pickle
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_inv3_prefix import *

NS = [2, 3, 4]

def lhdE(a, b): return a == b or lhd(a, b)

def bws_lean(C, T, note):
    """BumpWeakSrc（46d767db）。"""
    M = C.M; x = len(M) - 1
    for i in range(len(M)):
        if not C.e12(i): continue
        V = C.vOpt1(i)
        for j in C.ch(i):
            if M[j] != C.e.bump(i): continue
            kids = C.ch(j)
            for idx, k in enumerate(kids):
                ok_ = C.o(k)
                if not (ok_[1] == Z and ok_[2] == Z and ok_[0] != Z): continue
                fire = (k == x and kids == [x]) or \
                    (k < x and T.o(k) != ok_ and not lhdE(T.v(k), C.v(k)))
                if fire:
                    note('drop.BumpWeakSrc', C.ch(i) == [j] and idx == 0 and all(lt(g, OM1) for g in comps(Z, V)),
                         (i, j, k))

def check(M):
    M = list(M); cnt = Counter(); ex = {}
    def note(f, ok, info):
        cnt[(f, 'cases')] += 1
        if not ok:
            cnt[(f, 'FAIL')] += 1
            if len(ex.setdefault(f, [])) < 2: ex[f].append((M, info))
    if len(M) < 2: return cnt, ex
    C = Ctx(M); T = Ctx(M[:-1]); x = len(M) - 1
    if not (C.ok and T.ok): cnt['noval'] += 1; return cnt, ex
    cnt['mats'] += 1
    # drop
    def dnote(f, ok, info):
        if f != 'BumpWeakSrc': note('drop.' + f, ok, info)
    drop_fields(C, T, dnote)
    bws_lean(C, T, note)
    # seed
    r1, r0 = C.e.par(1, x), C.e.par(0, x)
    if r1 is not None and r1 == r0:
        r = r1
        cnt[('index', 'seed r<x')] += (r < x)
        if lt(Y.sf(T.v(r)), C.v(r)):
            o2 = T.o(r)
            note('seed', all(lt(g, o2) for g in comps(Z, o2)), (r,))
    # t0
    r = C.e.par(0, x)
    if r is not None and M[x][1] == 0:
        L = x - r
        g = C.e.par(0, r)
        s2, y2, _ = T.o(r)
        if s2 != C.v(r) and g is not None:
            cl = C.CL(g)
            if cl and cl[-1] == r:
                Lc = cl[:-1]; s, y, _ = C.o(r)
                B = spa(C.v(g), sumN([C.o(d) for d in Lc]))
                if lt(B, y) and lt((C.v(g), Z, Z), (s, y, Z)):
                    note('t0.hVr', vsmallV(s2), (r, g, Y.tstr(s2)))
        if g is not None and M[r] == C.e.bump(g) and C.e12(g):
            chT = T.ch(r)
            cnt[('index', "hG' children<x")] += all(c < x for c in chT)
            note("t0.hG'", sumN([T.o(c) for c in chT]) == sumN([C.o(c) for c in chT]), (r, g))
        for n in NS:
            N = trio.expand(M, n)
            if not N or len(N) != r + n * L or N[:r] != M[:r]:
                cnt[('VSNN expand shape mismatch', n)] += 1; continue
            S = Ctx(N)
            if not S.ok: cnt[('VSNN N noval', n)] += 1; continue
            for i in range(r):
                cl = C.CL(i)
                if not cl: continue
                cs = cl[-1]; Lc = cl[:-1]
                if cs >= len(N): cnt[('index', 'VSNN cs>=|N|')] += 1; continue
                cnt[('VSNN frames', n)] += 1
                if S.v(cs) == C.v(cs): continue
                cnt[('VSNN v(cs) changed', n)] += 1
                s, y, _ = C.o(cs)
                B = spa(C.v(i), sumN([C.o(d) for d in Lc]))
                if lt(B, y) and lt((C.v(i), Z, Z), (s, y, Z)):
                    note('t0.VSNN n=%d' % n, vsmallV(S.v(cs)), (i, cs, Y.tstr(S.v(cs))))
    return cnt, ex

if __name__ == '__main__':
    args = sys.argv[1:]
    if '--n' in args:
        k = args.index('--n'); NS[:] = [int(t) for t in args[k + 1].split(',')]; del args[k:k + 2]
    mats = []
    for f in args: mats += pickle.load(open(f, 'rb'))
    tot = Counter(); exs = {}
    with Pool(24) as p:
        for c, ex in p.imap_unordered(check, mats, chunksize=20):
            tot.update(c)
            for k, v in ex.items():
                if len(exs.setdefault(k, [])) < 2: exs[k].extend(v[:2 - len(exs[k])])
    for k in sorted(tot, key=str): print(k, tot[k])
    for k, v in exs.items():
        for M, info in v:
            print('EX', k, 'std' if std(M) else 'nonstd', ''.join('(%d,%d,%d)' % c for c in M), info)
