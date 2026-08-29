# -*- coding: utf-8 -*-
"""**課題 H59: `CorePlantCtxLift` —— `CoreSingleton` より弱い核に反証器を当てる。**

    def CorePlantCtxLift : Prop :=              `Gamma.lean:723`
      ∀ M, argOK M → 1 <= |M| → ∀ v z, z <= 1 → CtxOK M v z →
        ∀ t, **Lift1 ((0,v,z) :: M.dropLast) t ∈ GX**

`Lind.lean:208` `corePlantCtxLift_of_core : CoreSingleton → CorePlantCtxLift` は緑。
⟹ **これが偽なら `CoreSingleton` も `CoreCap` も偽**（弱いほうを狙うのが得）。

`GX`（`Gamma.lean:169`）を展開すると、`Y = Lift1 ((0,v,z) :: M.dropLast) t` について

    based Y → ∀ M' argOK, 1 <= |M'| → ∀ v' z', z' <= 1 → CtxOK M' v' z' →
      ∀ i <= |Y|, ∀ a t', 2(v'+t')+z' <= a →
        **Lift1 ((0,v',z') :: graft M' (Y.take i)) t' ∈ W a**

`based Y` は根が `(0,v,z)` なので常に真。⟹ 反証は最後の `∈ W a` を落とせばよい。

## 近似の向き

    `CtxOK` は `inW == True` で近似 ⟹ **過大に認める** ⟹ 母集団が広がる
      ⟹ 違反を見つけやすくなる ⟹ 「違反ゼロ」はこの向きで強い
    結論の `inW == False` は **確定した非所属**（健全）

## 対照

    陽性: `wref.CONTROLS`
    陰性: 同じ主語・同じ予算で段を 1 下げた版が鳴ること
"""
import sys, itertools, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import Ref, fmt, argOK, graft, Lift1, entry
from collections import Counter

TMAX = 1


def ctxOK(ref, M, v, z, tmax=TMAX):
    out = 'yes'
    for k in range(len(M)):
        for t in range(tmax + 1):
            r = ref.inW(Lift1([(0, v, z)] + list(M[:k]), t), 2 * (v + t) + z)
            if r is False:
                return 'no'
            if r is None:
                out = '?'
    return out


def verd(r):
    return '**違反**' if r is False else 'OK' if r is True else '未判定'


def main(nctx=6, seed=20260830):
    ref = Ref(ns=(1, 2, 3), maxdepth=9, maxlen=34, maxnodes=1500)
    wref.print_controls(ref)
    cols = [(d, b, c) for d in range(1, 4) for b in range(3) for c in range(2)]

    # ---------------- 消費側の文脈 `(M', v', z')` を先に用意（装備できたものだけ）
    ctxs = []
    st = Counter()
    for L in (1, 2):
        for Mp in itertools.product(cols, repeat=L):
            Mp = list(Mp)
            for vp in range(3):
                for zp in range(2):
                    s = ctxOK(ref, Mp, vp, zp)
                    st[s] += 1
                    if s == 'yes':
                        ctxs.append((Mp, vp, zp))
    print('## 消費側の文脈')
    print()
    print('装備できた `(M\', v\', z\')`: **%d** / %d（未判定 %d、**確定で破れ %d**）'
          % (len(ctxs), sum(st.values()), st['?'], st['no']))
    print()
    rng = random.Random(seed)
    use = ctxs if len(ctxs) <= nctx else rng.sample(ctxs, nctx)
    print('うち無作為 **%d** 本を使う。' % len(use))
    print()

    # ---------------- 主語 `Y = Lift1 ((0,v,z) :: M.dropLast) t`
    Ys = []
    sty = Counter()
    for L in (1, 2, 3):
        for M in itertools.product(cols, repeat=L):
            M = list(M)
            for v in range(3):
                for z in range(2):
                    s = ctxOK(ref, M, v, z)
                    sty[s] += 1
                    if s == 'no':
                        continue
                    for t in range(TMAX + 1):
                        Ys.append((Lift1([(0, v, z)] + M[:-1], t), M, v, z, t))
    print('## 主語 `Y = Lift1 ((0,v,z) :: M.dropLast) t`')
    print()
    print('生成した `Y`: **%d** 本（`CtxOK` が確定で破れた `M` は除外: %d 件）'
          % (len(Ys), sty['no']))
    if len(Ys) > 9000:
        Ys = rng.sample(Ys, 9000)
        print()
        print('⟹ マシンが他エージェントと競合しているため、**無作為 9000 本**で測る。')
    print()

    tot = Counter()
    ctl = Counter()
    ex = []
    rows = []
    t0 = time.time()
    for n, (Y, M, v, z, t) in enumerate(Ys):
        if n % 2000 == 0:
            sys.stderr.write('  Y %d/%d  %.0fs\n' % (n, len(Ys), time.time() - t0))
        for (Mp, vp, zp) in use:
            for i in range(len(Y) + 1):
                G = graft(Mp, Y[:i])
                for tp in range(TMAX + 1):
                    X = Lift1([(0, vp, zp)] + G, tp)
                    a = 2 * (vp + tp) + zp
                    if len(X) > 8:
                        tot['長すぎて外した'] += 1
                        continue
                    r = ref.inW(X, a)
                    tot[verd(r)] += 1
                    if i == len(Y):
                        rows.append((verd(r), X))
                    if r is False and len(ex) < 8:
                        ex.append((M, v, z, t, Mp, vp, zp, i, tp, a, X))
                    if a >= 1:
                        ctl[verd(ref.inW(X, a - 1))] += 1
    print('**`CorePlantCtxLift`（`GX` を展開した義務）**')
    print()
    wref.tally(tot, '結果')
    for e in ex:
        M, v, z, t, Mp, vp, zp, i, tp, a, X = e
        print('    ★★ **確定した反例**: M=`%s` v=%d z=%d t=%d ／ '
              'M\'=`%s` v\'=%d z\'=%d i=%d t\'=%d a=%d'
              % (fmt(M), v, z, t, fmt(Mp), vp, zp, i, tp, a))
        print('        X=`%s`' % fmt(X))
    if ex:
        print()
        print('    ⟹ **`CorePlantCtxLift` は偽 ⟹ `CoreSingleton` も `CoreCap` も偽**')
        print()
    wref.tally(ctl, '陰性対照（同じ主語・同じ予算で段を 1 下げた版。違反が出るべき）')
    wref.degeneracy(rows)


if __name__ == '__main__':
    main()
