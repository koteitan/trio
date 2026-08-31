# -*- coding: utf-8 -*-
"""**(SNOC) を正しい `inW`（h1/inw2.py）で測り直す。**

    (SNOC)  C in W u -> C /= [] -> hasParent (C ++ [p]) (srow ..) |C|
            ->  C ++ [p] in W u

正しい `inW` は **True が健全 / False は「予算 k 内で未確認」**（Kleene 近似は
`W` を下から近似する）。したがって

    inW_k(C,u) = True かつ inW_K(C++[p],u) = False   (K >> k)

は**違反の候補**であって確定ではない。K を上げて反転しないものだけを残す。

使い方: python3 h1/h36snoc.py [k] [K] [列の上限]
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
import inw2

K1 = int(sys.argv[1]) if len(sys.argv) > 1 else 20
K2 = int(sys.argv[2]) if len(sys.argv) > 2 else 80
XM = int(sys.argv[3]) if len(sys.argv) > 3 else 4

COLS = [(x, b, c) for x in range(XM) for b in range(x + 1)
        for c in range(min(b, 1) + 1)]
UMAX = 6

f1 = inw2.InW(maxd=K1, zx=2, zb=2, zl=2)
f2 = inw2.InW(maxd=K2, zx=2, zb=2, zl=2)

# 1. inW が True と確認できる C を集める（(SNOC) の**仮定**側）
t0 = time.time()
good = []
for L in (1, 2, 3, 4):
    for C in itertools.product(COLS, repeat=L):
        for u in range(UMAX + 1):
            if f1(C, u) is True:
                good.append((C, u))
                break                      # 最小の u だけ持つ
print('柱 %d 個  C の候補 %d 個から **W に入ると確認できた C = %d 個**  (%.0fs)'
      % (len(COLS), sum(len(COLS) ** L for L in (1, 2, 3, 4)), len(good),
         time.time() - t0))

# 2. (SNOC) の対を作って結論側を測る
t0 = time.time()
tot = conc_ok = cand = 0
orph = 0
ex = []
for C, u in good:
    for p in COLS:
        S = tuple(C) + (p,)
        j = len(C)
        if not inw2.has_parent(S, j):
            orph += 1
            continue                       # (SNOC) の仮定を満たさない
        tot += 1
        if f1(S, u) is True:
            conc_ok += 1
        elif f2(S, u) is True:
            conc_ok += 1                   # 予算を上げたら通った
        else:
            cand += 1
            if len(ex) < 8:
                ex.append((C, p, u))
print('(SNOC) の対 %d 件（末尾に親あり）／ 孤児で対象外 %d 件  (%.0fs)'
      % (tot, orph, time.time() - t0))
print('  結論も確認できた **%d / %d** (%.2f%%)' % (conc_ok, tot,
                                                100.0 * conc_ok / max(1, tot)))
print('  **違反の候補（k=%d で仮定は真、k=%d でも結論が未確認）: %d**'
      % (K1, K2, cand))
if cand == 0:
    print('  ⟹ **(SNOC) に反例なし。**予算を %d 段まで上げても結論は常に確認できた。' % K2)
else:
    print('  ⟹ 候補を印字（**確定ではない。予算不足かもしれない**）:')
    for C, p, u in ex:
        print('     u=%d  C=%s  p=%s' % (u, list(C), p))
