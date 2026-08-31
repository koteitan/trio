# -*- coding: utf-8 -*-
"""`tools/inw_audit.py` の仮説 H を**正しい `inW`**（h1/inw2.py）で測り直す。

    H: inW(S, a) is True  <=>  lev(S[0]) <= a

母集団は `tools/inw_audit.py` と同じ（seed も同じ）。
使い方: python3 h1/inw2audit.py [標本数] [maxd] [zx] [zb] [zl]
"""
import sys, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
import inw2

N = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
MD = int(sys.argv[2]) if len(sys.argv) > 2 else 12
ZX = int(sys.argv[3]) if len(sys.argv) > 3 else 2
ZB = int(sys.argv[4]) if len(sys.argv) > 4 else 2
ZL = int(sys.argv[5]) if len(sys.argv) > 5 else 2

f = inw2.InW(maxd=MD, zx=ZX, zb=ZB, zl=ZL)
rng = random.Random(20260829)          # inw_audit.py と同じ seed
agree = dis = und = 0
ex_f, ex_t = [], []
t0 = time.time()
for _ in range(N):
    L = rng.randint(1, 7)
    S = []
    for _ in range(L):
        x = rng.randint(0, 5)
        y = rng.randint(0, x)
        z = rng.randint(0, min(y, 1))
        S.append((x, y, z))
    a = rng.randint(0, 12)
    r = f(S, a)
    if r is None:
        und += 1
        continue
    pred = inw2.lev(S[0]) <= a
    if r == pred:
        agree += 1
    else:
        dis += 1
        (ex_f if r is False else ex_t).append((S, a))
tot = agree + dis
print('標本 %d  maxd=%d  pool=(x<%d,b<%d,|z|<=%d) 候補 %d'
      % (N, MD, ZX, ZB, ZL, len(f.cand)))
print('  判定できた %d / 未判定 %d   (%.0fs)' % (tot, und, time.time() - t0))
print('  inW(S,a) == (lev(S[0]) <= a): %d / %d (%.2f%%)'
      % (agree, tot, 100.0 * agree / max(1, tot)))
print('  **食い違い %d**  内訳: inW=False だが lev<=a が %d / inW=True だが lev>a が %d'
      % (dis, len(ex_f), len(ex_t)))
print('  節: c1=%d c2=%d c3=%d 偽=%d' % tuple(
    f.stat[k] for k in ('c1', 'c2', 'c3', 'no')))
if dis == 0:
    print('  ⟹ **まだ退化している。**')
else:
    print('  ⟹ **計器は生きている。** inW=False なのに lev(S[0])<=a の例:')
    for S, a in ex_f[:3]:
        print('     a=%d lev=%d  S=%s' % (a, inw2.lev(S[0]), S))
    if ex_t:
        print('   inW=True なのに lev(S[0])>a の例（**Lean の定理に反する ⟹ 近似の破れ**）:')
        for S, a in ex_t[:3]:
            print('     a=%d lev=%d  S=%s' % (a, inw2.lev(S[0]), S))
