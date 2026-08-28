# -*- coding: utf-8 -*-
"""**`ImgCofinalT` の破れの上界を、2 つの計器を合成して測る。**

`(conv3 A)⟦m⟧ = conv3 B` なる `B ∈ ST_TS` を探す方法は 2 つあり、**どちらの
「当たり」も証明**（`conv3 B == T` を検算する）で、**「外れ」だけが不確定**である:

    (1) 正しい母集団 `stts(L)` の**像の表**を引く   … `|T| <= L` のときだけ引ける
    (2) `rows3.preimage_try`（`d2b3` ＋ 双子戻し ＋ 接頭辞の当て直し） … 発見的

⟹ **`hit = (1) or (2)`** とすれば、`cofinal.py`（(2) だけ）より**必ず破れが減る**。
得られるのは **破れの上界**である（下界にはならない）。

⚠ 標本は**ランダムに取る**（先頭からではない）。課題 R24 で先頭 60 個の
サンプルが 960/960 当たりだったため 2 人とも `ImgCofinalT` を真と誤認した。

使い方: python3 tools/dbms/imgcof2.py [L] [mmax] [標本数] [tail]
"""
import sys, time, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, core, inv3
from stts import stts
from rows3 import b2d3, preimage_try
from core import expand

L = int(sys.argv[1]) if len(sys.argv) > 1 else 9
MM = int(sys.argv[2]) if len(sys.argv) > 2 else 16
NS = int(sys.argv[3]) if len(sys.argv) > 3 else 4000
TAIL = int(sys.argv[4]) if len(sys.argv) > 4 else 8

t0 = time.time()
P = stts(L)
print('母集団 ST_TS len<=%d（正しい既定）  **%d 個**  (%.0fs)'
      % (L, len(P), time.time() - t0), flush=True)

t0 = time.time()
img = set()
for i, M in enumerate(P):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    img.add(tuple(map(tuple, b2d3(list(M)))))
print('  像の表 %d 通り  (%.0fs)' % (len(img), time.time() - t0), flush=True)

cand = [M for M in P if len(M) > 1]
random.seed(20260829)
S = cand if len(cand) <= NS else random.sample(cand, NS)
print('  標本 **%d / %d**（**ランダム**。先頭からではない）' % (len(S), len(cand)),
      flush=True)

t0 = time.time()
n_tbl = n_try = 0
pats = {}
bad = []
for A in S:
    fA = tuple(map(tuple, b2d3(list(A))))
    pat = []
    for m in range(1, MM + 1):
        T = tuple(map(tuple, expand(fA, m)))
        if not T:
            pat.append('-'); continue
        if T in img:
            pat.append('O'); n_tbl += 1; continue
        B = preimage_try(rows3.b2d3, T, inv3.d2b3)
        if B is not None:
            pat.append('O'); n_try += 1
        else:
            pat.append('.')
    p = ''.join(pat)
    pats[p] = pats.get(p, 0) + 1
    if p[-TAIL:] != 'O' * TAIL:
        bad.append((A, p))
print('  走査 (%.0fs)  当たりの内訳: 表 **%d** / preimage_try **%d**'
      % (time.time() - t0, n_tbl, n_try), flush=True)
print(flush=True)
print('=== **`ImgCofinalT` の破れの上界**（末尾 %d 個が当たりなら非有界とみなす）' % TAIL,
      flush=True)
print('  **%d / %d（%.2f%%）**' % (len(bad), len(S), 100.0 * len(bad) / max(1, len(S))),
      flush=True)
print('  並びの型（上位）:', flush=True)
for p, c in sorted(pats.items(), key=lambda x: -x[1])[:8]:
    print('    %-18s %d' % (p, c), flush=True)
print('  破れの例:', flush=True)
for A, p in bad[:6]:
    print('    %-18s %s' % (p, ''.join('(%d,%d,%d)' % c for c in A)), flush=True)
