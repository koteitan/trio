# -*- coding: utf-8 -*-
"""**H40 段階 3 —— なぜ 0% なのか。残核の前提は証明書を構造的に排除する。**

さらに `wcert` に無い証明書（(C9) `oper_closed` / (C10)(C11) `wcat_cert`）も当てる。
"""
import sys, pickle, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import wcert as wc
import trio
from collections import Counter

hits = pickle.load(open('/tmp/h1work/h40hits.pkl', 'rb'))
print('前提を全部満たす (S,p,C) = %d 組' % len(hits))
print()
print('**★ 証明書ごとに「構造的に使えるか」を数える**')
b = Counter()
for S, p, C, R in hits:
    b['(C1) |R| <= 1'] += (len(R) <= 1)
    b['(C2) 行 2 ≡ 0'] += all(q[2] == 0 for q in R)
    b['(C3) 行 0 ≡ 0'] += all(q[0] == 0 for q in R)
    b["(C5') R[:-1] が行 2 ≡ 0"] += all(q[2] == 0 for q in R[:-1])
    b["(C6') R の末尾が孤児"] += wc._orphan(R, len(R) - 1)
for k in ('(C1) |R| <= 1', '(C2) 行 2 ≡ 0', '(C3) 行 0 ≡ 0',
          "(C5') R[:-1] が行 2 ≡ 0", "(C6') R の末尾が孤児"):
    print('   %-28s %6d / %d' % (k, b[k], len(hits)))
print()
print('   前提 10「R.dropLast に行 2 > 0」 ⟹ **(C1)(C2)(C5\') を排除**')
print('   前提  8「R の末尾は R で親を持つ」 ⟹ **(C6\') を排除**（剥がしが 0 段で止まる）')
print('   ⟹ **残核の前提は、末尾から剥がす証明書を全部ふさぐように書かれている。**')
print()

# ---- (C10)(C11) を全ての切り方で -------------------------------------
print('**(C10) `W_flatMap_copies` / (C11) `W_add` を全ての切り方で当てる**')
c = Counter()
for S, p, C, R in hits:
    got = None
    for j in range(1, len(R)):
        w = wc.wcat_cert(R[:j], R[j:])
        if w in ('C10', 'C11'):
            got = w
            break
    c[got or 'なし'] += 1
for k, v in sorted(c.items()):
    print('   %-8s %6d (%.1f%%)' % (k, v, 100.0 * v / len(hits)))
print()

# ---- (C9) oper_closed: R の前身を探す ---------------------------------
print('**(C9) `oper_closed`（M ∈ W u ⟹ M⟦n⟧ ∈ W u）: R の前身に証明書が届くか**')
COLS = [(a, bb, cc) for a in range(6) for bb in range(6) for cc in range(2)]
pre = Counter()
seen = {}
for S, p, C, R in hits[:1500]:
    R = tuple(tuple(q) for q in R)
    if R in seen:
        pre[seen[R]] += 1
        continue
    got = 'なし'
    # 前身 M は R より短い（展開は伸びるか同じ）。長さ 1..|R| で総当りは無理なので
    # 「R = M[n] となる M」を **R の接頭辞＋1 列**の形に限って探す
    for j in range(1, min(len(R), 5) + 1):
        M = R[:j]
        if wc.wcert(M) is None:
            continue
        for n in (1, 2, 3):
            if tuple(tuple(q) for q in trio.expand(list(M), n)) == R:
                got = 'C9'
                break
        if got == 'C9':
            break
    seen[R] = got
    pre[got] += 1
for k, v in sorted(pre.items()):
    print('   %-8s %6d / %d' % (k, v, sum(pre.values())))
print()

# ---- 2 軸の分類 --------------------------------------------------------
print('**届かない形の 2 軸**（`WCat` と同じ形か）')
ax = Counter()
for S, p, C, R in hits:
    root0 = R[0][0]
    a0 = any(q[0] < root0 for q in R[1:])          # 行 0 の軸: 根より浅い列
    a2 = any(q[2] > 0 for q in R[:-1])             # lev の軸: 中に行 2 > 0
    ax[('行 0 の軸' if a0 else '—', 'lev の軸' if a2 else '—')] += 1
for k, v in ax.most_common():
    print('   %-30s %6d (%.1f%%)' % (str(k), v, 100.0 * v / len(hits)))
print()
print('   ⟹ **lev の軸は 100%%**（前提 10 がそう書いてある）。')
print('      行 0 の軸は %.1f%% で、`WCat` の 98%% とは**別**。'
      % (100.0 * sum(v for k, v in ax.items() if k[0] != '—') / len(hits)))
