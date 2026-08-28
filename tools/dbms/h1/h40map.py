# -*- coding: utf-8 -*-
"""**課題 H40 段階 2 —— 残核のうち何割が既に定理か。届かない形の地図。**

⚠ **`wcert` が「届かない」は「非所属」ではない。反例ではない。**
   （`lev R 0 > u` のときだけが確実な非所属だが、残核の結論は `Wself` なので起きない。）
"""
import sys, pickle
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import wcert as wc
from collections import Counter

hits = pickle.load(open('/tmp/h1work/h40hits.pkl', 'rb'))
print('前提を全部満たす (S,p,C) = **%d 組**' % len(hits))
print()

# ---- 1. 覆い -----------------------------------------------------------
c = Counter()
miss = []
for S, p, C, R in hits:
    w = wc.wcert(R)
    c[w.split('+')[0] if w else 'なし'] += 1
    if w is None:
        miss.append((S, p, C, R))
n = len(hits) - c['なし']
print('**R に証明書が届く: %d / %d (%.1f%%)  ＝ 残核のうち既に定理である部分**'
      % (n, len(hits), 100.0 * n / len(hits)))
for k, v in sorted(c.items()):
    print('   %-14s %6d (%.1f%%)' % (k, v, 100.0 * v / len(hits)))
print()

# ---- 2. 退化検査 -------------------------------------------------------
print('**退化検査**（教訓 12。自明な族と一致していないか）')
pop = [R for _, _, _, R in hits]
f = lambda R: wc.wcert(R) is not None
for nm, tv in (('「行 0 ≡ 0」', lambda R: all(q[0] == 0 for q in R)),
               ('「|R| <= 2」', lambda R: len(R) <= 2),
               ('「末尾が孤児」', lambda R: not wc.has_parent(R, len(R) - 1)),
               ('「行 2 > 0 の列が 1 本だけ」',
                lambda R: sum(1 for q in R if q[2] > 0) == 1)):
    wc.audit(pop, f, tv, 'wcert(R) vs ' + nm)
print()

# ---- 3. 限界の覆い -----------------------------------------------------
print('**限界の覆い**（既に覆われているものを除いた母数で）')
wc.marginal(pop, lambda R: wc._base(R) is not None,
            lambda R: wc.wcert(R) is not None, "(C6') 剥がし")
print()

# ---- 4. 届かない形の地図 ----------------------------------------------
print('**届かない %d 件の地図 —— どこで剥がしが止まるか**' % len(miss))


def stop_at(R):
    """(C6') の剥がしがどこで止まるか。(k 段剥がせた, 止まった X)"""
    X, k = tuple(tuple(q) for q in R), 0
    while len(X) >= 2:
        if wc._base(X):
            return k, X, 'base'
        if not wc._orphan(X, len(X) - 1):
            return k, X, 'stuck'
        X = X[:-1]
        k += 1
    return k, X, 'base'


m = Counter()
ax = Counter()
for S, p, C, R in miss:
    k, X, why = stop_at(R)
    m[(why, '%d 段剥がせた' % k)] += 1
    if why == 'stuck':
        root0 = X[0][0]
        # 行 0 の軸: 根より浅い（行 0 が小さい）列が中にある
        a0 = any(q[0] < root0 for q in X[1:])
        # lev の軸: 末尾より前に行 2 > 0 の列がある（(C2)(C5') を塞ぐ）
        a2 = any(q[2] > 0 for q in X[:-1])
        ax[('行 0 の軸' if a0 else '—', 'lev の軸' if a2 else '—')] += 1
for k, v in m.most_common(8):
    print('   %-32s %6d' % (str(k), v))
print()
print('**止まった地点での 2 軸**（`WCat` と同じ形か）')
tot = sum(ax.values())
for k, v in ax.most_common():
    print('   %-34s %6d (%.1f%%)' % (str(k), v, 100.0 * v / max(1, tot)))
print()
print('**届かない最短の例**')
for S, p, C, R in sorted(miss, key=lambda t: len(t[3]))[:5]:
    k, X, why = stop_at(R)
    print('   R=%s' % list(R))
    print('     %d 段剥がして %s で止まった X=%s' % (k, why, list(X)))
