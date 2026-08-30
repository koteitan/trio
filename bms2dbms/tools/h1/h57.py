# -*- coding: utf-8 -*-
"""**課題 H56 —— `CoreCap` の健全性（とくに `c >= 2`）。**

⚠ **私の H36 §8.3 / H54-c / H55-c の「健全な非所属判定は `lev M[0] > u` しかない」は誤り。**
`lean/Wchar.lean` に**厳密な再帰的特徴づけ**がある:

    `mem_iff_oper_mem`（:75）  `2 <= |S|` ⟹ (`S ∈ W a` ⟺ `∀ n >= 1, S⟦n⟧ ∈ W a`)
    `mem_iff_lev_le`（:106）   `[(d,v,z)] ∈ W a` ⟺ `2v+z <= a`

⟹ **展開の木を降りて `lev > a` の単元に届けば、それは確定した非所属**（健全な反証）。
`tools/probe_cap2.py` はこれを使っている。ここではそれを `c >= 2` に広げる。
"""
import sys, itertools, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter

NS = (1, 2, 3)
MAXDEPTH = 9
MAXLEN = 28


def lev(c):
    return 2 * c[1] + c[2]


def lift1(S, t):
    return [(c[0], c[1] + (t if trio.is_ancestor(S, 1, 0, i) else 0), c[2])
            for i, c in enumerate(S)]


def inW(S, a, depth, memo):
    """True=閉じた / **False=確定した非所属**（健全） / None=予算切れ。"""
    S = tuple(tuple(c) for c in S)
    key = (S, a)
    if key in memo:
        return memo[key]
    if len(S) == 0:
        return True
    if len(S) == 1:
        r = lev(S[0]) <= a
        memo[key] = r
        return r
    if depth <= 0 or len(S) > MAXLEN:
        return None
    memo[key] = None
    out = True
    for n in NS:
        r = inW(trio.expand(list(S), n), a, depth - 1, memo)
        if r is False:
            memo[key] = False
            return False
        if r is None:
            out = None
    memo[key] = out
    return out


memo = {}
print('**陽性対照: 反証器が確定 False を返すか**')
ctl = [([(0, 1, 0)], 0, '単元、lev 2 > 0'),
       ([(0, 0, 0), (1, 1, 1)], 0, '展開すると lev 3 の単元に届く'),
       ([(0, 0, 0), (1, 2, 1)], 1, '同上、より深い'),
       ([(0, 0, 0), (1, 1, 0)], 5, '（反例でないはず）')]
for S, a, why in ctl:
    print('   `%s` @ a=%d : **%s**  （%s）'
          % (''.join('(%d,%d,%d)' % q for q in S), a,
             {True: 'W に入る', False: '**確定 非所属**', None: '未判定'}[
                 inW(S, a, MAXDEPTH, memo)], why))
print()

print('**`CoreCap` を `c >= 2` まで広げて測る**')
print('   （`probe_cap2.py` は `c in range(2)` だった。ここは `c in range(4)`）')
COLS = [(d, b, c) for d in range(1, 4) for b in range(3) for c in range(3)]
tot = Counter()
ex = {}
for L in (1, 2, 3):
    for M in itertools.product(COLS, repeat=L):
        M = list(M)
        for v in range(3):
            for z in range(2):
                eq = True
                for k in range(L):
                    for t in range(2):
                        P = lift1([(0, v, z)] + M[:k], t)
                        if inW(P, 2 * (v + t) + z, MAXDEPTH, memo) is not True:
                            eq = False
                            break
                    if not eq:
                        break
                if not eq:
                    tot['文脈: 装備できない'] += 1
                    continue
                tot['文脈: 装備できた'] += 1
                for b in range(3):
                    for c in range(4):
                        cap = M[:-1] + [(M[-1][0], b, c)]
                        for t in range(2):
                            a = 2 * (v + t) + z
                            X = lift1([(0, v, z)] + cap, t)
                            r = inW(X, a, MAXDEPTH, memo)
                            k2 = ('**違反**' if r is False
                                  else 'OK' if r is True else '未判定')
                            tot['c<=1 / ' + k2 if c <= 1
                                else '**c>=2** / ' + k2] += 1
                            if r is not True:
                                ex.setdefault((c <= 1, k2),
                                              (M, v, z, b, c, t, a, X))
print('   | 場合 | 件数 |')
print('   |---|--:|')
for k in sorted(tot):
    print('   | %s | %d |' % (k, tot[k]))
print()
for k, e in sorted(ex.items(), key=str):
    M, v, z, b, c, t, a, X = e
    print('   例 %s: M=%s v=%d z=%d b=%d c=%d t=%d a=%d'
          % (k, ''.join('(%d,%d,%d)' % q for q in M), v, z, b, c, t, a))
    print('        X=%s' % ''.join('(%d,%d,%d)' % q for q in X))
