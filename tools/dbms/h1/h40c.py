# -*- coding: utf-8 -*-
"""**H40 段階 4 —— 残核を、前提から無料で出る証明書で正しく測る。**

残核の前提から**ただで**手に入る所属（すべて Lean で証明ずみ）:

    S ∈ Wself, C ∈ Wself                          （前提）
    `W_segment`（`Wtower2.lean:2981`）:
        M ∈ W u ⟹ (M.drop j).take k ∈ W (lev M j)
        lev ((M.drop j).take k) 0 = lev M j ⟹ **∈ Wself**
    ⟹ **S の任意の連続区間、C の任意の連続区間が Wself**

貼り合わせ（`W_add`, `Wset.lean:1682`）:

    A ∈ W u, B ∈ W u, rsum A B  ⟹  A ++ B ∈ W u
    `mem_Wself_iff` で段を揃える: A,B ∈ Wself かつ **lev B 0 <= lev A 0** なら
    A ++ B ∈ W (lev A 0) = W (lev (A++B) 0) ⟹ **∈ Wself**

⚠ `wcert.wcat_cert` は `A`,`B` 自身の所属を検査しない（呼ぶ側が前提として持つ設計）。
   **任意の切り方に当てると不健全**。ここでは両側を必ず確かめる。
"""
import sys, pickle
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import wcert as wc
from collections import Counter

hits = pickle.load(open('/tmp/h1work/h40hits.pkl', 'rb'))
print('前提を全部満たす (S,p,C) = %d 組' % len(hits))
print()


def segments(M):
    """M の連続区間すべて（`W_segment` で Wself）。"""
    M = tuple(tuple(q) for q in M)
    return {M[i:j] for i in range(len(M)) for j in range(i + 1, len(M) + 1)}


def mk_self(S, C):
    """この (S,C) で `Wself` と**証明できる**行列の集合（無料の分）。"""
    free = segments(S) | segments(C)
    free.add(())

    def is_self(M):
        M = tuple(tuple(q) for q in M)
        if M in free:
            return 'W_segment'
        w = wc.wcert(M)
        return w if w else None
    return is_self


def glue(is_self, R, depth=2, memo=None):
    """`W_add` で R を組み立てられるか。深さ `depth` まで切る。"""
    if memo is None:
        memo = {}
    R = tuple(tuple(q) for q in R)
    if R in memo:
        return memo[R]
    memo[R] = None
    w = is_self(R)
    if w:
        memo[R] = w
        return w
    if depth <= 0:
        return None
    for j in range(1, len(R)):
        A, B = R[:j], R[j:]
        if wc.lev0(B) > wc.lev0(A):
            continue                       # 段が揃わない
        if not wc.rsum(A, B):
            continue                       # 側条件
        a = glue(is_self, A, depth - 1, memo)
        if not a:
            continue
        b = glue(is_self, B, depth - 1, memo)
        if not b:
            continue
        memo[R] = 'C11(%s|%s)' % (a, b)
        return memo[R]
    return None


c = Counter()
miss = []
why = Counter()
for S, p, C, R in hits:
    isf = mk_self(S, C)
    g = glue(isf, R)
    c[g.split('(')[0] if g else 'なし'] += 1
    if not g:
        miss.append((S, p, C, R))
        # なぜ貼れないか
        ok_lev = ok_rsum = 0
        for j in range(1, len(R)):
            A, B = R[:j], R[j:]
            if wc.lev0(B) <= wc.lev0(A):
                ok_lev += 1
                if wc.rsum(A, B):
                    ok_rsum += 1
        if ok_lev == 0:
            why['**lev の軸**: どの切り方でも lev B 0 > lev A 0'] += 1
        elif ok_rsum == 0:
            why['**行 0 の軸**: lev は揃うが rsum が全部落ちる'] += 1
        else:
            why['両方通る切り方はあるが、片側に証明書が無い'] += 1

n = len(hits) - c['なし']
print('**R に証明書が届く: %d / %d (%.1f%%)  ＝ 残核のうち既に定理である部分**'
      % (n, len(hits), 100.0 * n / len(hits)))
for k, v in sorted(c.items()):
    print('   %-14s %6d (%.1f%%)' % (k, v, 100.0 * v / len(hits)))
print()
print('**届かない %d 件が、どちらの軸で止まるか**' % len(miss))
for k, v in why.most_common():
    print('   %-46s %6d (%.1f%%)' % (k, v, 100.0 * v / len(miss)))
print()
print('**退化検査**')
pop = [(S, p, C, R) for S, p, C, R in hits]
f = lambda t: glue(mk_self(t[0], t[2]), t[3]) is not None
wc.audit(pop, f, lambda t: len(t[3]) <= 2, 'この計器 vs 「|R| <= 2」')
wc.audit(pop, f, lambda t: t[1] == 0, 'この計器 vs 「p = 0」')
wc.audit(pop, f, lambda t: len(t[2]) == 1, 'この計器 vs 「|C| = 1」')
print()
print('**限界の覆い**（`wcert` 単独が覆えなかったものを母数に）')
wc.marginal(pop, lambda t: wc.wcert(t[3]) is not None, f, 'W_segment + W_add')
print()
print('**届かない最短の例**')
for S, p, C, R in sorted(miss, key=lambda t: len(t[3]))[:4]:
    print('   S=%s p=%d C=%s' % (list(S), p, list(C)))
    print('     R=%s  lev(R 0)=%d' % (list(R), wc.lev0(R)))
