# -*- coding: utf-8 -*-
"""`prefixCopiesOpen_of_zeroRow2` から `hzA` を外した版の反証器。

狙う文（**Q だけ行 2 ≡ 0、A は任意の `W` 元**）:

    A in W u,  Q in W u,  (forall q in Q, entry Q 0 0 <= q.1),
    (exists q in A, q.1 < entry Q 0 0),  (forall p in Q, p.2 = 0)
      ==>  A ++ Q^n in W u

既存の `prefixCopiesOpen_of_zeroRow2`（`lean/H12Export.lean:4452`）は **A も**
行 2 ≡ 0 を要求する。その 1 点だけを外した形。

両側とも健全に挟む:
  下界（True が健全）  緑の定理だけ: zeroRow2 / two_col_mem_W / r49 の Wlo（孤児の塔）
  上界（False が健全）  r49 の Wup（節 2 を n<=N に切り、節 3 を必要条件に緩めたもの）

`certified(A)` かつ `certified(Q)` かつ `Wup(A ++ Q^n, u) is False` が出たら**本物の反例**。
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import trio, r49

def lev(c): return 2 * c[1] + c[2]
def s(m): return ''.join('(%d,%d,%d)' % c for c in m)

def certified(M, u):
    """健全な下界: True なら本当に M in W u（緑の定理のみ）。"""
    if not M: return True
    if lev(M[0]) > u: return False
    if all(c[2] == 0 for c in M): return True            # zeroRow2_mem_Wself
    if len(M) == 2 and M[0][0] == 0: return True         # two_col_mem_W
    return r49.Wlo(M)                                    # 孤児の塔

def cols(maxval):
    return [(x, y, z) for x in range(maxval + 1) for y in range(maxval + 1) for z in (0, 1)]

def main(maxlenA=3, maxlenQ=3, maxval=2, nmax=3, N=2, depth=7, maxlen=16):
    C = cols(maxval)
    As = [(0, 0, 0)]
    pool = []
    for k in range(1, maxlenA + 1):
        for tail in itertools.product(C, repeat=k - 1):
            A = ((0, 0, 0),) + tail
            if certified(A, 0): pool.append(A)
    print('certified A: %d 本' % len(pool))
    tested = ce = 0
    for A in pool:
        for k in range(1, maxlenQ + 1):
            for Q in itertools.product([c for c in C if c[2] == 0], repeat=k):
                d = Q[0][0]
                if any(q[0] < d for q in Q): continue         # Q の根が最浅
                if not any(q[0] < d for q in A): continue     # open な場合だけ
                if not certified(Q, 0): continue
                for n in range(1, nmax + 1):
                    M = list(A) + list(Q) * n
                    if len(M) > maxlen: break
                    tested += 1
                    r = r49.Wup(M, 0, depth, {}, N, maxlen)
                    if r is False:
                        ce += 1
                        if ce <= 5:
                            print('★ 反例  A=%s  Q=%s  n=%d\n        A++Q^n=%s'
                                  % (s(A), s(Q), n, s(M)))
    print('判定 %d 件 / 反例 %d 件' % (tested, ce))

if __name__ == '__main__':
    main(*(int(a) for a in sys.argv[1:]))
