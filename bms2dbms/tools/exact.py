"""f を ord の定義から**一意に**決める（2 行）。

鍵は BMS 系の展開の性質:

    極限行列 N について N[1] = N から末尾列を取ったもの

f は ord を保つ全単射なので f(M)[1] = f(M[1])、つまり

    M が極限なら  f(M) = f(M[1]) ++ [c]      （c は 1 列だけ）
    M が後続なら  f(M) = f(M - 末尾) ++ [(0,0)]

c は「f(M[1]) ++ [c] が DBMS 標準形で、{f(M[n])} の上界になる最小のもの」。
上界の判定は列の辞書式比較 cmpmat で閉じるので、シートも近似も要らない。

使い方:
    python3 exact.py [列数上限]
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import parse, show, expand, isstd, cmpmat, diagcol
from functools import lru_cache

K = 4        # 上界の判定に使う基本列の項数


def is_succ(m):
    return bool(m) and all(v == 0 for v in m[-1])


def cands(prev):
    """f(M[1]) = prev のあとに置ける列。DBMS の対角以下で、辞書式に小さい順。"""
    x = len(prev)
    out = []
    for a in range(x + 1):
        for b in range(min(a, 1) * (a - 1) + 1):      # DBMS: b <= max(a-1,0)
            out.append((a, b))
    out.sort()
    return out


@lru_cache(maxsize=None)
def f(M):
    if not M:
        return ()
    if is_succ(M):
        return f(M[:-1]) + ((0, 0),)
    prev = f(expand(M, 1))
    ub = [f(expand(M, n)) for n in range(2, K + 1)]
    for c in cands(prev):
        N = prev + (c,)
        if not isstd(N, 'DBMS'):
            continue
        if any(cmpmat(N, u) <= 0 for u in ub):
            continue
        return N
    raise RuntimeError('候補なし: ' + show(M))


def cofinal_ok(M, N, K2=3):
    """両側の共終性で検算する。"""
    if is_succ(M):
        return is_succ(N)
    if is_succ(N):
        return False
    fm = [f(expand(M, n)) for n in range(1, K2 + 1)]
    nn = [expand(N, m) for m in range(1, K2 + 1)]
    if any(cmpmat(a, N) >= 0 for a in fm):
        return False
    if cmpmat(nn[-1], fm[-1]) > 0:
        return False
    return True


def main(lim=7):
    from rows2 import gen, convC
    A = sorted(gen('BMS', lim), key=lambda m: (list(m), len(m)))
    print('BMS 2 行標準形 (<=%d 列): %d' % (lim, len(A)))
    img = {}
    diff = []
    for M in A:
        N = f(M)
        img[N] = M
        if tuple(convC(list(M))) != N:
            diff.append((M, tuple(convC(list(M))), N))
    print('  f != convC:', len(diff))
    for M, c, n in diff[:5]:
        print('    M   =', show(M))
        print('     convC=', show(c))
        print('     f    =', show(n))
    print('  単射:', len(img) == len(A))
    print('  共終性の検算 NG:', sum(1 for M in A if not cofinal_ok(M, f(M))))
    for k in range(3, lim + 1):
        D = gen('DBMS', k)
        miss = [d for d in D if d not in img]
        print('  DBMS <=%d 列: %d 個中 像に無い %d' % (k, len(D), len(miss)))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
