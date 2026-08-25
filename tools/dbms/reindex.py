"""REINDEX 予想の検査。

  (conC M)[m] = conC (M[g(M,m)])            … 像閉包 + 基本列の関係

を BMS 標準形の全域（列数上限まで）で確かめ、g の regime を数える。
regime は 4 つしかないと予想している:

  succ  : M の末尾列 = (0,0)          -> g(m) = 0
  shift : M の末尾列 = (1,1)          -> g(1) in {1,2}, g(m) = m+1 (m>=2)
  contr : 末尾で縮約が効いた場合       -> g(m) = m-1
  id    : それ以外                    -> g(m) = m

使い方: python3 reindex.py [列数上限] [m の上限]
"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core
from core import expand, show
from rows2 import gen, convC, readC, untranslate


def back(N):
    return tuple(untranslate(readC(list(N))))


def gval(M, W, m, nmax=16):
    E = expand(W, m)
    if not E:
        return None
    Mp = back(E)
    if tuple(convC(list(Mp))) != E:
        return 'NOTIMG'
    for n in range(0, nmax):
        if tuple(expand(M, n)) == Mp:
            return n
    return 'NOFS'


def main(lim=8, K=4):
    A = gen('BMS', lim)
    reg = collections.Counter()
    bad = []
    for i, M in enumerate(A):
        if i % 20000 == 0:
            core._exp_memo.clear(); core._flat_memo.clear()
        if len(M) <= 1:
            continue
        W = tuple(convC(list(M)))
        g = tuple(gval(M, W, m) for m in range(1, K + 1))
        if any(isinstance(x, str) for x in g):
            bad.append((M, W, g)); continue
        if all(x == 0 for x in g):
            reg['succ' if M[-1] == (0, 0) else 'succ?'] += 1
        elif all(g[m - 1] == m for m in range(1, K + 1)):
            reg['id'] += 1
        elif all(g[m - 1] == m + 1 for m in range(2, K + 1)):
            reg['shift' if M[-1] == (1, 1) else 'shift?'] += 1
        elif all(g[m - 1] == m - 1 for m in range(1, K + 1)):
            reg['contr'] += 1
        else:
            reg['other' + str(g)] += 1
    print("lim=%d  標準形 %d  regime %s  違反 %d"
          % (lim, len(A), dict(reg), len(bad)))
    for M, W, g in bad[:8]:
        print("   NG M=", show(M), " conC M=", show(W), " g=", g)
    return len(bad)


if __name__ == '__main__':
    lim = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    K = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    sys.exit(1 if main(lim, K) else 0)
