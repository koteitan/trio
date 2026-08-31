"""変換器の性質 R を、シートの外（生成した全標準形）で測る。

性質 R: 任意の n に対し、ある m と n'>=n で 像<m> = 像(M<n'>)。
無限を有限で見るので「像の基本列が f(M<n>) に当たる回数」を数える。
当たりが散らばっていれば共終とみなす。

    python3 probeR.py [列数上限] [K] [列数の上限(打ち切り)]
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rule
from core import expand, show
from rows3 import gen3, key

CAP = 80          # これより長い行列は飛ばす（変換が重い）


def f(m):
    return tuple(rule.convert(tuple(m), 3))


def hits(M, K, cap=CAP):
    N = f(M)
    img = set()
    for m in range(1, K + 1):
        E = expand(N, m)
        if len(E) > cap:
            break
        img.add(tuple(E))
    out = []
    for n in range(1, K + 1):
        E = expand(M, n)
        if len(E) > cap:
            break
        if f(E) in img:
            out.append(n)
    return out


def main(lim, K):
    A = [M for M in sorted(gen3('BMS', lim, zcap=1), key=key) if len(M) > 1]
    t0 = time.time()
    bad = []
    for i, M in enumerate(A):
        h = hits(M, K)
        if len(h) < 3:
            bad.append((M, h))
        if (i + 1) % 2000 == 0:
            print('  %d/%d  違反 %d  (%.0fs)' % (i + 1, len(A), len(bad),
                                                time.time() - t0), flush=True)
    print('<=%d 列 %d 個: 当たり 3 回未満 %d  (%.0fs)'
          % (lim, len(A), len(bad), time.time() - t0))
    for M, h in bad[:10]:
        print('    %-36s 当たり %s -> %s' % (show(M), h, show(f(M))))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 5,
         int(sys.argv[2]) if len(sys.argv) > 2 else 10)
