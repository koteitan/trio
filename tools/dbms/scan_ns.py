"""`conC` の像が DBMS 非標準になる**最小の** BMS 標準形を探す。

素朴に `gen` で全部作るとメモリが飛ぶ（`core` の isstd / expand のメモが
候補を全部抱えるため）。ここは

  * 標準形を長さごとに**流しながら**作る（全部は持たない）
  * 長さが変わるたびにメモを捨てる

の 2 つでメモリを一定に保つ。

使い方:
    python3 scan_ns.py [列数上限]
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core
from core import isstd, show
from rows2 import convC


def clear_memo():
    core._isstd_memo.clear()
    core._exp_memo.clear()
    core._flat_memo.clear()


def level(prev, ver):
    """長さ k の標準形から長さ k+1 の標準形を**流しながら**作る。"""
    for S in prev:
        amax = (S[-1][0] + 1) if S else 0
        for a in range(amax + 1):
            bmax = a if ver == 'BMS' else max(a - 1, 0)
            for b in range(bmax + 1):
                T = S + ((a, b),)
                if isstd(T, ver):
                    yield T


def main(lim=10):
    cur = [()]
    for k in range(1, lim + 1):
        last = (k == lim)
        bad, n = [], 0
        nxt = []
        for M in level(cur, 'BMS'):
            n += 1
            if not last:
                nxt.append(M)
            W = tuple(convC(list(M)))
            if not isstd(W, 'DBMS'):
                bad.append((M, W))
            if n % 200000 == 0:
                clear_memo()
        print('%2d 列: 標準形 %9d 個  像が DBMS 非標準 %d'
              % (k, n, len(bad)), flush=True)
        for M, W in bad[:5]:
            print('     ', show(M), '->', show(W), flush=True)
        clear_memo()
        if bad:
            return
        cur = nxt


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 10)
