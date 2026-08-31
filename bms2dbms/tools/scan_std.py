"""修正版 convC の像が DBMS 標準形かを、列数上限まで全数走査する。

`scan_ns.py` は旧 convC（sibRun 版）用。こちらは `rows2.convC`（units_split 版）。
メモリのため `gen` は使わず、接頭辞延長でストリーム生成する。

使い方: python3 scan_std.py [列数上限]
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core
from core import isstd, show
from rows2 import convC


def level(prev, lim):
    """BMS 標準形を 1 列ずつ延ばして流す。"""
    for M in prev:
        if len(M) >= lim:
            continue
        last = M[-1]
        for a in range(0, last[0] + 2):
            for b in range(0, a + 1):
                N = M + ((a, b),)
                if isstd(N, 'BMS'):
                    yield N


def main(lim=9):
    cur = [((0, 0),)]
    total = 0
    for depth in range(1, lim):
        nxt = []
        cnt = 0
        for M in level(cur, lim):
            cnt += 1
            W = tuple(convC(list(M)))
            if not isstd(W, 'DBMS'):
                print("非標準!", show(M), "->", show(W))
                return 1
            nxt.append(M)
            if cnt % 100000 == 0:
                core._isstd_memo.clear(); core._exp_memo.clear(); core._flat_memo.clear()
        total += cnt
        print("  %2d 列: %d 個  (累計 %d)" % (depth + 1, cnt, total), flush=True)
        cur = nxt
        core._isstd_memo.clear(); core._exp_memo.clear(); core._flat_memo.clear()
    print("<=%d 列 %d 個すべて像が DBMS 標準形" % (lim, total + 1))
    return 0


if __name__ == '__main__':
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 9))
