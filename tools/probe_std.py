# -*- coding: utf-8 -*-
"""(STD) の反証器。

狙う文（koteitan の提案の簡約版 —— 接尾辞の条件を落として標準形だけにする）:

    X in W u,  X ++ C が標準形  ==>  X ++ C in W u

両側とも健全に挟む:
  下界（True が健全）  緑の定理のみ: zeroRow2 / two_col_mem_W / 孤児の塔（r49.Wlo）
  上界（False が健全）  r49.Wup

`certified(X)` かつ `Wup(X ++ C, u) is False` なら**本物の反例**。
"""
import sys, os, itertools, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import trio, r49

BMS = os.path.expanduser('~/code/yaBMS/c/bms')

def lev(c): return 2 * c[1] + c[2]
def s(m): return ''.join('(%d,%d,%d)' % c for c in m)
def standard(m):
    return subprocess.run([BMS, '-s', s(m)], capture_output=True, text=True).stdout.strip() == '1'

def certified(M, u):
    if not M: return True
    if lev(M[0]) > u: return False
    if all(c[2] == 0 for c in M): return True
    if len(M) == 2 and M[0][0] == 0: return True
    return r49.Wlo(M)

def ge(B, C):
    """列の辞書式で B >= C か。"""
    for b, c in zip(B, C):
        if b != c: return b > c
    return len(B) >= len(C)

def main(maxX=4, maxC=3, maxval=3, N=2, depth=7, maxlen=16):
    cols = [(x, y, z) for x in range(maxval + 1) for y in range(maxval + 1) for z in (0, 1)]
    Xs = []
    for k in range(1, maxX + 1):
        for tail in itertools.product(cols, repeat=k - 1):
            X = ((0, 0, 0),) + tail
            if certified(X, 0) and standard(list(X)): Xs.append(X)
    print('certified かつ標準形の X: %d 本' % len(Xs))
    tested = ce = 0
    for X in Xs:
        for k in range(1, maxC + 1):
            for C in itertools.product(cols, repeat=k):
                M = list(X) + list(C)
                if len(M) > maxlen: continue
                if not standard(M): continue
                tested += 1
                if r49.Wup(M, 0, depth, {}, N, maxlen) is False:
                    ce += 1
                    if ce <= 6:
                        print('★ 反例  X=%s  C=%s\n        X++C=%s' % (s(X), s(C), s(M)))
    print('判定 %d 件 / 反例 %d 件' % (tested, ce))

if __name__ == '__main__':
    main(*(int(a) for a in sys.argv[1:]))
