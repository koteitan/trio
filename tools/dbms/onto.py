"""convC の全射性を、列数の上限に惑わされずに確かめる。

BMS の逆像は像より**長い**ことがある。例:

    N  = (0,0)(1,0)(2,1)(2,1)(2,1)(2,0)                              6 列
    P* = (0,0)(1,1)(1,1)(1,1)(1,0)(2,1)(2,1)(2,1)(2,0)               9 列

なので「BMS を k 列まで生成して DBMS の k 列を覆えるか」を見ると、
覆えないものが大量に出る。それは全射でないことの証拠にならない。

ここでは逆像を**構成**する。極限 N について、N の基本列は
「N[1] のうしろに悪い部分をぶら下げて繰り返す」形なので、
N[2] の逆像 Q が分かれば、逆像は Q に 1 列足したものになる。

    P* = Q ++ [c]     c は BMS の列（有限個の候補から選ぶ）

使い方:
    python3 onto.py [DBMS の列数上限] [BMS の生成上限]
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import show, isstd, expand
from rows2 import gen, convC


def is_succ(m):
    return bool(m) and all(v == 0 for v in m[-1])


def cand_cols(Q):
    """BMS の列の候補（対角以下）。"""
    x = len(Q)
    return [(a, b) for a in range(x + 1) for b in range(a + 1)]


def preimage(N, img, depth=0):
    """N の逆像。`img` は既知の像 -> 逆像の辞書。"""
    if N in img:
        return img[N]
    if not N or depth > 8:
        return None
    if is_succ(N):
        Q = preimage(N[:-1], img, depth + 1)
        return None if Q is None else Q + ((0, 0),)
    Q = preimage(expand(N, 2), img, depth + 1)
    if Q is None:
        return None
    for c in cand_cols(Q):
        P = Q + (c,)
        if isstd(P, 'BMS') and tuple(convC(list(P))) == N:
            return P
    return None


def main(dlim=7, blim=8):
    A = gen('BMS', blim)
    img = {}
    for M in A:
        img[tuple(convC(list(M)))] = M
    print('BMS 標準形 (<=%d 列): %d  -> 像 %d 個' % (blim, len(A), len(img)))
    for k in range(3, dlim + 1):
        D = sorted(gen('DBMS', k), key=lambda m: (list(m), len(m)))
        direct = [N for N in D if N not in img]
        built, fail = 0, []
        for N in direct:
            P = preimage(N, img)
            if P is not None:
                built += 1
                img[N] = P
            else:
                fail.append(N)
        print('  DBMS <=%d 列: %d 個  直接ヒット %d  逆像を構成 %d  未解決 %d'
              % (k, len(D), len(D) - len(direct), built, len(fail)))
        for N in fail[:3]:
            print('     未解決:', show(N))


if __name__ == '__main__':
    a = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    b = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    main(a, b)
