"""tools/trio.py の BM4 モデルの検証。

    python3 tools/verify_trio.py

検査項目
  1. Y=2 で、数式的定義のペア数列規則（一様上昇・A なし）と、標準形の
     到達集合上で完全一致すること
  2. (0,0,0)(1,1,1)[n] = 2 行対角列の z=0 埋め込み
  3. (0,0,0)(1,1,1)(2,2,2)[n] = z 頭打ち対角列（z<2 断片の生成元）
  4. psi(I) 行列の展開が BM4-Analysis シートの塔行列と一致すること
  5. z<2 は展開で閉じていること（生成元からの BFS 全体で z <= 1）
  6. A 行列が効く例（一様上昇と BM4 が異なる標準形）の探索
"""

from __future__ import annotations

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from trio import expand, diag, parent  # noqa: E402


def pair_expand(S, n):
    """数式的定義のペア数列の節そのもの（一様上昇・A なし）。"""
    if not S:
        return []
    x = len(S) - 1
    if S[x] == (0, 0):
        return list(S[:x])
    if S[x][1] != 0:
        r = parent(S, 1, x)
    else:
        r = parent(S, 0, x)
    if r is None:
        return list(S[:x])
    d0 = S[x][0] - S[r][0] if S[x][1] != 0 else 0
    out = list(S[:r])
    for a in range(n):
        out += [(S[r + xx][0] + a * d0, S[r + xx][1]) for xx in range(x - r)]
    return out


def bfs(seeds, ns, depth):
    """seeds から n ∈ ns の展開を depth 段まで。到達集合を返す。"""
    seen = set()
    frontier = [tuple(s) for s in seeds]
    for _ in range(depth):
        nxt = []
        for S in frontier:
            if S in seen:
                continue
            seen.add(S)
            for n in ns:
                T = tuple(expand(list(S), n))
                if T not in seen:
                    nxt.append(T)
        frontier = nxt
    seen.update(frontier)
    return seen


def main():
    ok = True

    # 1. ペア規則との一致
    reach = bfs([diag(2, v) for v in range(4)], ns=(1, 2, 3), depth=5)
    bad = [S for S in reach
           if [tuple(c) for c in expand(list(S), 3)] != pair_expand(list(S), 3)]
    print('1. pair agreement   : %d standard forms, %d mismatch' % (len(reach), len(bad)))
    ok &= not bad

    # 2. (0,0,0)(1,1,1)[n]
    got = expand([(0, 0, 0), (1, 1, 1)], 4)
    want = [(k, k, 0) for k in range(4)]
    print('2. seed[4]          :', got, 'ok' if got == want else 'NG')
    ok &= got == want

    # 3. (0,0,0)(1,1,1)(2,2,2)[n] = z 頭打ち対角列
    got = expand([(0, 0, 0), (1, 1, 1), (2, 2, 2)], 4)
    want = diag(3, 4, zcap=1)
    print('3. full-diag[4]     :', got, 'ok' if got == want else 'NG')
    ok &= got == want

    # 4. psi(I) 行列の塔展開（BM4-Analysis 行 2193 / 4392）
    psiI = [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (2, 0, 0)]
    block = [(1, 1, 1), (2, 1, 1), (3, 1, 0)]
    w1 = [(0, 0, 0)] + block                    # psi(W_W)
    w2 = [(0, 0, 0)] + block + block            # psi(W_W_W)
    g1, g2 = expand(psiI, 1), expand(psiI, 2)
    print('4. psi(I)[1]        :', g1, 'ok' if g1 == w1 else 'NG')
    print('   psi(I)[2]        :', g2, 'ok' if g2 == w2 else 'NG')
    ok &= g1 == w1 and g2 == w2

    # 5. z<2 の閉性
    reach3 = bfs([diag(3, v, zcap=1) for v in range(4)], ns=(1, 2, 3), depth=4)
    zbad = [S for S in reach3 for c in S if c[2] >= 2]
    print('5. z<2 closure      : %d reachable, %d violations' % (len(reach3), len(zbad)))
    ok &= not zbad

    # 6. A 行列が効く例
    def expand_uniform(S, n):
        if not S:
            return []
        x = len(S) - 1
        Y = len(S[0])
        if all(v == 0 for v in S[x]):
            return list(S[:x])
        t = max(y for y in range(Y) if S[x][y] > 0)
        r = parent(S, t, x)
        if r is None:
            return list(S[:x])
        delta = [(S[x][y] - S[r][y]) if y < t else 0 for y in range(Y)]
        out = list(S[:r])
        for a in range(n):
            out += [tuple(S[r + xx][y] + a * delta[y] for y in range(Y))
                    for xx in range(x - r)]
        return out

    diffs = [S for S in sorted(reach3)
             if expand(list(S), 3) != expand_uniform(list(S), 3)]
    print('6. A-matrix matters : %d/%d standard forms differ from uniform ascension'
          % (len(diffs), len(reach3)))
    for S in diffs[:2]:
        print('   ex:', list(S))
        print('     BM4     :', expand(list(S), 2))
        print('     uniform :', expand_uniform(list(S), 2))

    print('ALL OK' if ok else 'FAILURES ABOVE')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
