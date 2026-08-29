# -*- coding: utf-8 -*-
"""**課題 H47 —— 「上限 3」の手順を明示し、行数 `Y` を振って確かめる。**

## H44-c で私が数えたもの（擬似コード）

    k = 0
    X = M
    loop:
        n  = |X| - 1                       # 末尾の列
        t  = srow(X, n)                    # 非零最下行
        r0 = parent(X, t, n)               # X のバッドルート
        if r0 is None: break               # 孤児 ⟹ 打ち切り
        blk = X[r0 : n]                    # **段（末尾の列は含まない）**、幅 b = n - r0
        E   = X⟦2⟧
        r1  = parent(E, srow(E, |E|-1), |E|-1)      # X⟦2⟧ のバッドルート
        if r1 is not None and r1 >= r0 + b:
            break                          # **新しい段の中 ⟹ 復活しない。ここで止める**
        k = k + 1
        X = E
    return k

**要点は 2 つ:**
  1. 判定は「`X⟦2⟧` のバッドルートが**新しい段の中**にあるか」（`X` 自身ではなく展開後を見る）
  2. **復活しない段が 1 つ出たらそこで止める** ⟹ 数えているのは
     **先頭からの「連続」復活回数**であって、鎖全体の総数ではない

`H1-NOTES.md` §86 の見出しも「**連続**して復活する回数」と書いてある。
リードの手順は (2) が違い、**10 段ぶんの総数**を数えている ⟹ 最大 6 になるのは当然。
"""
import sys, io, contextlib, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter

MAXL = 4000


def srowG(S, j):
    """一般の行数での `srow`（非零最下行）。"""
    c = S[j]
    for y in range(len(c) - 1, -1, -1):
        if c[y] > 0:
            return y
    return 0


def step(X):
    """(復活したか, X⟦2⟧) を返す。判定できなければ (None, None)。"""
    X = [tuple(c) for c in X]
    n = len(X) - 1
    if n < 0:
        return None, None
    r0 = trio.parent(X, srowG(X, n), n)
    if r0 is None:
        return None, None
    b = n - r0
    E = [tuple(c) for c in trio.expand(list(X), 2)]
    if len(E) > MAXL:
        return None, None
    m = len(E) - 1
    r1 = trio.parent(E, srowG(E, m), m)
    esc = not (r1 is not None and r1 >= r0 + b)
    return esc, E


def krun(M, cap=12):
    """**連続**復活回数（H44-c の数え方）。"""
    X = [tuple(c) for c in M]
    k = 0
    while k < cap:
        esc, E = step(X)
        if esc is None or not esc:
            break
        k += 1
        X = E
    return k


def ktot(M, steps=10):
    """**鎖 `steps` 段ぶんの総数**（リードの数え方）。"""
    X = [tuple(c) for c in M]
    k = 0
    for _ in range(steps):
        esc, E = step(X)
        if esc is None:
            break
        if esc:
            k += 1
        X = E
    return k


def pool(Y, vmax, maxlen, ns=(1, 2, 3)):
    """`diag(Y, v)` からの展開閉包（一般行数の標準形）。"""
    seen, fr = set(), []
    for v in range(vmax + 1):
        S = tuple(tuple(c) for c in trio.diag(Y, v))
        if S and S not in seen:
            seen.add(S)
            fr.append(S)
    while fr:
        S = fr.pop()
        for n in ns:
            T = tuple(tuple(c) for c in trio.expand(list(S), n))
            if T and len(T) <= maxlen and T not in seen:
                seen.add(T)
                fr.append(T)
    return sorted(seen, key=lambda s: (len(s), s))


if __name__ == '__main__':
    print(__doc__)
    print('=' * 62)
    print('**行数 `Y` を振って「連続復活回数」の上限を測る**')
    print('母集団は `trio.diag(Y, v)` からの展開閉包（一般行数の標準形）')
    print()
    print('| `Y`（行数）| 母数 | 分布 | **上限** |')
    print('|--:|--:|---|--:|')
    for Y, vmax, maxlen in ((1, 6, 12), (2, 4, 11), (3, 4, 10), (4, 3, 10)):
        t0 = time.time()
        P = pool(Y, vmax, maxlen)
        c = Counter(krun(M) for M in P)
        mx = max(c)
        print('| %d | %d | %s | **%d** |'
              % (Y, len(P), dict(sorted(c.items())), mx))
    print()
    print('**参考: リードの数え方（鎖 10 段ぶんの総数）でも測る**')
    print('| `Y` | 母数 | 分布 | 最大 |')
    print('|--:|--:|---|--:|')
    for Y, vmax, maxlen in ((1, 6, 12), (2, 4, 11), (3, 4, 10), (4, 3, 10)):
        P = pool(Y, vmax, maxlen)
        c = Counter(ktot(M) for M in P)
        print('| %d | %d | %s | %d |'
              % (Y, len(P), dict(sorted(c.items())), max(c)))
