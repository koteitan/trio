# -*- coding: utf-8 -*-
"""**`inW` が退化していないかの監査**（課題 H35 の一般化、2026-08-29）。

課題 H35 で `probe_snoc.py` の `minstage(S)` が **`lev(S[0])` と同じ**と判明した。
原因は `inW` が Lean の `Aop`（`lean/Wset.lean:171`）の 3 節のうち**第 2 節しか
模していない**こと（第 3 節 = graft の節が段 `u` の本体）。

    27 個のプローブが同じ `inW` を使い、ほぼ全部が graft を落としている。

⟹ **`PROOF-STATUS §4` の「違反 0」が軒並み空虚かもしれない。** ここで直に測る:

    仮説 H:  inW(S, a) is True  ⟺  lev(S[0]) <= a

**H が真なら、この計器は「第 0 列の段」しか見ていない。**
`W` の中身（展開も塔も置換も）を一切測っていないことになる。

使い方: python3 tools/inw_audit.py [標本数]
"""
import sys, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio

NS = (1, 2)
MAXD = 9
MAXLEN = 34


def lev(col):
    return 2 * col[1] + col[2]


def inW(S, a, depth, memo):
    S = tuple(tuple(c) for c in S)
    key = (S, a)
    if key in memo:
        return memo[key]
    if len(S) == 0:
        return True
    if len(S) == 1:
        r = lev(S[0]) <= a
        memo[key] = r
        return r
    if depth <= 0 or len(S) > MAXLEN:
        return None
    memo[key] = None
    out = True
    for n in NS:
        r = inW(trio.expand(list(S), n), a, depth - 1, memo)
        if r is False:
            memo[key] = False
            return False
        if r is None:
            out = None
    memo[key] = out
    return out


def main(N=20000):
    rng = random.Random(20260829)
    memo = {}
    agree = dis = und = 0
    ex = []
    # 標本は**ランダム**。列の値も長さも広く取る（教訓 11）
    for _ in range(N):
        L = rng.randint(1, 7)
        S = []
        for _ in range(L):
            x = rng.randint(0, 5)
            y = rng.randint(0, x)
            z = rng.randint(0, min(y, 1))
            S.append((x, y, z))
        a = rng.randint(0, 12)
        r = inW(S, a, MAXD, memo)
        if r is None:
            und += 1
            continue
        pred = lev(S[0]) <= a
        if r == pred:
            agree += 1
        else:
            dis += 1
            if len(ex) < 6:
                ex.append((S, a, r, pred))
    tot = agree + dis
    print('標本 %d（ランダム。長さ 1..7、行 0 は 0..5、行1<=行0、行2<=min(行1,1)）' % N)
    print('  判定できた %d / 未判定 %d' % (tot, und))
    print('  **inW(S,a) == (lev(S[0]) <= a) が成り立つ: %d / %d（%.2f%%）**'
          % (agree, tot, 100.0 * agree / max(1, tot)))
    print('  食い違い **%d**' % dis)
    if dis == 0:
        print('  ⟹ **この計器は第 0 列の段しか見ていない。W の中身を測っていない。**')
    else:
        print('  ⟹ **退化していない。食い違う例:**')
        for S, a, r, p in ex:
            print('     S=%s a=%d  inW=%s  lev(S[0])<=a=%s' % (S, a, r, p))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 20000)
