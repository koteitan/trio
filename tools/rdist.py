# -*- coding: utf-8 -*-
"""**`WSnoc` の悪い根 `r` の分布**（課題 L47、L2 の依頼）。

L2 の解析:

    (C ++ [p])⟦n⟧ = C.take r ++ **shTower (C.drop r) δ n**
    r >= 1  … `C.drop r` は `C` より真に短い ⟹ **長さの帰納で落ちる**
    r = 0   … 目標が `shTower C δ n ∈ W u` ＝ **`C` 自身の (TOW)** ⟹ **循環**

⟹ **`r = 0` が起きるかどうかで `WSnoc` の証明の可否が決まる。**

母集団は 2 つ:
  (a) ランダムな `C`（広いが `W u` とは限らない）
  (b) **`Wlo` が立つ孤児の塔**（`C ∈ W u` が確定。`WSnoc` の前提そのもの）

陽性対照: `r = |C|-1`（親が末尾）の割合も出す。**両方鳴るはず。**

使い方: python3 bms2dbms/tools/rdist.py [標本数]
"""
import sys, random
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def lev(c):
    return 2 * c[1] + c[2]


def is_orphan_step(M):
    """`oper` が `Pred M` を返す枝（最後の列が零 または 親が無い）。"""
    j = len(M) - 1
    if all(v == 0 for v in M[j]):
        return True
    return trio.parent(list(M), srow(M, j), j) is None


def wlo(M):
    """`Wlo`（True が健全）: 孤児の塔。"""
    M = list(M)
    while len(M) >= 2:
        if not is_orphan_step(M):
            return False
        M = M[:-1]
    return len(M) == 0 or lev(M[0]) == 0


def report(pairs, tag):
    cr = Counter()
    based0 = notbased0 = 0
    n1 = 0
    for C, p, r in pairs:
        cr[r] += 1
        if r == 0:
            if C[0][0] == 0: based0 += 1
            else: notbased0 += 1
        if r == len(C) - 1: n1 += 1
    tot = len(pairs)
    print('=== %s  親のある (C,p) **%d 組**' % (tag, tot), flush=True)
    if not tot:
        return
    print('  r の分布: %s' % dict(sorted(cr.items())), flush=True)
    print('  **r = 0（p の親が C の先頭）: %d / %d（%.2f%%）**'
          % (cr[0], tot, 100.0 * cr[0] / tot), flush=True)
    print('    うち C が基づく（C[0][0] == 0）: **%d** / 基づかない: %d'
          % (based0, notbased0), flush=True)
    print('  陽性対照 r = |C|-1（親が末尾）: **%d / %d（%.2f%%）**'
          % (n1, tot, 100.0 * n1 / tot), flush=True)
    print('  ⟹ %s' % ('**r = 0 は起きない ⟹ 長さの帰納だけで落ちる見込み**'
                      if cr[0] == 0 else
                      '**r = 0 が起きる ⟹ その枝は (TOW) と循環**'), flush=True)


def main(N=200000):
    rng = random.Random(20260829)
    COLS = [(a, b, c) for a in range(6) for b in range(6) for c in range(2)
            if b <= a and c <= min(b, 1)]
    rnd, tow = [], []
    for _ in range(N):
        L = rng.randint(1, 8)
        C = tuple(rng.choice(COLS) for _ in range(L))
        p = rng.choice(COLS)
        S = list(C) + [p]
        r = trio.parent(S, srow(S, len(C)), len(C))
        if r is None:
            continue
        rnd.append((C, p, r))
        if wlo(C):
            tow.append((C, p, r))
    report(rnd, 'ランダムな C')
    print(flush=True)
    report(tow, '**Wlo が立つ C（C ∈ W u が確定。WSnoc の前提そのもの）**')


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 200000)
