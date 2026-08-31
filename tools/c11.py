# -*- coding: utf-8 -*-
"""**(C11) の測定** —— 「`M` のすべての展開が行 2 ≡ 0 なら `M ∈ Wself`」の覆い。

    節 2: `∀ n >= 1, M⟦n⟧ ∈ X`
    (C2) `zeroRow2_mem_Wself`: 行 2 ≡ 0 ⟹ `Wself`

    ⟹ **すべての `M⟦n⟧` が行 2 ≡ 0 なら、節 2 の 1 段で `M ∈ Wself`**

**測度は要らず 1 段で終わる**ので、「行 2 の列の本数についての帰納」（課題 R34 で全滅）
とは別の話。課題 R34 の例がまさにこの形:

    M = (0,1,0)(1,4,0)(1,5,1)  ->  **M⟦2⟧ = (0,1,0)(1,4,0)(1,5,0)(2,8,0)**  行 2 が全部 0


## ★ 結果（2026-08-29）—— **(C11) は `snoc_zeroRow2` の言い換え。新しい証明書ではない**

    標本 20000（長さ 2..6）。行 2 に 1 がある `M`: **17020**
    **(C11) が当たる 2213 / 17020（13.00%）**
    当たらない 14807 は**全部 `n = 1` で行 2 が残る**

**退化検査（決定的）:**

    (C11) が当たる 2213 個のうち
    **「行 2 = 1 が末尾だけ」（＝ `snoc_zeroRow2` の範囲）: 2213（100.00%）**
    **末尾だけでない当たり: 0**
    逆に「末尾だけ」の 2213 個は**全部**当たる（100%）

⟹ **(C11) ⟺ `snoc_zeroRow2`。** 機構も同じ（`j1 = |M|-1` はコピーされるブロックに
入らないので、末尾の行 2 = 1 の列だけが展開で消える）。**8 本目の証明書にはならない。**

⟹ **L2 の分析（課題 L49）が正しかった**: 行 2 = 1 の列を**途中**に置くと、
その列が悪い部分に入った瞬間にコピーで複製されるので、`n = 1` で既に残る。

使い方: python3 tools/c11.py [標本数] [N]
"""
import sys, random
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio


def row2ok(M):
    return all(c[2] == 0 for c in M)


def main(NS=20000, N=5):
    rng = random.Random(20260829)
    COLS = [(a, b, c) for a in range(6) for b in range(6) for c in range(2)
            if b <= a and c <= min(b, 1)]
    tot = Counter()
    firstbad = Counter()
    ex = []
    n2 = 0
    for _ in range(NS):
        L = rng.randint(2, 6)
        M = tuple(rng.choice(COLS) for _ in range(L))
        if row2ok(M):
            tot['もとから行 2 ≡ 0（(C2) で自明）'] += 1
            continue
        n2 += 1
        bad = None
        for n in range(1, N + 1):
            T = tuple(map(tuple, trio.expand(list(M), n)))
            if T == M:                      # 自己参照（|M| <= 1）
                bad = 'self'
                break
            if not row2ok(T):
                bad = n
                break
        if bad is None:
            tot['**(C11) が当たる**'] += 1
            if len(ex) < 5:
                ex.append(M)
        else:
            tot['当たらない'] += 1
            firstbad[bad] += 1
    print('標本 %d（長さ 2..6、行1<=行0、行2<=min(行1,1)）  N = %d' % (NS, N))
    print('  行 2 に 1 がある `M`: **%d**' % n2)
    for k in sorted(tot, key=lambda x: -tot[x]):
        print('  %-34s %d' % (k, tot[k]))
    if n2:
        c = tot['**(C11) が当たる**']
        print('  ⟹ **行 2 に 1 がある `M` のうち (C11) が当たる: %d / %d（%.2f%%）**'
              % (c, n2, 100.0 * c / n2))
    print('  当たらない `M` で行 2 が最初に残る n:', dict(sorted(firstbad.items(),
          key=lambda x: (str(x[0])))))
    for M in ex:
        T = tuple(map(tuple, trio.expand(list(M), 2)))
        print('   当たる例 M=%s' % ''.join(map(str, M)))
        print('            M⟦2⟧=%s' % ''.join(map(str, T)))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 20000,
         int(sys.argv[2]) if len(sys.argv) > 2 else 5)
