# -*- coding: utf-8 -*-
"""**`M ∉ W u` の健全な証明器**（課題 L47 / 2026-08-29）。

`PROOF-STATUS §4` の百万例は `inW` の退化で空虚だった（SESSION §25）。
`inW` の向きはこうである:

    inW = True   … 健全（節 2 が立てば所属する）。ただし**ほぼ必ず True** ⟹ 判別力ゼロ
    inW = False  … **健全でない**（節 3 を見ていないので、節 3 で所属するかもしれない）

⟹ 要るのは「所属の証明器」ではなく **「非所属の証明器」**。それは
**(W3) の対偶**で作れる（`lean/L47W.lean` で証明ずみ）:

    W3 : M ∈ W u → 2 ≤ |M| → (∀ n ≥ 1, M⟦n⟧ ∈ W u) ∨ M.dropLast ∈ W u

    対偶: 2 ≤ |M| ∧ (∃ n, M⟦n⟧ ∉ W u) ∧ **M.dropLast ∉ W u**  ⟹  **M ∉ W u**

## 底（`|M| <= 1`）

`lean/Trio.lean:98` の `oper` は **`j1 = 0` なら `M` を返す**（`[]` ではない）。
⟹ 1 列の節 2 は `M ∈ X` という自己参照で、**最小不動点では所属を与えない**。
残るのは節 1（`lev M 0 = 0`）と節 3（`domT M m` が `m = lev M 0 - 1 < u` を要求）。

    ⟹ **`lev M[0] > u`  ⟹  `M ∉ W u`**（健全。決定的）
    ⟹ `[] ∈ W u`（節 1。`|[]| = 0 <= 1`）

## 停止性

`M.dropLast` の側は長さが必ず減る。`M⟦n⟧` の側だけ `depth` で打ち切って **Unknown**。

使い方: python3 tools/refute.py            （自己検査 ＋ 陽性対照）
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio

NMAX = 4          # 節 2 の否定を探す n の範囲。増やすと反証が見つかりやすくなる
MAXLEN = 40


def lev(c):
    return 2 * c[1] + c[2]


def refute(M, u, depth=10, memo=None, nmax=NMAX):
    """**True なら `M ∉ W u` が証明された**（健全）。False / None は不明。"""
    if memo is None:
        memo = {}
    M = tuple(map(tuple, M))
    key = (M, u)
    if key in memo:
        return memo[key]
    if len(M) == 0:
        memo[key] = False                       # [] ∈ W u（節 1）
        return False
    if len(M) == 1:
        r = lev(M[0]) > u                       # 底。健全で決定的
        memo[key] = r
        return r
    if depth <= 0 or len(M) > MAXLEN:
        return None                             # 打ち切り。memo しない
    memo[key] = None                            # 循環は不明
    # 節 2 の否定: ∃ n >= 1, M⟦n⟧ ∉ W u
    hit = False
    for n in range(1, nmax + 1):
        T = tuple(map(tuple, trio.expand(list(M), n)))
        if T == M:                              # 自己参照（j1 = 0）は情報にならない
            continue
        if refute(T, u, depth - 1, memo, nmax) is True:
            hit = True
            break
    if not hit:
        memo[key] = None
        return None
    # (W3) の対偶: 節 3 は `M.dropLast ∈ W u` を含意するので、そこを潰せば節 3 も潰れる
    if refute(M[:-1], u, depth - 1, memo, nmax) is True:
        memo[key] = True
        return True
    memo[key] = None
    return None


def _selftest():
    import random
    from collections import Counter
    print('=== 陽性対照: `refute` が True を返す例が実在するか', flush=True)
    rng = random.Random(20260829)
    COLS = [(a, b, c) for a in range(6) for b in range(6) for c in range(2)
            if b <= a and c <= min(b, 1)]
    tot = Counter()
    ex = []
    memo = {}                       # **標本をまたいで共有**（無いと 5^depth で爆発する）
    for _ in range(4000):
        L = rng.randint(1, 6)
        M = tuple(rng.choice(COLS) for _ in range(L))
        u = rng.randint(0, 4)
        r = refute(M, u, 6, memo, NMAX)
        tot['True（∉ W u が証明された）' if r is True
            else ('False（∈ W u の側）' if r is False else '不明')] += 1
        if r is True and len(M) >= 2 and len(ex) < 5:
            ex.append((M, u))
    for k in sorted(tot):
        print('  %-30s %d' % (k, tot[k]), flush=True)
    print('  ⟹ 陽性対照は %s'
          % ('**効いている**' if tot['True（∉ W u が証明された）'] else
             '**効いていない。計器が無力**'), flush=True)
    print('  |M| >= 2 で反証できた例:', flush=True)
    for M, u in ex:
        print('    u=%d  M=%s' % (u, ''.join(map(str, M))), flush=True)

    print(flush=True)
    print('=== 健全性の対照: 行 2 ≡ 0 は `zeroRow2_mem_Wself` で `W (lev M 0)` に入る',
          flush=True)
    print('    ⟹ そこで `refute(M, lev M 0) = True` が出たら**計器のバグ**', flush=True)
    C0 = [(a, b, 0) for a in range(7) for b in range(7) if b <= a]
    bad = 0
    n = 0
    memo2 = {}
    for _ in range(4000):
        L = rng.randint(1, 6)
        M = tuple(rng.choice(C0) for _ in range(L))
        u = lev(M[0])
        n += 1
        if refute(M, u, 6, memo2, NMAX) is True:
            bad += 1
            if bad <= 3:
                print('    **バグの疑い** u=%d M=%s' % (u, ''.join(map(str, M))),
                      flush=True)
    print('  検査 %d 件 / **矛盾 %d 件**  ⟹ %s'
          % (n, bad, '**健全**' if bad == 0 else '**バグあり**'), flush=True)


if __name__ == '__main__':
    _selftest()
