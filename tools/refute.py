# -*- coding: utf-8 -*-
"""**⛔ この計器も退化していた。使わないこと**（課題 R33 / R1 が発見、2026-08-29）。

    **refute(M, u) == (lev M[0] > u)  が 4328 / 4328（食い違い 0）**

`inw_audit.py` を自分自身に当てて確認した。**`inW` とまったく同じ穴。**

## 原因は測定ではなく**構造**（定理）

`W` の定義に現れる操作は `oper`（節 2）／`Pred`／`graft`（節 3）の 3 つだけで、
**そのすべてが第 0 列を変えない**（R1 が乱択 60000 行列で確認。例外 0）:

    Pred M    = M.dropLast                      -> M[0] は残る
    graft M z = M.dropLast ++ (z を持ち上げ)     -> M[0] は残る
    M⟦n⟧      = M.take j0 ++ (ブロックの n 個の写し)
                j0 >= 1 なら take の先頭が M[0]／j0 = 0 なら k=0 の写しが持ち上げ 0
                j1 = 0 なら M そのもの

⟹ **健全な反証器の再帰で到達するどの行列も `M[0]` が同じ**
⟹ 底（`lev M[0] > u`）が鳴るかは**最初から決まっている**
⟹ **`lev M[0] > u` 以外は何も証明できない。**

## さらに: 反証型は**原理的に**届かない（教訓 13 の 3 例目）

`lev M[0] <= u` のとき `M ∉ W u` は、`W` が最小不動点であることから
**「`M` から始まる展開が停止しない」と実質同値**。それはいま証明しようとしている
ことの否定そのもの。⟹ **停止性が真なら、どんな健全な反証器も永遠に鳴らない。**

## ⚠ チームリードの対照は退化を検出できなかった

    陽性対照   4000 件中 2669 件で反証 ⟹ 「効いている」と読んだ
    健全性対照 行 2 ≡ 0 で矛盾 0 ⟹ 「健全」と読んだ

**どちらも通ったのは、計器が退化していた**からである
（2669 件は全部 `lev M[0] > u`、行 2 ≡ 0 の族は `u = lev M 0` なので絶対に鳴らない）。

> **教訓 12 の追記: 対照が鳴っただけでは足りない。
> 「計器が自明な関数と一致していないか」を必ず直に測る**（`inw_audit.py` の形）。
> **新しい計器を作ったら、その計器自身に `inw_audit` を当てること。**

以下は記録として残す（実装は正しいが、測れる量が `lev M[0] > u` しかない）。
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
