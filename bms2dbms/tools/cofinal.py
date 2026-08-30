"""**ImgCofinalT の採点器** — Lean が実際に要求しているのはこちらである。

## なぜ `ImgClosedT` ではないのか

`lean/Dbms3.lean` の `ST_D3_conv3_of_parts` の仮定は commit 7faa432 で
`ImgClosedT3`（**すべての** m）から `ImgCofinalT3`（**いくらでも大きい** m）に
弱めてある:

    ImgCofinalT3 conv3 :=
      ∀ A, ST_TS A → 1 < |A| → ∀ m0, ∃ m >= m0, ∃ B, ST_TS B ∧ (conv3 A)⟦m⟧ = conv3 B

差を埋める補題（展開指数についての単調性）は `lean/Cofidx.lean` に証明ずみ:

    oper_mono_idx : j <= k → M⟦j⟧ = M⟦k⟧ ∨ seqlex (M⟦j⟧) (M⟦k⟧)

`ReindexT1_of_cofinal` は、`SandwichU` の n 版と `oper_mono_idx` を継いで
`conv3 (A⟦n⟧) <= (conv3 A)⟦n+1⟧ <= (conv3 A)⟦m⟧ = conv3 B` とするので、
**m は n+1 以上でありさえすればよい**。だから

    「A ごとに、逆像を持つ m の集合が**非有界**か」

が本当の要件である。`imgfast.py` が測っているのは「m<=3 の全部で逆像があるか」で、
**要件より強い**。

## 測り方

* **段 1**: 逆写像 `d2b3` を当てる。当たれば逆像 B を手に持っているので**確定**。
* 段 1 が m = m0..MMAX で 1 つも当たらない A だけを「非有界でない疑い」として残す。
  そこは `imgfast.find2` の探索に落とす（節点上限に当たったら「未判定」）。

## 実測（v16 sibnb, 2026-08-28）

`d2b3` が当たる m の並び（m = 1..16）を破れた A ごとに数えると:

    lim=6 の ImgClosedT(m<=3) の破れ 40 個
      O...............   27 個   m=1 だけ
      .OOOOOOOOOOOOOOO    7 個   **m>=2 が全部当たる ＝ 非有界 ＝ 要件は満たす**
      ................    5 個
      OO..............    1 個

⟹ **40 個のうち 7 個は `ImgCofinalT` では破れていない。**
`imgfast.py` の数字は要件より厳しい側に偏っている。

## 使い方

    python3 cofinal.py 5          lim=5
    python3 cofinal.py 6 16       lim=6, m<=16 まで見る
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rows3
from core import show, expand, isstd


def hits(A, mmax=16, f=None):
    """m = 1..mmax のうち逆像が**確定した** m の並び（'O' / '.'）。

    段 1 は `rows3.preimage_try`（`d2b3` ＋ 双子戻し ＋ 接頭辞の当て直し）を使う。
    素の `d2b3` だけだと `conv3` の版に追いつけず破れが水増しされる
    （lim=6 で 40 対 34、差の 6 個は `preimage_try` が**逆像を実際に持って**救出する。
    NOTES §課題 H13 の「基準線はひとつ」を読むこと）。
    """
    from inv3 import d2b3
    f = f or rows3.b2d3
    fA = f(list(A))
    out = []
    for m in range(1, mmax + 1):
        T = tuple(expand(tuple(map(tuple, fA)), m))
        out.append('O' if rows3.preimage_try(f, T, d2b3) is not None else '.')
    return ''.join(out)


def cofinal_ok(pat, tail=4):
    """並びの**末尾 `tail` 個がすべて当たり**なら非有界とみなす。
    `(conv3 A)⟦m⟧` は m について接頭辞の増加列なので、末尾が続けて当たるなら
    そのまま続く見込みが高い（証明ではない。上界の評価である）。"""
    return pat[-tail:] == 'O' * tail


def score(lim=5, mmax=16, imgmax=3, verbose=1, f=None):
    """(ImgClosedT の破れ, そのうち ImgCofinalT でも破れているもの) を返す。"""
    import imgfast, inv3
    f = f or rows3.b2d3
    t0 = time.time()
    r = imgfast.score(lim=lim, mmax=imgmax, verbose=0, f=f,
                      d2b3=(lambda T: rows3.preimage_try(f, T, inv3.d2b3)))
    bad = sorted(set(A for A, m, T in r.badpairs), key=rows3.key)
    still = []
    for A in bad:
        p = hits(A, mmax, f)
        if not cofinal_ok(p):
            still.append((A, p))
    if verbose:
        print('lim=%d  ImgClosedT(m<=%d) の破れ %d 個 -> '
              'そのうち **ImgCofinalT でも破れ** %d 個   (%.0fs)'
              % (lim, imgmax, len(bad), len(still), time.time() - t0))
        for A, p in still[:verbose * 8]:
            print('   %-52s %s' % (show(list(A)), p))
    return len(bad), still


if __name__ == '__main__':
    lim = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    mmax = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    score(lim, mmax)
