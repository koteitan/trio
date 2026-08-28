# -*- coding: utf-8 -*-
"""**`M ∈ W u` / `M ∈ Wself` の証明書**（2026-08-29、課題 R45）。

当たれば **Lean で証明ずみの定理から所属が出る**。外れても**非所属ではない**
（証明書が届かないだけ）。⟹ 「届かない」は反例ではない。

    from wcert import wcert, wcat_cert, audit, marginal
    wcert(M)            # -> 証明書の名前（str）または None。u 省略時は `Wself`
    wcert(M, u)         # -> `M ∈ W u` の証明書
    wcat_cert(A, B)     # -> `A ++ B` の証明書（(C10)(C11) 込み）

## 段は `lev M 0` しか運んでいない（これが全体の土台）

    `mem_Wself_iff`（`lean/Wtower2.lean:2991`）:
        **M ∈ W u  ↔  M ∈ Wself ∧ lev M 0 ≤ u**       Wself = {M | M ∈ W (lev M 0)}
    `lev_root_le_of_mem_W`（`lean/Wset.lean:2161`）:  M ∈ W u → M ≠ [] → lev M 0 ≤ u

⟹ **`W u` の判定は「`Wself` か」＋「`lev M 0 ≤ u` か」に分かれる。**
この module は `Wself` の側だけを扱い、`u` は最後に `lev M 0 <= u` で見る。

## 証明書の一覧（すべて Lean で証明ずみ）

    (C1)  `singleton_mem_W`      `lean/Wchar.lean:99`     |M| <= 1
          （`[(d,v,z)] ∈ W a ⟺ 2v+z <= a`。`[] ∈ W u` は `W_nil`、`Wset.lean:259`）
    (C2)  `zeroRow2_mem_Wself`   `lean/Wtower2.lean:2985` 行 2 ≡ 0
    (C3)  `flat_mem_W`           `lean/Wtower2.lean:257`  行 0 ≡ 0
    (C5') `snoc_zeroRow2`        `lean/Wtower2.lean:3127` 行 2 ≡ 0 ＋ **任意の 1 列**
    (C6') `snoc_orphan`          `lean/Wtower2.lean:3053` **任意の証明書** ＋ 孤児。繰り返せる
    (C7') `dropLast_mem_Wself`   `lean/Wtower2.lean:3077` 下向きの閉包（構成には使わない）
    (C8)  `W_shift`              `lean/Wset.lean:1320`    行 0 のシフトは段を上げない
    (C9)  `oper_closed`          `lean/Wset.lean:2103`    M ∈ W u → M⟦n⟧ ∈ W u
    (C10) `W_flatMap_copies`     `lean/Wset.lean:2552`    同じ Q を n 個並べる
    (C11) `W_add`                `lean/Wset.lean:1682`    A ++ B、側条件 `rsum A B`
          `rsum A B : ∀ p ∈ A ++ B, entry B 0 0 ≤ p.1`（**B の根が A++B 全体で最浅**）

    （旧 (C4)「孤児の塔」は (C1) を底にした (C6') の特別な場合なので、独立には持たない。）

## ⚠ 実装上の落とし穴（実際に踏んだ）

**(C5') は接頭辞で閉じていない。** (C2)(C3)(C1) は接頭辞に遺伝するので
「孤児を全部剥がしてから基礎を見る」でよいが、(C5') は違う。
⟹ **1 段剥がすごとに、基礎の証明書を全部見なければならない。**
（`r57.why_self` はこれを間違えていた。`r60` で直した。）

## ⚠ 使い方の規律（今日 3 回救われた）

**(a) 退化検査**: 新しい証明書を足したら `audit()` を当て、**自明な関数と一致して
いないか**を直に測る。`inW` / `refute.py` / `Wup` は 3 つとも `lev M[0] > u` に
潰れていた（15609/15609、14421/14421、3717/3717）のに、陽性対照も健全性対照も
通っていた。**対照が鳴っただけでは足りない。**

**(b) 限界の覆いで測る**: 新しい証明書の値打ちは、**既に覆われているものを除いた
母数**で測る。絶対値で測ると誤解を招く（(C11)「全展開が行 2 ≡ 0」は絶対値 13% だが
**限界の覆いは 0%** ——（C5') に完全に含まれていた）。`marginal()` を使う。
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio

__all__ = ['lev', 'lev0', 'srow', 'has_parent', 'wcert', 'wcat_cert',
           'rsum', 'audit', 'marginal', 'CERTS']

CERTS = ('C1', 'C2', 'C3', "C5'", "C6'", 'C10', 'C11')


def lev(p):
    """列のレベル `2*行1 + 行2`（`lean/Wset.lean:57`）。"""
    return 2 * p[1] + p[2]


def lev0(M):
    """`lev M 0`。`M = []` は 0（`entry` は範囲外で 0）。"""
    return lev(M[0]) if M else 0


def srow(M, j):
    """`srow`（`lean/Trio.lean:81`）: 列 j の非零最下行。"""
    return 2 if M[j][2] > 0 else (1 if M[j][1] > 0 else 0)


def has_parent(M, j):
    """`hasParent M (srow M j) j`（`lean/Trio.lean:85`）。"""
    return trio.parent([tuple(p) for p in M], srow(M, j), j) is not None


def _orphan(M, j):
    """列 j が零列か、親を持たないか（`oper` が `Pred` に潰れる条件）。"""
    return tuple(M[j]) == (0, 0, 0) or not has_parent(M, j)


def _base(M):
    """剥がしを使わない基礎の証明書。**(C5') が接頭辞で閉じていない**ので、
    (C6') の各段でこれを呼ぶ必要がある。"""
    if len(M) <= 1:
        return 'C1'                                   # singleton_mem_W / W_nil
    if all(p[2] == 0 for p in M):
        return 'C2'                                   # zeroRow2_mem_Wself
    if all(p[0] == 0 for p in M):
        return 'C3'                                   # flat_mem_W
    if all(p[2] == 0 for p in M[:-1]):
        return "C5'"                                  # snoc_zeroRow2
    return None


def wcert(M, u=None):
    """`M ∈ Wself`（`u` を渡せば `M ∈ W u`）の証明書の名前、無ければ None。

    当たれば Lean の証明ずみ定理から所属が出る。**外れても非所属ではない。**"""
    M = tuple(tuple(p) for p in M)
    if u is not None and M and lev0(M) > u:
        return None                       # `lev_root_le_of_mem_W` の対偶。確実に非所属
    b = _base(M)
    if b:
        return b
    X, k = M, 0
    while len(X) >= 2:                    # (C6') snoc_orphan を末尾から 1 段ずつ
        if not _orphan(X, len(X) - 1):
            return None
        X = X[:-1]; k += 1
        b = _base(X)
        if b:
            return "C6'(%d)+%s" % (k, b)
    return None


def rsum(A, B):
    """`rsum A B`（`lean/Wset.lean:1317`）: B の根の行 0 が `A ++ B` の全列以下。"""
    r = B[0][0]
    return all(r <= p[0] for p in A) and all(r <= p[0] for p in B)


def wcat_cert(A, B, u=None):
    """`A ++ B` の証明書。(C10) `W_flatMap_copies` と (C11) `W_add` を含む。

    ⚠ 段は `A` 側に揃う（`lev (A++B) 0 = lev A 0`）ので、(C11) には
    `lev B 0 <= lev A 0` が要る（`mem_Wself_iff`）。"""
    A = tuple(tuple(p) for p in A); B = tuple(tuple(p) for p in B)
    if not A:
        return wcert(B, u)
    if not B:
        return wcert(A, u)
    if A == B and all(A[0][0] <= p[0] for p in A):
        return 'C10'                       # W_flatMap_copies（同じ Q を n 個）
    if lev0(B) <= lev0(A) and rsum(A, B):
        return 'C11'                       # W_add
    return wcert(A + B, u)


# ---------------------------------------------------------------- 規律の道具

def audit(pop, f, trivial, name='計器'):
    """**退化検査**（教訓 12）。`f` の判定が自明な関数 `trivial` と一致しないか。

    `inw_audit.py` と同じ形。**一致率 100% なら、その計器は何も測っていない。**
    戻り値: (一致, 食い違い, 未判定)。"""
    same = diff = und = 0
    for M in pop:
        a, b = f(M), trivial(M)
        if a is None:
            und += 1
        elif bool(a) == bool(b):
            same += 1
        else:
            diff += 1
        del b
    print('  [退化検査] %s: 一致 %d / **食い違い %d** / 未判定 %d%s'
          % (name, same, diff, und,
             '   ⚠ **食い違い 0 ⟹ 退化している**' if same and not diff else ''))
    return same, diff, und


def marginal(pop, old, new, name='新しい証明書'):
    """**限界の覆い**（教訓・R41）。既に `old` が覆うものを除いた母数で `new` を測る。

    絶対値で測ると誤解を招く。戻り値: (残りの母数, new が覆った数)。"""
    rest = [M for M in pop if not old(M)]
    hit = sum(1 for M in rest if new(M))
    print('  [限界の覆い] %s: 母数 %d（旧が覆えなかったもの）中 **%d (%.1f%%)**'
          % (name, len(rest), hit, 100.0 * hit / max(1, len(rest))))
    return len(rest), hit


if __name__ == '__main__':
    import random
    from collections import Counter
    rng = random.Random(20260829)
    COLS = [(a, b, c) for a in range(6) for b in range(6) for c in range(2)]
    P = set()
    while len(P) < 4000:
        P.add(tuple(rng.choice(COLS) for _ in range(rng.randint(1, 5))))
    P = list(P)
    c = Counter(wcert(M).split('+')[0] if wcert(M) else 'なし' for M in P)
    n = sum(v for k, v in c.items() if k != 'なし')
    print('自己検査: 乱択 %d 個（長さ 1..5、行 0/行 1 は 0..5、行 2 は 0..1）' % len(P))
    print('  **覆い %d (%.0f%%)**  内訳 %s'
          % (n, 100.0 * n / len(P), dict(sorted(c.items()))))
    # 陽性対照: 各証明書が実際に使われていること
    miss = [k for k in ('C1', 'C2', 'C3', "C5'") if c.get(k, 0) == 0]
    print('  [陽性対照] 使われなかった基礎の証明書: %s' % (miss or 'なし（全部使われた）'))
    # 退化検査: 「行 2 ≡ 0 か」と一致していないか
    audit(P, lambda M: wcert(M) is not None,
          lambda M: all(p[2] == 0 for p in M), 'wcert vs 「行 2 ≡ 0」')
    audit(P, lambda M: wcert(M) is not None,
          lambda M: len(M) <= 1, 'wcert vs 「|M| <= 1」')
    # 限界の覆い: (C5')(C6') は (C1)-(C3) を真に超えるか
    marginal(P, lambda M: _base(M) in ('C1', 'C2', 'C3'),
             lambda M: wcert(M) is not None, "(C5') + (C6')")
