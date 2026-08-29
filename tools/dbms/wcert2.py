# -*- coding: utf-8 -*-
"""**連結分割で閉じた `Wself` の証明書**（課題 R66、2026-08-29）。

`wcert.py`（R45）は連結の分割を探していなかった。team-lead の指摘:

    psiI.json 行 270 `(0,0,0)(1,1,1)(0,0,0)(1,0,0) = psi(W_w)+w`
    `wcert` は落とすが、`A=(0,0,0)(1,1,1)`, `B=(0,0,0)(1,0,0)` に切れば
    `wcat_cert` が **C11 (`W_add`)** を返す ⟹ **計器の穴**

ここでは **分割点 k を全部試し、両側を再帰**して閉じる。`wcert.py` は壊さない。

## 使う規則（**Lean で証明ずみのものだけ**。各分岐にどの定理かを書く）

    `mem_Wself_iff`（`lean/Wtower2.lean:2991`）
        **M ∈ W u  ↔  M ∈ Wself ∧ lev M 0 ≤ u**          Wself = {M | M ∈ W (lev M 0)}
    `W_add`（`lean/Wset.lean:1682`）
        A ∈ W u → B ∈ W u → **rsum A B** → A ++ B ∈ W u
        `rsum A B : ∀ p ∈ A ++ B, entry B 0 0 ≤ p.1`（`lean/Wset.lean:1317`）
    `W_flatMap_copies`（`lean/Wset.lean:2552`）
        Q ∈ W u → (∀ p ∈ Q, entry Q 0 0 ≤ p.1) → **Q を n 個並べたもの** ∈ W u
    `Aop` の節 2（`lean/Wset.lean:171`）
        (∀ n ≥ 1, M⟦n⟧ ∈ W u) → M ∈ W u

## (C12) —— **持ち上げの無い展開なら節 2 が有限で閉じる**（R66 で新設）

`oper`（`lean/Trio.lean:98`）は `i1 := srow M j1` が **0 のとき `d0 = d1 = 0`**（持ち上げ無し）。
このとき（`j0 :=` 最後の列の親）

    **M⟦n⟧ = M.take j0 ++ (Q を n 個)**,  Q := M[j0 : j1]      （検算 10455/10455）

`Q` の側は `W_flatMap_copies` で **n に依らず** `W (lev Q 0)`、`M.take j0` との連結は
`W_add` で、その側条件 `rsum` も **Q の列の繰り返しなので n に依らない**。
⟹ **`∀ n ≥ 1` が有限で確かめきれる** ⟹ 節 2 で `M ∈ W u`。**健全。**

⟹ **`A ++ B ∈ Wself`** を出す道:  `lev (A ++ B) 0 = lev A 0`（第 0 列は A のもの）なので
   `u := lev A 0` と置き、`A ∈ Wself`（＝ `A ∈ W u`）、`B ∈ Wself ∧ lev B 0 ≤ u`
   （＝ `B ∈ W u`、`mem_Wself_iff`）、`rsum A B` の 3 つが揃えば `W_add` が使える。

基礎の証明書は `wcert.py` と同じ（(C1)(C2)(C3)(C5')(C6')）。**その落とし穴も同じ**:
**(C5') は接頭辞で閉じていないので、(C6') の剥がしは 1 段ごとに全部の基礎を見る。**

## ⚠ 健全性について

当たれば Lean の証明ずみ定理から所属が出る。**外れても非所属ではない。**
唯一の確実な非所属は `lev M 0 > u`（`lev_root_le_of_mem_W`、`lean/Wset.lean:2161`）。
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
from wcert import lev, lev0, srow, has_parent, rsum, _base, _orphan, audit, marginal

__all__ = ['wself2', 'wcert2', 'why2_detail', 'lev0', 'rsum']

_MEMO = {}
_C13_MAXLEN = 24      # (C13) を試す M の長さ上限（費用の打ち切り）
_C13_MAXEXP = 90      # (C13) で見る展開の長さ上限（費用の打ち切り）


def _peel(M):
    """(C6') `snoc_orphan` を末尾から 1 段ずつ。**各段で基礎を全部見る**。"""
    b = _base(M)
    if b:
        return b
    X, k = M, 0
    while len(X) >= 2:
        if not _orphan(X, len(X) - 1):
            return None
        X = X[:-1]; k += 1
        b = _base(X)
        if b:
            return "C6'(%d)+%s" % (k, b)
    return None


def _copies(M):
    """(C10) `W_flatMap_copies`: M = Q を n 個 かつ Q の根が Q で最浅。"""
    L = len(M)
    for q in range(1, L // 2 + 1):
        if L % q:
            continue
        Q = M[:q]
        if all(M[i * q:(i + 1) * q] == Q for i in range(L // q)) and \
           all(Q[0][0] <= p[0] for p in Q):
            return 'C10(n=%d)' % (L // q)
    return None


def _noliftexp(M):
    """(C12) 持ち上げの無い展開（`srow(最後) = 0`）なら節 2 が有限で閉じるか。"""
    j1 = len(M) - 1
    if j1 < 1 or srow(M, j1) != 0 or not has_parent(M, j1):
        return None
    j0 = trio.parent([tuple(p) for p in M], 0, j1)
    if j0 is None or j0 >= j1:
        return None
    P, Q = M[:j0], M[j0:j1]
    u = lev0(M)
    if lev0(Q) > u:                       # mem_Wself_iff: Q*n ∈ W u に必要
        return None
    if not all(Q[0][0] <= p[0] for p in Q):
        return None                       # W_flatMap_copies の側条件
    if wself2(Q) is None:
        return None
    if P:
        if not (all(Q[0][0] <= p[0] for p in P)):
            return None                   # rsum(P, Q*n)。n に依らない
        if wself2(P) is None:
            return None
    return 'C12(j0=%d)' % j0


def _clause2_induction(M, N=6):
    """(C13) **節 2 を n について帰納で閉じる**。

    `srow(最後) = 0` のとき `M⟦n⟧ = P ++ Q*n`（持ち上げ無し。C12 の検算と同じ）。
    ⟹ **`X_{n+1} = X_n ++ Q`**。各段の `X_n ∈ Wself` が **同じ規則**で
    `X_{n-1} ∈ Wself` から出るなら、`∀ n ≥ 1` が **Nat の帰納**で閉じ、
    節 2（`Aop`、`lean/Wset.lean:171`）で `M ∈ W u` が出る。

    一様性の根拠（n に依らない量）:
      * `X_n` の**列の集合**は n によらない（P の列 ∪ Q の列）
        ⟹ 「根が最浅」「`lev`」「`rsum`」の判定は n に依らない
      * 最後の列は常に `Q[-1]` で、その親は n >= 2 で一定（前に Q の写しが増えるだけ）

    ⚠ **`∀n` の一様性は n = 1..N で確かめている**（`N` を振って不動なことを別途測る）。
    ⟹ 各段は証明ずみの規則だが、**この規則自体はまだ Lean に無い**。L2 への依頼。
    """
    j1 = len(M) - 1
    if j1 < 1 or srow(M, j1) != 0 or not has_parent(M, j1):
        return None
    if len(M) > _C13_MAXLEN:
        return None                              # 費用の打ち切り（N と上限を振って検査する）
    Es = []
    for n in range(1, N + 2):
        E = tuple(tuple(x) for x in trio.expand([tuple(p) for p in M], n))
        if not E or E == M or len(E) > _C13_MAXEXP:
            return None
        Es.append(E)
    D = Es[1][len(Es[0]):]                       # X_2 = X_1 ++ D
    if not D or Es[0] + D != Es[1]:
        return None
    for n in range(1, N):                        # X_{n+1} = X_n ++ D が一様か
        if Es[n] + D != Es[n + 1]:
            return None
    cs = [wself2(E) for E in Es]
    if any(c is None for c in cs):
        return None
    if len(set(cs[1:])) != 1:                    # n >= 2 の証明書が**同じ規則**か
        return None
    return 'C13(%s)' % cs[1]


def wself2(M, depth=0):
    """`M ∈ Wself` の証明書の名前、無ければ None。**分割を全部試して再帰**。"""
    M = tuple(tuple(p) for p in M)
    if M in _MEMO:
        return _MEMO[M]
    if len(M) <= 1:
        _MEMO[M] = 'C1'                      # singleton_mem_W / W_nil
        return 'C1'
    _MEMO[M] = None                          # 循環よけ（分割は真に短くなるので実際は不要）
    r = _peel(M)
    if r is None:
        r = _copies(M)
    if r is None:
        r = _noliftexp(M)                # (C12) 節 2（持ち上げ無し）
    if r is None:
        r = _clause2_induction(M)        # (C13) 節 2 を n について帰納
    if r is None:
        u = lev0(M)                          # lev (A++B) 0 = lev A 0
        for k in range(1, len(M)):
            A, B = M[:k], M[k:]
            if lev0(B) > u:                  # mem_Wself_iff: B ∈ W u に必要
                continue
            if not rsum(A, B):               # W_add の側条件
                continue
            if wself2(A, depth + 1) is None:
                continue
            if wself2(B, depth + 1) is None:
                continue
            r = 'C11(k=%d)' % k              # W_add
            break
    _MEMO[M] = r
    return r


def wcert2(M, u=None):
    """`M ∈ W u`（`u` 省略時は `Wself`）の証明書。"""
    M = tuple(tuple(p) for p in M)
    if u is not None and M and lev0(M) > u:
        return None                          # lev_root_le_of_mem_W の対偶（**確実な非所属**）
    return wself2(M)


def why2_detail(M):
    """落ちた M について、どこで落ちたかを返す（診断用）。"""
    M = tuple(tuple(p) for p in M)
    u = lev0(M)
    n_lev = n_rsum = n_A = n_B = 0
    for k in range(1, len(M)):
        A, B = M[:k], M[k:]
        if lev0(B) > u:
            n_lev += 1; continue
        if not rsum(A, B):
            n_rsum += 1; continue
        if wself2(A) is None:
            n_A += 1; continue
        if wself2(B) is None:
            n_B += 1; continue
    return {'lev0(B)>u': n_lev, 'rsum が破れる': n_rsum,
            '左片が覆えない': n_A, '右片が覆えない': n_B}
