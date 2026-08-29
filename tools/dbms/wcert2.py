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
_C13_MAXLEN = 12      # (C13) を試す M の長さ上限（費用の打ち切り）
_C13_MAXEXP = 40      # (C13) で見る展開の長さ上限（費用の打ち切り）
_BUDGET = [10 ** 7]   # 1 回の判定で回すノード数の上限。**尽きたら「覆えない」側に倒す**
                      # （健全側。証明書が見つからないだけで非所属ではない）
TOW_ORACLE = False    # 旧 (C14) 用（R68 で (C15) に置き換え）
ASSUME = set()        # 仮定として足すもの。空なら strict（Lean 証明ずみの規則だけ）
                      #   'S'     (SNOC-flat) 平らな列を、親が根でなくても足せる
                      #   'D'     深い側の連結（`rsum` と `lev0(B) <= u` を落とした `W_add`）
                      #   'TOW' 'LTOW' 'MLIFT'  塔の族（行 2 = 1 を含む Q の場合）


def _peel(M):
    """(C6') `snoc_orphan` を末尾から 1 段ずつ。**各段で基礎を全部見る**。

    `'S'`（**(SNOC-flat)**）を仮定すると、**平らな列（srow = 0）**は
    親が根でなくても剥がせる（`snoc_flat_root`（`Wtower2.lean:2208`）から
    「親が根」を落としたもの）。"""
    b = _base(M)
    if b:
        return b
    X, k = M, 0
    while len(X) >= 2:
        if not _orphan(X, len(X) - 1) and not (
                'S' in ASSUME and srow(X, len(X) - 1) == 0):
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


def _clause2_induction(M, N=4):
    """(C13) **節 2 を n について帰納で閉じる**（R69 で族の形に一般化）。

    `expfam` より `X_n := M⟦n⟧ = A0 ++ concat_{k<n} (Q0 + k*D)`。⟹

        **X_{n+1} = X_n ++ (Q0 + n*D)**

    各段の `X_n ∈ Wself` が**同じ規則**で `X_{n-1} ∈ Wself` から出るなら、
    `∀ n ≥ 1` が **Nat の帰納**で閉じ、節 2（`Aop`、`lean/Wset.lean:171`）で `M ∈ W u`。

    一様性の根拠: 継ぎ足す塊 `Q0 + n*D` は **列の `srow` と行 2 が n に依らない**
    （`D` の行 2 成分は 0、行 0/行 1 は増えるだけ）。⟹ 「平らな列か」「孤児か」の
    判定に使う量が n によらない。

    ⚠ **`∀n` の一様性は n = 1..N で確かめている**（`N` を振って不動なことを別途測る）。
    **この規則自体はまだ Lean に無い**（L2 への依頼、L55-b）。
    """
    if len(M) > _C13_MAXLEN:
        return None
    r = expfam(M)
    if r is None:
        return None
    A0, Q0, D = r
    if not Q0:
        return None
    Es = []
    for n in range(1, N + 2):
        X = A0 + tuple(tuple(Q0[i][j] + k * D[i][j] for j in range(3))
                       for k in range(n) for i in range(len(Q0)))
        if len(X) > _C13_MAXEXP:
            return None
        Es.append(X)
    cs = [wself2(E) for E in Es]
    if any(c is None for c in cs):
        return None
    kinds = [c.split('(')[0].split('+')[0] for c in cs[1:]]
    if len(set(kinds)) != 1:                 # n >= 2 の証明書が**同じ規則**か
        return None
    return 'C13(%s)' % kinds[0]


def _towexp(M):
    """(C14) **`(TOW)` を神託にした節 2**（`TOW_ORACLE = True` のときだけ）。

    `srow(最後) = 1` のとき `d1 = 0`（`1 < i1` が偽）で行 0 だけ持ち上がる:

        **M⟦n⟧ = M.take j0 ++ shTower(Q, d0, n)**,  Q := M[j0:j1]  （検算 35744/35744）

    `(TOW)`（`ShiftTowerClosed`、`lean/Wtower2.lean:1763`）が `shTower Q d0 n ∈ W (lev Q 0)`
    を与え、前置きとの連結は `W_add`。`rsum` は `shTower` の列が `Q` の列以上なので
    **n に依らない** ⟹ `∀n` が一様に閉じる。

    ⚠ `(TOW)` は**未証明**。これは「もし `(TOW)` があればどこまで伸びるか」の測定用。
    """
    if not TOW_ORACLE:
        return None
    j1 = len(M) - 1
    if j1 < 1 or srow(M, j1) != 1 or not has_parent(M, j1):
        return None
    j0 = trio.parent([tuple(p) for p in M], 1, j1)
    if j0 is None or j0 >= j1:
        return None
    P, Q = M[:j0], M[j0:j1]
    u = lev0(M)
    if lev0(Q) > u:
        return None
    if not all(Q[0][0] <= p[0] for p in Q):        # (TOW) の側条件（根が最浅）
        return None
    if wself2(Q) is None:
        return None
    if P:
        if not all(Q[0][0] <= p[0] for p in P):    # rsum（n に依らない）
            return None
        if wself2(P) is None:
            return None
    return 'C14/TOW(j0=%d)' % j0


def expfam(M):
    """**`oper` の定義から厳密に**展開の族を取り出す（推定しない）。

    `oper_unfold`（L2, commit 978c7a5）:

        M⟦n⟧ = M.take j0 ++ (range n).flatMap (写し k)
        写し k の第 i 列 = Q0[i] + k * D[i]   （**k について 1 次。j0/d0/d1 は M だけで決まる**）

    ⟹ `M⟦1⟧` と `M⟦2⟧` の 2 つだけで `A0`, `Q0`, `D` が**確定**する:

        j1 = |M| - 1,  |M⟦1⟧| = j1（＝ M.dropLast）,  |M⟦2⟧| = j1 + (j1 - j0)
        ⟹ **j0 = 2*j1 - |M⟦2⟧|**,  A0 = M⟦1⟧[:j0],  Q0 = M⟦1⟧[j0:],  D = M⟦2⟧[j1:] - Q0

    戻り値 (A0, Q0, D) または None（`Pred` に潰れる場合など）。
    """
    if len(M) < 2:
        return None
    E1 = tuple(tuple(x) for x in trio.expand([tuple(p) for p in M], 1))
    E2 = tuple(tuple(x) for x in trio.expand([tuple(p) for p in M], 2))
    j1 = len(M) - 1
    if len(E1) != j1 or len(E2) <= len(E1):
        return None                        # `Pred` 型（既存の孤児証明書の領分）
    j0 = 2 * j1 - len(E2)
    if not (0 <= j0 < j1):
        return None
    A0, Q0, Q1 = E1[:j0], E1[j0:], E2[j1:]
    if len(Q1) != len(Q0):
        return None
    D = tuple((Q1[i][0] - Q0[i][0], Q1[i][1] - Q0[i][1], Q1[i][2] - Q0[i][2])
              for i in range(len(Q0)))
    if any(d[0] < 0 or d[1] < 0 or d[2] != 0 for d in D):
        return None
    return A0, Q0, D


def famname(D):
    """族の名前。(F2) 複製 / (F3) 一様シフト / (F4) 一様持ち上げ / (F5) 列ごと増分。"""
    if all(d == (0, 0, 0) for d in D):
        return 'F2'                        # W_flatMap_copies。**証明ずみ**
    if len(set(D)) == 1:
        return 'F3' if D[0][1] == 0 else 'F4'
    if all(d[1] == 0 for d in D):
        return 'F5e'                       # 行 0 だけ、列ごとに違う
    return 'F5'                            # 行 1 も列ごとに違う


_NEED = {'F2': None, 'F3': 'TOW', 'F4': 'LTOW', 'F5e': 'MLIFT', 'F5': 'MLIFT'}


def _famcert(M):
    """(C15) **展開の族による節 2**。`oper_unfold` から厳密に取るので推定しない。

    塔の部分 `concat_k (Q0 + k*D)` を規則（F2 は `W_flatMap_copies` で**証明ずみ**、
    F3/F4/F5 は仮定）で `W (lev Q0 0)` に入れ、前置き `A0` は `W_add` で継ぐ。
    `rsum(A0, 塔)` は塔の列が `Q0` の列以上なので **n に依らない**。
    """
    r = expfam(M)
    if r is None:
        return None
    A0, Q0, D = r
    if not Q0:
        return None
    fam = famname(D)
    need = _NEED[fam]
    # **`shiftTowerClosed_of_zeroRow2`（`lean/L47W.lean:136`、証明ずみ）**:
    #   Q ∈ W u → (∀ p ∈ Q, p.2.2 = 0) → shTower Q e n ∈ W u
    #   **側条件（根が最浅）を 1 度も使わない。**
    # ⟹ 一様シフト塔（F2/F3）で `Q0` が行 2 ≡ 0 なら **仮定が要らず、根が最浅も要らない**。
    z2 = all(p[2] == 0 for p in Q0)
    proven_tow = fam in ('F2', 'F3') and z2
    if proven_tow:
        need = None
    if need is not None and need not in ASSUME:
        return None                        # strict では証明ずみの族しか使えない
    u = lev0(M)
    deep = 'D' in ASSUME
    if not deep and lev0(Q0) > u:
        return None                        # mem_Wself_iff（塔が W u に入るのに必要）
    if not proven_tow and not all(Q0[0][0] <= p[0] for p in Q0):
        return None                        # 塔の側条件（根が最浅）
    if wself2(Q0) is None:
        return None
    if A0:
        if not deep and not all(Q0[0][0] <= p[0] for p in A0):
            return None                    # rsum(A0, 塔)。n に依らない
        if wself2(A0) is None:
            return None
    return 'C15/%s%s%s' % (fam + ('z2' if proven_tow else ''),
                           '' if need is None else '[%s]' % need,
                           '[D]' if deep else '')


def wself2(M, depth=0):
    """`M ∈ Wself` の証明書の名前、無ければ None。**分割を全部試して再帰**。"""
    M = tuple(tuple(p) for p in M)
    if M in _MEMO:
        return _MEMO[M]
    _BUDGET[0] -= 1
    if _BUDGET[0] <= 0:
        return None                          # 予算切れ。**健全側（覆えない）に倒す**
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
        r = _towexp(M)                   # (C14) 旧（R68 で (C15) に置換）
    if r is None:
        r = _famcert(M)                  # (C15) 展開の族による節 2（厳密）
    if r is None:
        u = lev0(M)                          # lev (A++B) 0 = lev A 0
        deep = 'D' in ASSUME
        for k in range(1, len(M)):
            A, B = M[:k], M[k:]
            if not deep and lev0(B) > u:     # mem_Wself_iff: B ∈ W u に必要
                continue
            if not deep and not rsum(A, B):  # W_add の側条件
                continue
            if wself2(A, depth + 1) is None:
                continue
            if wself2(B, depth + 1) is None:
                continue
            r = ('C11d(k=%d)[D]' if deep else 'C11(k=%d)') % k   # W_add
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
