/-
課題 L51: シートのラダーで**最初に落ちる 3 行**は、どれも同じ `Q = (0,0,0)(1,1,1)` の
**一般塔**で、違うのは `(e, d)` だけである。

    行 275  (0,0,0)(1,1,1)(1,0,0) = psi(W_w)*w   M⟦n⟧ = gTower Q 0 0 n  ← **W_flatMap_copies**
    行 284  (0,0,0)(1,1,1)(1,1,0) = psi(W_w+W)   M⟦n⟧ = gTower Q 1 0 n  ← ShiftTowerClosed
    行 316  (0,0,0)(1,1,1)(1,1,1) = psi(W_w*2)   M⟦n⟧ = gTower Q 1 1 n  ← (GTOW) 未証明

`(e,d) = (0,0)` は **既に Lean にある**（`Wset.W_flatMap_copies`）ので、行 275 は取れる。
-/
import Wtower2

namespace TRIO
namespace L51T

open Wset

/-- **一般塔**: `k` 枚目の写しは行 0 を `e*k`、行 1 を `d*k` ずらす。

    (e,d) = (0,0)  `W_flatMap_copies`（証明ずみ）
    (e,d) = (e,0)  `shTower` ＝ `ShiftTowerClosed`（未証明）
    (e,d) = (e,d)  **(GTOW)（未証明）** -/
noncomputable def gTower (Q : TrioSeq) (e d n : ℕ) : TrioSeq :=
  (List.range n).flatMap fun k => shiftr01 (e * k) (d * k) Q

theorem gTower_flatMap (Q : TrioSeq) (n : ℕ) :
    gTower Q 0 0 n = (List.range n).flatMap fun _ => Q := by
  unfold gTower
  simp [shiftr01]

theorem gTower_shTower (Q : TrioSeq) (e n : ℕ) : gTower Q e 0 n = shTower Q e n := by
  unfold gTower shTower
  simp [Nat.mul_comm]

/-- **(GTOW)** —— 課題 L51-c で切り出す一般命題。
`d = 0` が `ShiftTowerClosed`、`e = d = 0` が `W_flatMap_copies`。 -/
def GTow : Prop :=
  ∀ (u e d n : ℕ) (Q : TrioSeq), Q ∈ W u → (∀ p ∈ Q, entry Q 0 0 ≤ p.1) →
    gTower Q e d n ∈ W u

/-- **★ (GTOW) の `e = d = 0` は既に定理**（`W_flatMap_copies`）。 -/
theorem gTow_zero {u n : ℕ} {Q : TrioSeq} (hQ : Q ∈ W u)
    (hQr : ∀ p ∈ Q, entry Q 0 0 ≤ p.1) : gTower Q 0 0 n ∈ W u := by
  rw [gTower_flatMap]
  exact W_flatMap_copies hQ hQr n

/-! ### 課題 L51-a: `(0,0,0)(1,1,1)(1,0,0) ∈ Wself` -/

/-- `Q = (0,0,0)(1,1,1)` ＝ 2 行 BMS の極限 `psi(W_w)`。 -/
def Q0 : TrioSeq := [(0, 0, 0), (1, 1, 1)]

/-- `(0,0,0)(1,1,1)(1,0,0)` ＝ `psi(W_w)*w`。**シートのラダーで最初に落ちる行**。 -/
def M275 : TrioSeq := [(0, 0, 0), (1, 1, 1), (1, 0, 0)]

theorem Q0_mem_Wself : Q0 ∈ Wself := by
  have h : Q0 = [((0, 0, 0) : ℕ × ℕ × ℕ)] ++ [((1, 1, 1) : ℕ × ℕ × ℕ)] := rfl
  rw [h]
  refine snoc_zeroRow2 ?_ _
  intro p hp
  simp at hp
  rw [hp]

theorem lev_Q0 : lev Q0 0 = 0 := by simp [lev, entry, Q0]

theorem Q0_mem_W_zero : Q0 ∈ W 0 := by
  have h := Q0_mem_Wself
  rw [Wself, Set.mem_setOf_eq, lev_Q0] at h
  exact h

theorem Q0_root : ∀ p ∈ Q0, entry Q0 0 0 ≤ p.1 := by
  intro p hp
  simp [entry, Q0]

theorem lev_M275 : lev M275 0 = 0 := by simp [lev, entry, M275]

@[simp] theorem entry_M275_00 : entry M275 0 0 = 0 := rfl
@[simp] theorem entry_M275_10 : entry M275 1 0 = 0 := rfl
@[simp] theorem entry_M275_20 : entry M275 2 0 = 0 := rfl
@[simp] theorem entry_M275_01 : entry M275 0 1 = 1 := rfl
@[simp] theorem entry_M275_11 : entry M275 1 1 = 1 := rfl
@[simp] theorem entry_M275_21 : entry M275 2 1 = 1 := rfl

/-- 末尾 `(1,0,0)` は行 1・行 2 が 0 なので **`srow = 0`**。
⟹ `d0 = d1 = 0`（上昇がまったく無い）。 -/
theorem srow_M275 : srow M275 2 = 0 := by simp [srow, entry, M275]

theorem nextrel0_M275_02 : nextrel0 M275 0 2 := by
  refine ⟨by simp [M275], by simp [M275], by omega, by simp [entry, M275], ?_⟩
  intro j hj
  have h1 : j = 1 := by omega
  subst h1
  simp [entry, M275]

theorem nextrel0_M275_unique {j : ℕ} (h : nextrel0 M275 j 2) : j = 0 := by
  obtain ⟨hj3, -, -, hlt, -⟩ := h
  simp only [M275] at hj3
  simp at hj3
  rcases j with _ | _ | _ | j
  · rfl
  · simp [entry, M275] at hlt
  · simp [entry, M275] at hlt
  · omega

theorem nextR_M275_02 : nextR M275 0 0 2 := by
  rw [nextR]
  simp only [if_pos rfl]
  exact nextrel0_M275_02

theorem hasParent_M275 : hasParent M275 0 2 := by
  refine ⟨0, nextR_M275_02, ?_⟩
  intro y hy
  rw [nextR] at hy
  simp only [if_pos rfl] at hy
  exact nextrel0_M275_unique hy

theorem parent_M275 : parent M275 0 2 = 0 := by
  have hex : ∃ j0, nextR M275 0 j0 2 := ⟨0, nextR_M275_02⟩
  have hspec : nextR M275 0 (parent M275 0 2) 2 := Classical.epsilon_spec hex
  rw [nextR] at hspec
  simp only [if_pos rfl] at hspec
  exact nextrel0_M275_unique hspec

/-- **★★ `M275⟦n⟧` は `Q0` を `n` 個並べただけ**（上昇が無い）。 -/
theorem oper_M275 (n : ℕ) : M275⟦n⟧ = gTower Q0 0 0 n := by
  have hl : M275.length - 1 = 2 := rfl
  have hs : srow M275 (M275.length - 1) = 0 := srow_M275
  have hp : parent M275 (srow M275 (M275.length - 1)) (M275.length - 1) = 0 := parent_M275
  rw [oper]
  dsimp only
  split
  · exact absurd ‹M275.length - 1 = 0› (by decide)
  split
  · rename_i h
    exact absurd h.1 (by simp [entry, M275])
  split
  · rename_i h
    exact absurd hasParent_M275 h
  rw [hp, hl]
  have htake : M275.take 0 = [] := rfl
  rw [htake, List.nil_append, gTower_flatMap]
  congr 1
  funext k
  have hr : List.range' 0 2 = [0, 1] := rfl
  rw [hr]
  simp [Q0, srow_M275]

/-- **★★★ 課題 L51-a: `(0,0,0)(1,1,1)(1,0,0) ∈ W 0`。仮定ゼロ。** -/
theorem M275_mem_W_zero : M275 ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n hn
  rw [oper_M275]
  exact gTow_zero Q0_mem_W_zero Q0_root

/-- **★★★ 課題 L51-a: `(0,0,0)(1,1,1)(1,0,0) ∈ Wself`。仮定ゼロ。** -/
theorem M275_mem_Wself : M275 ∈ Wself := by
  show M275 ∈ W (lev M275 0)
  rw [lev_M275]
  exact M275_mem_W_zero

/-! ### 課題 L51-b: 行 284 `(0,0,0)(1,1,1)(1,1,0)` ＝ `gTower Q0 1 0 n` ＝ `shTower` -/

theorem le0_le {M : TrioSeq} {a b : ℕ} (h : le0 M a b) : a ≤ b := by
  obtain ⟨-, -, h⟩ := h
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => exact le_trans ih (le_of_lt h2.2.2.1)

/-- `(0,0,0)(1,1,1)(1,1,0)` ＝ `psi(W_w + W)`。 -/
def M284 : TrioSeq := [(0, 0, 0), (1, 1, 1), (1, 1, 0)]

@[simp] theorem entry_M284_00 : entry M284 0 0 = 0 := rfl
@[simp] theorem entry_M284_10 : entry M284 1 0 = 0 := rfl
@[simp] theorem entry_M284_20 : entry M284 2 0 = 0 := rfl
@[simp] theorem entry_M284_01 : entry M284 0 1 = 1 := rfl
@[simp] theorem entry_M284_11 : entry M284 1 1 = 1 := rfl
@[simp] theorem entry_M284_21 : entry M284 2 1 = 1 := rfl
@[simp] theorem entry_M284_02 : entry M284 0 2 = 1 := rfl
@[simp] theorem entry_M284_12 : entry M284 1 2 = 1 := rfl
@[simp] theorem entry_M284_22 : entry M284 2 2 = 0 := rfl

theorem lev_M284 : lev M284 0 = 0 := by simp [lev, entry, M284]

/-- 末尾 `(1,1,0)` は行 2 が 0・行 1 が 1 なので **`srow = 1`**。⟹ `d1 = 0`。 -/
theorem srow_M284 : srow M284 2 = 1 := by simp [srow, entry, M284]

theorem nextrel0_M284_01 : nextrel0 M284 0 1 := by
  refine ⟨by simp [M284], by simp [M284], by omega, by simp [entry, M284], ?_⟩
  intro j hj
  omega

theorem nextrel0_M284_02 : nextrel0 M284 0 2 := by
  refine ⟨by simp [M284], by simp [M284], by omega, by simp [entry, M284], ?_⟩
  intro j hj
  have h1 : j = 1 := by omega
  subst h1
  simp [entry, M284]

theorem le0_M284_00 : le0 M284 0 0 :=
  ⟨by simp [M284], by simp [M284], Relation.ReflTransGen.refl⟩

theorem le0_M284_01 : le0 M284 0 1 :=
  ⟨by simp [M284], by simp [M284], Relation.ReflTransGen.single nextrel0_M284_01⟩

theorem le0_M284_02 : le0 M284 0 2 :=
  ⟨by simp [M284], by simp [M284], Relation.ReflTransGen.single nextrel0_M284_02⟩

theorem nextrel1_M284_02 : nextrel1 M284 0 2 := by
  refine ⟨by simp [M284], by simp [M284], by omega, by simp [entry, M284],
    le0_M284_02, ?_⟩
  intro j hj
  have h1 : j ≤ 2 := le0_le hj.2
  have h3 : j < 3 := hj.2.1
  rcases j with _ | _ | _ | j
  · omega
  · simp [entry, M284]
  · simp [entry, M284]
  · omega

theorem nextrel1_M284_unique {j : ℕ} (h : nextrel1 M284 j 2) : j = 0 := by
  obtain ⟨hj3, -, -, hlt, -, -⟩ := h
  simp only [M284] at hj3
  simp at hj3
  rcases j with _ | _ | _ | j
  · rfl
  · simp [entry, M284] at hlt
  · simp [entry, M284] at hlt
  · omega

theorem nextR_M284_02 : nextR M284 1 0 2 := by
  rw [nextR]
  simp only [if_neg (by omega : (1 : ℕ) ≠ 0), if_pos rfl]
  exact nextrel1_M284_02

theorem hasParent_M284 : hasParent M284 1 2 := by
  refine ⟨0, nextR_M284_02, ?_⟩
  intro y hy
  rw [nextR] at hy
  simp only [if_neg (by omega : (1 : ℕ) ≠ 0), if_pos rfl] at hy
  exact nextrel1_M284_unique hy

theorem parent_M284 : parent M284 1 2 = 0 := by
  have hex : ∃ j0, nextR M284 1 j0 2 := ⟨0, nextR_M284_02⟩
  have hspec : nextR M284 1 (parent M284 1 2) 2 := Classical.epsilon_spec hex
  rw [nextR] at hspec
  simp only [if_neg (by omega : (1 : ℕ) ≠ 0), if_pos rfl] at hspec
  exact nextrel1_M284_unique hspec

/-- **★★ `M284⟦n⟧ = gTower Q0 1 0 n = shTower Q0 1 n`**（行 0 だけ上がる）。 -/
theorem oper_M284 (n : ℕ) : M284⟦n⟧ = gTower Q0 1 0 n := by
  have hl : M284.length - 1 = 2 := rfl
  have hp : parent M284 (srow M284 (M284.length - 1)) (M284.length - 1) = 0 :=
    parent_M284
  rw [oper]
  dsimp only
  split
  · exact absurd ‹M284.length - 1 = 0› (by decide)
  split
  · rename_i h
    exact absurd h.1 (by simp [entry, M284])
  split
  · rename_i h
    exact absurd hasParent_M284 h
  rw [hp, hl]
  have htake : M284.take 0 = [] := rfl
  rw [htake, List.nil_append]
  unfold gTower
  congr 1
  funext k
  have hr : List.range' 0 2 = [0, 1] := rfl
  rw [hr]
  simp [Q0, shiftr01, srow_M284, le0_M284_00, le0_M284_01, Nat.mul_comm]

/-- **★ 行 284 は `(TOW)` そのもの**（`ShiftTowerClosed` を仮定すれば取れる）。 -/
theorem M284_mem_W_zero_of_tow (h : ShiftTowerClosed) : M284 ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n hn
  rw [oper_M284, gTower_shTower]
  exact h 0 1 n Q0 Q0_mem_W_zero Q0_root

theorem M284_mem_Wself_of_tow (h : ShiftTowerClosed) : M284 ∈ Wself := by
  show M284 ∈ W (lev M284 0)
  rw [lev_M284]
  exact M284_mem_W_zero_of_tow h

/-! ### 課題 L51-c: `W_flatMap_copies` は **`e ≥ 1` で止まる**。止まる場所は `rsum`

`W_flatMap_copies`（`Wset.lean:2552`）の中身は `W_add ih hQ (rsum ...)` で、

    rsum A B := ∀ p ∈ A ++ B, entry B 0 0 ≤ p.1     （足す塊の根が**全体で最浅**）

`e = 0` なら写しは `Q` そのものなので根が変わらず `rsum` が通る。**`e ≥ 1` だと
`k` 枚目の写しの根は `e*k > 0` で、`Q` の根 `0` より深いので `rsum` が破れる。**
下の `example` がその証明（`d ≥ 1` を待つまでもなく `e ≥ 1` で止まる）。

⟹ **(GTOW) に要るのは「`W_add` の `rsum` を、深い側に足す形に緩めたもの」**であり、
それは `Aop` の節 3（`graft`）＝ 残核である（課題 L50 §3 と同じ結論）。 -/
example : ¬ rsum Q0 (shiftr01 1 0 Q0) := by
  intro h
  have h9 := h (0, 0, 0) (by simp [Q0, shiftr01])
  simp [entry, Q0, shiftr01] at h9


/-! ### 課題 L51-b: `(TOWER)` の一般形（列ごとの増分 `D`）

実測（`tools/dbms/ladder.py`、シート 4467 行を全数）では **99.96%** が

    M⟦n⟧ = A ++ concat_{k<n} (Q + k*D)      A = M⟦1⟧、Q = 1 段目、D = 列ごとの増分

の形。内訳は 一様シフト `D=(e,0,0)` 53.9% ／ 一様持ち上げ `D=(e,d,0)` 28.6% ／
列ごとに違う増分 12.4% ／ 複製 `D=0` 5.0%。 -/

/-- `Q` の `j` 番目の成分（`j < |Q|` のとき）。 -/
theorem entry_getElem {Q : TrioSeq} {j : ℕ} (h : j < Q.length) :
    entry Q 0 j = Q[j].1 ∧ entry Q 1 j = Q[j].2.1 ∧ entry Q 2 j = Q[j].2.2 := by
  have hg : Q.getD j ((0, 0, 0) : ℕ × ℕ × ℕ) = Q[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    rfl
  unfold entry
  simp only []
  rw [hg]
  exact ⟨rfl, rfl, rfl⟩

/-- **`k` 段目**: 列 `j` の行 0 に `k * D[j].0`、行 1 に `k * D[j].1` を足す。
**行 2 は不変**（上昇行列 `A_xy` は行 2 に乗らない）。 -/
noncomputable def bump (Q D : TrioSeq) (k : ℕ) : TrioSeq :=
  (List.range Q.length).map fun j =>
    ((entry Q 0 j + k * entry D 0 j, entry Q 1 j + k * entry D 1 j, entry Q 2 j) :
      ℕ × ℕ × ℕ)

/-- 列ごとの増分つきの塔。 -/
noncomputable def mTower (Q D : TrioSeq) (n : ℕ) : TrioSeq :=
  (List.range n).flatMap (bump Q D)

/-- **増分が一様なら `bump` は `shiftr01`**。⟹ `mTower` は `gTower` に化ける。 -/
theorem bump_const (Q : TrioSeq) (e d k : ℕ) :
    bump Q (List.replicate Q.length ((e, d, 0) : ℕ × ℕ × ℕ)) k
      = shiftr01 (e * k) (d * k) Q := by
  unfold bump shiftr01
  refine List.ext_getElem (by simp) ?_
  intro j h1 h2
  simp only [List.length_map, List.length_range] at h1
  obtain ⟨e0, e1, e2⟩ := entry_getElem (Q := Q) h1
  have hlr : j < (List.replicate Q.length ((e, d, 0) : ℕ × ℕ × ℕ)).length := by
    simpa using h1
  obtain ⟨d0, d1, -⟩ :=
    entry_getElem (Q := List.replicate Q.length ((e, d, 0) : ℕ × ℕ × ℕ)) hlr
  simp only [List.getElem_replicate] at d0 d1
  have hD : entry (List.replicate Q.length ((e, d, 0) : ℕ × ℕ × ℕ)) 0 j = e ∧
      entry (List.replicate Q.length ((e, d, 0) : ℕ × ℕ × ℕ)) 1 j = d := ⟨d0, d1⟩
  simp only [List.getElem_map, List.getElem_range]
  rw [e0, e1, e2, hD.1, hD.2]
  simp [Nat.mul_comm]

theorem mTower_const (Q : TrioSeq) (e d n : ℕ) :
    mTower Q (List.replicate Q.length ((e, d, 0) : ℕ × ℕ × ℕ)) n = gTower Q e d n := by
  unfold mTower gTower
  congr 1
  funext k
  exact bump_const Q e d k

/-- **(TOWER)** —— 実測が示す形をそのまま書き下したもの。**側条件はまだ確定していない**
（ここに置いた 3 本は `W_flatMap_copies` が使っているものに合わせた最小の候補）。

    D = 0（かつ A = Q）  `W_flatMap_copies`（`Wset.lean:2552`）**証明ずみ**
    D = (e,0,0) 一様      `ShiftTowerClosed`（`gTower_shTower` で橋渡し）
    D = (e,d,0) 一様      (LTOW)
    D が列ごとに違う      (MTOW)

⚠ **この形のままでは偽**（`D` が無制限）。側条件を決めるのが課題 L51-b の本体。 -/
def Tower : Prop :=
  ∀ (u n : ℕ) (A Q D : TrioSeq), A ∈ W u → Q ∈ W u →
    (∀ p ∈ Q, entry Q 0 0 ≤ p.1) → A ++ mTower Q D n ∈ W u

/-- **★ `(TOWER)` の `D = 0` かつ `A = []` は既に定理**。 -/
theorem tower_zero {u n : ℕ} {Q : TrioSeq} (hQ : Q ∈ W u)
    (hQr : ∀ p ∈ Q, entry Q 0 0 ≤ p.1) :
    mTower Q (List.replicate Q.length ((0, 0, 0) : ℕ × ℕ × ℕ)) n ∈ W u := by
  rw [mTower_const]
  exact gTow_zero hQ hQr


/-! ### 課題 L52-c: 行 316 `(0,0,0)(1,1,1)(1,1,1)` ＝ `gTower Q0 1 1 n` ＝ (LTOW) の最小事例 -/

theorem le1_le {M : TrioSeq} {a b : ℕ} (h : le1 M a b) : a ≤ b := by
  obtain ⟨-, -, h⟩ := h
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => exact le_trans ih (le_of_lt h2.2.2.1)

/-- `(0,0,0)(1,1,1)(1,1,1)` ＝ `psi(W_w * 2)`。**(LTOW) の最小事例**。 -/
def M316 : TrioSeq := [(0, 0, 0), (1, 1, 1), (1, 1, 1)]

@[simp] theorem entry_M316_00 : entry M316 0 0 = 0 := rfl
@[simp] theorem entry_M316_10 : entry M316 1 0 = 0 := rfl
@[simp] theorem entry_M316_20 : entry M316 2 0 = 0 := rfl
@[simp] theorem entry_M316_01 : entry M316 0 1 = 1 := rfl
@[simp] theorem entry_M316_11 : entry M316 1 1 = 1 := rfl
@[simp] theorem entry_M316_21 : entry M316 2 1 = 1 := rfl
@[simp] theorem entry_M316_02 : entry M316 0 2 = 1 := rfl
@[simp] theorem entry_M316_12 : entry M316 1 2 = 1 := rfl
@[simp] theorem entry_M316_22 : entry M316 2 2 = 1 := rfl

theorem lev_M316 : lev M316 0 = 0 := by simp [lev, entry, M316]

theorem srow_M316 : srow M316 2 = 2 := by simp [srow, entry, M316]

theorem nextrel0_M316_01 : nextrel0 M316 0 1 := by
  refine ⟨by simp [M316], by simp [M316], by omega, by simp [entry, M316], ?_⟩
  intro j hj
  omega

theorem nextrel0_M316_02 : nextrel0 M316 0 2 := by
  refine ⟨by simp [M316], by simp [M316], by omega, by simp [entry, M316], ?_⟩
  intro j hj
  have h1 : j = 1 := by omega
  subst h1
  simp [entry, M316]

theorem le0_M316_00 : le0 M316 0 0 :=
  ⟨by simp [M316], by simp [M316], Relation.ReflTransGen.refl⟩

theorem le0_M316_01 : le0 M316 0 1 :=
  ⟨by simp [M316], by simp [M316], Relation.ReflTransGen.single nextrel0_M316_01⟩

theorem le0_M316_02 : le0 M316 0 2 :=
  ⟨by simp [M316], by simp [M316], Relation.ReflTransGen.single nextrel0_M316_02⟩

theorem nextrel1_M316_01 : nextrel1 M316 0 1 := by
  refine ⟨by simp [M316], by simp [M316], by omega, by simp [entry, M316],
    le0_M316_01, ?_⟩
  intro j hj
  have h1 : j ≤ 1 := le0_le hj.2
  have h2 : j = 1 := by omega
  subst h2
  simp [entry, M316]

theorem nextrel1_M316_02 : nextrel1 M316 0 2 := by
  refine ⟨by simp [M316], by simp [M316], by omega, by simp [entry, M316],
    le0_M316_02, ?_⟩
  intro j hj
  have h1 : j ≤ 2 := le0_le hj.2
  have h3 : j < 3 := hj.2.1
  rcases j with _ | _ | _ | j
  · omega
  · simp [entry, M316]
  · simp [entry, M316]
  · omega

theorem le1_M316_00 : le1 M316 0 0 :=
  ⟨by simp [M316], by simp [M316], Relation.ReflTransGen.refl⟩

theorem le1_M316_01 : le1 M316 0 1 :=
  ⟨by simp [M316], by simp [M316], Relation.ReflTransGen.single nextrel1_M316_01⟩

theorem le1_M316_02 : le1 M316 0 2 :=
  ⟨by simp [M316], by simp [M316], Relation.ReflTransGen.single nextrel1_M316_02⟩

theorem nextrel2_M316_02 : nextrel2 M316 0 2 := by
  refine ⟨by simp [M316], by simp [M316], by omega, by simp [entry, M316],
    le1_M316_02, ?_⟩
  intro j hj
  have h1 : j ≤ 2 := le1_le hj.2
  have h3 : j < 3 := hj.2.1
  rcases j with _ | _ | _ | j
  · omega
  · simp [entry, M316]
  · simp [entry, M316]
  · omega

theorem nextrel2_M316_unique {j : ℕ} (h : nextrel2 M316 j 2) : j = 0 := by
  obtain ⟨hj3, -, -, hlt, -, -⟩ := h
  simp only [M316] at hj3
  simp at hj3
  rcases j with _ | _ | _ | j
  · rfl
  · simp [entry, M316] at hlt
  · simp [entry, M316] at hlt
  · omega

theorem nextR_M316_02 : nextR M316 2 0 2 := by
  rw [nextR]
  simp only [if_neg (by omega : (2 : ℕ) ≠ 0), if_neg (by omega : (2 : ℕ) ≠ 1)]
  exact nextrel2_M316_02

theorem hasParent_M316 : hasParent M316 2 2 := by
  refine ⟨0, nextR_M316_02, ?_⟩
  intro y hy
  rw [nextR] at hy
  simp only [if_neg (by omega : (2 : ℕ) ≠ 0), if_neg (by omega : (2 : ℕ) ≠ 1)] at hy
  exact nextrel2_M316_unique hy

theorem parent_M316 : parent M316 2 2 = 0 := by
  have hex : ∃ j0, nextR M316 2 j0 2 := ⟨0, nextR_M316_02⟩
  have hspec : nextR M316 2 (parent M316 2 2) 2 := Classical.epsilon_spec hex
  rw [nextR] at hspec
  simp only [if_neg (by omega : (2 : ℕ) ≠ 0), if_neg (by omega : (2 : ℕ) ≠ 1)] at hspec
  exact nextrel2_M316_unique hspec

/-- **★★ `M316⟦n⟧ = gTower Q0 1 1 n`**（行 0 も行 1 も段ごとに `+1`）。 -/
theorem oper_M316 (n : ℕ) : M316⟦n⟧ = gTower Q0 1 1 n := by
  have hl : M316.length - 1 = 2 := rfl
  have hp : parent M316 (srow M316 (M316.length - 1)) (M316.length - 1) = 0 :=
    parent_M316
  rw [oper]
  dsimp only
  split
  · exact absurd ‹M316.length - 1 = 0› (by decide)
  split
  · rename_i h
    exact absurd h.1 (by simp [entry, M316])
  split
  · rename_i h
    exact absurd hasParent_M316 h
  rw [hp, hl]
  have htake : M316.take 0 = [] := rfl
  rw [htake, List.nil_append]
  unfold gTower
  congr 1
  funext k
  have hr : List.range' 0 2 = [0, 1] := rfl
  rw [hr]
  simp [Q0, shiftr01, srow_M316, le0_M316_00, le1_M316_00, le0_M316_01, le1_M316_01,
    Nat.mul_comm]

/-- **★★★ 行 316 は (LTOW)（＝ `GTow`）の最小事例**。
実測ではこれ 1 本で覆いが 4.2% → 64.5% に跳ねる。 -/
theorem M316_mem_W_zero_of_gtow (h : GTow) : M316 ∈ W 0 := by
  refine A1_intro (Or.inr (Or.inl ?_))
  intro n hn
  rw [oper_M316]
  exact h 0 1 1 n Q0 Q0_mem_W_zero Q0_root

theorem M316_mem_Wself_of_gtow (h : GTow) : M316 ∈ Wself := by
  show M316 ∈ W (lev M316 0)
  rw [lev_M316]
  exact M316_mem_W_zero_of_gtow h


end L51T
end TRIO
