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

end L51T
end TRIO
