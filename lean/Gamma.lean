/-
Gamma.lean: γ 装置のステップ合成。

`Lift1 ((0,v,z)::graft M y) t` の展開を、graft 三分法（Xbar）と
リフト同変性（Lcone / `liftInner_holds`）で義務レベルに落とす:

  inner   : (Lift1 N t)⟦n⟧ = Lift1 ((0,v,z)::graft M (y⟦n⟧)) t
  blocked : (Lift1 N t)⟦n⟧ = Lift1 ((0,v,z)::graft (M.take (p+1)) Y') t
            （文脈が厳密に短くなる）

N = (0,v,z)::graft M y。どちらも既証明補題の合成。
-/
import Lcone
import Xbar

namespace TRIO

open Wset

/-- **The (a)-branch step**: an inner parent lets the lifted obligation recurse
into the argument's expansion. -/
theorem lift_graft_inner_step {M y : TrioSeq} (v z t n : ℕ)
    (hM : M ≠ []) (hy : y ≠ []) (hyL : y.length - 1 ≠ 0)
    (hG : argOK (graft M y))
    (hp : hasParent y (srow y (y.length - 1)) (y.length - 1)) :
    (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y) t)⟦n⟧
      = Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M (y⟦n⟧)) t := by
  have hGne : graft M y ≠ [] :=
    List.length_pos_iff.mp (by
      rw [graft_length]
      have h1 : 0 < y.length := List.length_pos_iff.mpr hy
      omega)
  have hpG := hasParent_graft_inner hM hy hp
  rw [liftInner_holds v z t n (graft M y) hG hGne hpG,
    oper_cons_nat hG hGne hpG, oper_graft_inner n hM hy hyL hp]

/-- **The γ-branch step**: a blocked parent lets the lifted obligation recurse
onto a strictly shorter context. -/
theorem lift_graft_blocked_step {M y : TrioSeq} {p : ℕ} (v z t n : ℕ)
    (hM : M ≠ []) (hy : y ≠ [])
    (hG : argOK (graft M y))
    (hL : (graft M y).length - 1 ≠ 0)
    (hpG : hasParent (graft M y)
      (srow (graft M y) ((graft M y).length - 1)) ((graft M y).length - 1))
    (hpar : parent (graft M y) (srow (graft M y) ((graft M y).length - 1))
      ((graft M y).length - 1) = p)
    (hplt : p < M.length - 1) :
    (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y) t)⟦n⟧
      = Lift1 (((0, v, z) : ℕ × ℕ × ℕ)
          :: graft (M.take (p + 1))
            (shiftl0 (entry M 0 p)
              (gcopies (graft M y) p ((graft M y).length - 1 - p)
                (if 0 < srow (graft M y) ((graft M y).length - 1)
                  then entry (graft M y) 0 ((graft M y).length - 1)
                    - entry (graft M y) 0 p else 0)
                (if 1 < srow (graft M y) ((graft M y).length - 1)
                  then entry (graft M y) 1 ((graft M y).length - 1)
                    - entry (graft M y) 1 p else 0) n))) t := by
  have hGne : graft M y ≠ [] :=
    List.length_pos_iff.mp (by
      rw [graft_length]
      have h1 : 0 < y.length := List.length_pos_iff.mpr hy
      omega)
  rw [liftInner_holds v z t n (graft M y) hG hGne hpG,
    oper_cons_nat hG hGne hpG,
    oper_graft_blocked n hM hy hL hpG hpar hplt]


/-- **The peel step**: a dead trailing column (no parent even with the root)
peels, and the lift passes through. -/
theorem lift_graft_dead_step {M y : TrioSeq} (v z t n : ℕ)
    (hM : M ≠ []) (hy : y ≠ [])
    (hlen2 : 1 < (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y).length)
    (hnp : ¬ hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y)
      (srow (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y)
        ((((0, v, z) : ℕ × ℕ × ℕ) :: graft M y).length - 1))
      ((((0, v, z) : ℕ × ℕ × ℕ) :: graft M y).length - 1)) :
    (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y) t)⟦n⟧
      = Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y.dropLast) t := by
  classical
  set N : TrioSeq := ((0, v, z) : ℕ × ℕ × ℕ) :: graft M y with hN
  have hGne : graft M y ≠ [] :=
    List.length_pos_iff.mp (by
      rw [graft_length]
      have h1 : 0 < y.length := List.length_pos_iff.mpr hy
      omega)
  have hLN : (Lift1 N t).length - 1 ≠ 0 := by
    rw [Lift1_length, hN]
    simp only [List.length_cons]
    have : 0 < (graft M y).length := List.length_pos_iff.mpr hGne
    omega
  have hnpL : ¬ hasParent (Lift1 N t)
      (srow (Lift1 N t) ((Lift1 N t).length - 1)) ((Lift1 N t).length - 1) := by
    rw [Lift1_length, srow_Lift1 (by
      rw [hN]
      simp only [List.length_cons]
      have : 0 < (graft M y).length := List.length_pos_iff.mpr hGne
      omega), hasParent_Lift1]
    exact hnp
  have hpred : (Lift1 N t)⟦n⟧ = Pred (Lift1 N t) := by
    by_cases hz : entry (Lift1 N t) 0 ((Lift1 N t).length - 1) = 0 ∧
        entry (Lift1 N t) 1 ((Lift1 N t).length - 1) = 0 ∧
        entry (Lift1 N t) 2 ((Lift1 N t).length - 1) = 0
    · exact oper_eq_pred_of_zero n hLN hz
    · exact oper_eq_pred_of_noParent n hLN hz hnpL
  rw [hpred]
  unfold Pred
  rw [if_neg (by rw [Lift1_length]; omega), Lift1_dropLast, hN,
    dropLast_cons hGne, graft_dropLast hy]


/-! ## GX 機械の補助 -/

theorem based_oper {B : TrioSeq} {n : ℕ} (hn : 1 ≤ n) (h : based B) :
    based (B⟦n⟧) := by
  unfold based at h ⊢
  rw [oper_head_eq hn, h]

theorem based_dropLast {B : TrioSeq} (h : based B) : based B.dropLast := by
  rcases B with _ | ⟨b0, B'⟩
  · simp
  · rcases B' with _ | ⟨b1, B''⟩
    · simp [based, entry]
    · unfold based at h ⊢
      simpa [entry] using h

/-- Rows 1 and 2 of the graft block's trailing column are the argument's. -/
theorem lev_graft_last {M y : TrioSeq} (hy : y ≠ []) :
    lev (graft M y) ((graft M y).length - 1) = lev y (y.length - 1) := by
  classical
  have hylen : 0 < y.length := List.length_pos_iff.mpr hy
  unfold lev
  rw [graft_eq_shift]
  have hlen : (M.dropLast ++ shiftr01 (entry M 0 (M.length - 1)) 0 y).length - 1
      = M.dropLast.length + (y.length - 1) := by
    rw [List.length_append, shiftr01_length]
    omega
  rw [hlen, entry_append_right, entry_append_right, entry1_shiftr01,
    entry2_shiftr01]


/-! ## GX 機械

`CtxOK M` = 全接頭辞パッケージ（MASTER の長さ帰納が供給）。
`GX` = 装備付き文脈すべてに対する graft-義務の集合。 -/

def CtxOK (M : TrioSeq) : Prop :=
  ∀ k, k ≤ M.length → ∀ v z a t : ℕ, z ≤ 1 → 2 * (v + t) + z ≤ a →
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: M.take k) t ∈ W a

theorem ctxOK_take {M : TrioSeq} (h : CtxOK M) (j : ℕ) : CtxOK (M.take j) := by
  intro k hk v z a t hz1 hva
  rw [List.take_take]
  have hk' : min k j ≤ M.length := by
    rw [List.length_take] at hk
    omega
  exact h (min k j) hk' v z a t hz1 hva

def GX : Set TrioSeq :=
  {y | based y → ∀ M : TrioSeq, argOK M → 2 ≤ M.length → CtxOK M →
    ∀ v z a t : ℕ, z ≤ 1 → 2 * (v + t) + z ≤ a →
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y) t ∈ W a}

/-- **Core γ' (blocked)**: the descended obligations. -/
def CoreBlocked : Prop :=
  ∀ (u : ℕ) (Y M : TrioSeq) (p : ℕ),
    Aop W u GX Y → based Y → Y ≠ [] →
    argOK M → 2 ≤ M.length → CtxOK M →
    ¬ hasParent Y (srow Y (Y.length - 1)) (Y.length - 1) →
    hasParent (graft M Y) (srow (graft M Y) ((graft M Y).length - 1))
      ((graft M Y).length - 1) →
    parent (graft M Y) (srow (graft M Y) ((graft M Y).length - 1))
      ((graft M Y).length - 1) = p →
    p < M.length - 1 →
    ∀ v z a t n : ℕ, z ≤ 1 → 2 * (v + t) + z ≤ a → 1 ≤ n →
      Lift1 (((0, v, z) : ℕ × ℕ × ℕ)
        :: graft (M.take (p + 1))
          (shiftl0 (entry M 0 p)
            (gcopies (graft M Y) p ((graft M Y).length - 1 - p)
              (if 0 < srow (graft M Y) ((graft M Y).length - 1)
                then entry (graft M Y) 0 ((graft M Y).length - 1)
                  - entry (graft M Y) 0 p else 0)
              (if 1 < srow (graft M Y) ((graft M Y).length - 1)
                then entry (graft M Y) 1 ((graft M Y).length - 1)
                  - entry (graft M Y) 1 p else 0) n))) t ∈ W a

/-- **Core α (row-1 tower under lift)**. -/
def CoreT1L : Prop :=
  ∀ (u : ℕ) (Y M : TrioSeq),
    Aop W u GX Y → based Y → Y ≠ [] →
    argOK M → 2 ≤ M.length → CtxOK M →
    srow (graft M Y) ((graft M Y).length - 1) = 1 →
    (∃ m, domT (graft M Y) m) →
    ∀ v z a t : ℕ, z ≤ 1 → 2 * (v + t) + z ≤ a →
      hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y)
        (srow (graft M Y) ((graft M Y).length - 1)) (graft M Y).length →
      Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y) t ∈ W a

/-- **Core β (row-2 tower over clause-2 data)**. -/
def CoreT2E : Prop :=
  ∀ (u : ℕ) (Y M : TrioSeq),
    (∀ n, 1 ≤ n → Y⟦n⟧ ∈ GX) → based Y → Y ≠ [] →
    argOK M → 2 ≤ M.length → CtxOK M →
    srow (graft M Y) ((graft M Y).length - 1) = 2 →
    (∃ m, domT (graft M Y) m) →
    ∀ v z a t : ℕ, z ≤ 1 → 2 * (v + t) + z ≤ a →
      hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y)
        (srow (graft M Y) ((graft M Y).length - 1)) (graft M Y).length →
      Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y) t ∈ W a

end TRIO
