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

/-- **Slice equipment**: the context's prefix packages at the ambient root
`(v, z)`, with the stage and lift quantified.  All actual consumption stays in
the ambient slice, so the equipment need not carry foreign roots. -/
def CtxOK (M : TrioSeq) (v z : ℕ) : Prop :=
  ∀ k, k < M.length → ∀ a t : ℕ, 2 * (v + t) + z ≤ a →
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: M.take k) t ∈ W a

theorem ctxOK_take {M : TrioSeq} {v z : ℕ} (h : CtxOK M v z) (j : ℕ) :
    CtxOK (M.take j) v z := by
  intro k hk a t hva
  rw [List.take_take]
  have hk' : min k j < M.length := by
    rw [List.length_take] at hk
    omega
  exact h (min k j) hk' a t hva

/-- The machine's set: for every slice-equipped context, the graft obligations
of the element AND of all its prefixes (the latter feed context composition,
`ctxOK_graft` / `ctxOK_ltail`). -/
def GX : Set TrioSeq :=
  {y | based y → ∀ M : TrioSeq, argOK M → 2 ≤ M.length →
    ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
    ∀ i, i ≤ y.length → ∀ a t : ℕ, 2 * (v + t) + z ≤ a →
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M (y.take i)) t ∈ W a}

/-- The full-element obligation of a `GX`-member. -/
theorem GX_full {y M : TrioSeq} {v z a t : ℕ} (h : y ∈ GX) (hb : based y)
    (hM : argOK M) (hM2 : 2 ≤ M.length) (hctx : CtxOK M v z)
    (hz1 : z ≤ 1) (hva : 2 * (v + t) + z ≤ a) :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y) t ∈ W a := by
  have := h hb M hM hM2 v z hz1 hctx y.length le_rfl a t hva
  rwa [List.take_length] at this

/-- **Core γ' (blocked)**: the descended obligations. -/
def CoreBlocked : Prop :=
  ∀ (u : ℕ) (Y M : TrioSeq) (p : ℕ),
    Aop W u GX Y → based Y → Y ≠ [] →
    argOK M → 2 ≤ M.length →
    ¬ hasParent Y (srow Y (Y.length - 1)) (Y.length - 1) →
    hasParent (graft M Y) (srow (graft M Y) ((graft M Y).length - 1))
      ((graft M Y).length - 1) →
    parent (graft M Y) (srow (graft M Y) ((graft M Y).length - 1))
      ((graft M Y).length - 1) = p →
    p < M.length - 1 →
    ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
    ∀ a t n : ℕ, 2 * (v + t) + z ≤ a → 1 ≤ n →
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
    argOK M → 2 ≤ M.length →
    srow (graft M Y) ((graft M Y).length - 1) = 1 →
    (∃ m, domT (graft M Y) m) →
    ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
    ∀ a t : ℕ, 2 * (v + t) + z ≤ a →
      hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y)
        (srow (graft M Y) ((graft M Y).length - 1)) (graft M Y).length →
      Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y) t ∈ W a

/-- **Core β, family form**: only the slice-packages of the composite tower's
own lifted elements. -/
def CoreT2EFam : Prop :=
  ∀ (u : ℕ) (Y M : TrioSeq),
    (∀ n, 1 ≤ n → Y⟦n⟧ ∈ GX) → based Y → Y ≠ [] →
    argOK M → 2 ≤ M.length →
    srow (graft M Y) ((graft M Y).length - 1) = 2 →
    (∃ m, domT (graft M Y) m) →
    ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
      hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y)
        (srow (graft M Y) ((graft M Y).length - 1)) (graft M Y).length →
      ∀ j : ℕ, argOK (graft (graft M Y)
          (Lift1 ((((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y)⟦j⟧)
            (entry (graft M Y) 1 ((graft M Y).length - 1) - v))) →
        ∀ a s : ℕ, 2 * (v + s) + z ≤ a →
        Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft (graft M Y)
          (Lift1 ((((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y)⟦j⟧)
            (entry (graft M Y) 1 ((graft M Y).length - 1) - v))) s ∈ W a

/-- **Core β (row-2 tower over clause-2 data)**. -/
def CoreT2E : Prop :=
  ∀ (u : ℕ) (Y M : TrioSeq),
    (∀ n, 1 ≤ n → Y⟦n⟧ ∈ GX) → based Y → Y ≠ [] →
    argOK M → 2 ≤ M.length →
    srow (graft M Y) ((graft M Y).length - 1) = 2 →
    (∃ m, domT (graft M Y) m) →
    ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
    ∀ a t : ℕ, 2 * (v + t) + z ≤ a →
      hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y)
        (srow (graft M Y) ((graft M Y).length - 1)) (graft M Y).length →
      Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y) t ∈ W a


/-- The family core suffices: β's ∀-interface reduces to the family form. -/
theorem coreT2E_of_fam (hf : CoreT2EFam) : CoreT2E := by
  intro u Y M hop hbased hy hMarg hM2 hs2 hdG v z hz1 hctx a t hva hpN
  obtain ⟨m, hdm⟩ := hdG
  have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
  have hG : argOK (graft M Y) := argOK_graft hMne hMarg Y
  have hGne : graft M Y ≠ [] :=
    List.length_pos_iff.mp (by
      rw [graft_length]
      have : 0 < Y.length := List.length_pos_iff.mpr hy
      omega)
  exact towerGraft2_lift_mem_fam hG hGne hz1 hva hdm hs2
    (hf u Y M hop hbased hy hMarg hM2 hs2 ⟨m, hdm⟩ v z hz1 hctx hpN) hpN

theorem based_graft_arg {Y w : TrioSeq} (hy : Y ≠ []) (hbY : based Y)
    (hbw : based w) : based (graft Y w) := by
  classical
  rcases Y with _ | ⟨c, Y'⟩
  · exact absurd rfl hy
  · rcases Y' with _ | ⟨c1, Y''⟩
    · have hc : c = ((0, c.2.1, c.2.2) : ℕ × ℕ × ℕ) := by
        unfold based entry at hbY
        simp at hbY
        exact Prod.ext hbY rfl
      rw [hc, graft_Om]
      exact hbw
    · unfold based
      rw [graft_head_eq (by simp) hbw
        (graft_ne_nil (by simp))]
      exact hbY

/-- **Context composition**: the composite context `graft M Y` is equipped
whenever `M` is and the peel `Y.dropLast` is in the machine's set — the strict
composite prefixes are the `M`-prefixes plus the grafts of `Y`'s strict
prefixes, i.e. exactly the peel's element-prefix obligations. -/
theorem ctxOK_graft {M Y : TrioSeq} {v z : ℕ} (hMarg : argOK M)
    (hM2 : 2 ≤ M.length) (hz1 : z ≤ 1) (hctx : CtxOK M v z)
    (hYd : Y.dropLast ∈ GX) (hbY : based Y) :
    CtxOK (graft M Y) v z := by
  intro k hk a t hva
  rw [graft_length] at hk
  rcases Nat.lt_or_ge k M.length with hkM | hkM
  · rw [take_graft_low (by omega)]
    exact hctx k hkM a t hva
  · have hkk : k = M.length - 1 + (k - (M.length - 1)) := by omega
    rw [hkk, take_graft_high]
    have hres := hYd (based_dropLast hbY) M hMarg hM2 v z hz1 hctx
      (k - (M.length - 1)) (by rw [List.length_dropLast]; omega) a t hva
    rwa [dropLast_take (by omega)] at hres

/-- **Lifted-context equipment**: the lifted composite context's slice at the
lifted root `(v + t, z)` is fully supplied by the context's `(v, z)`-slice and
the peel's prefix obligations — the lifts compose (`Lift1_Lift1`) and the cone
is prefix-local (`ltail_take`). -/
theorem ctxOK_ltail {M Y : TrioSeq} {v z t : ℕ} (hMarg : argOK M)
    (hM2 : 2 ≤ M.length) (hz1 : z ≤ 1) (hctx : CtxOK M v z)
    (hYd : Y.dropLast ∈ GX) (hbY : based Y) :
    CtxOK (Wset.ltail v z (graft M Y) t) (v + t) z := by
  intro k hk a t' hva
  rw [Wset.ltail_length, graft_length] at hk
  have hkR : k ≤ (graft M Y).length := by rw [graft_length]; omega
  rw [Wset.ltail_take hkR, ← Wset.lift_cons, Lift1_Lift1]
  rcases Nat.lt_or_ge k M.length with hkM | hkM
  · rw [take_graft_low (by omega)]
    exact hctx k hkM a (t + t') (by omega)
  · have hkk : k = M.length - 1 + (k - (M.length - 1)) := by omega
    rw [hkk, take_graft_high]
    have hres := hYd (based_dropLast hbY) M hMarg hM2 v z hz1 hctx
      (k - (M.length - 1)) (by rw [List.length_dropLast]; omega) a (t + t')
      (by omega)
    rwa [dropLast_take (by omega)] at hres

/-- **The γ'-residue, element form**: the descended copies block is in the
machine's set (independent of the ambient root `(v, z, t)`). -/
def CoreBlockedElt : Prop :=
  ∀ (u : ℕ) (Y M : TrioSeq) (p : ℕ),
    Aop W u GX Y → based Y → Y ≠ [] →
    argOK M → 2 ≤ M.length →
    ¬ hasParent Y (srow Y (Y.length - 1)) (Y.length - 1) →
    hasParent (graft M Y) (srow (graft M Y) ((graft M Y).length - 1))
      ((graft M Y).length - 1) →
    parent (graft M Y) (srow (graft M Y) ((graft M Y).length - 1))
      ((graft M Y).length - 1) = p →
    p < M.length - 1 →
    ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
    ∀ n : ℕ, 1 ≤ n →
      shiftl0 (entry M 0 p)
        (gcopies (graft M Y) p ((graft M Y).length - 1 - p)
          (if 0 < srow (graft M Y) ((graft M Y).length - 1)
            then entry (graft M Y) 0 ((graft M Y).length - 1)
              - entry (graft M Y) 0 p else 0)
          (if 1 < srow (graft M Y) ((graft M Y).length - 1)
            then entry (graft M Y) 1 ((graft M Y).length - 1)
              - entry (graft M Y) 1 p else 0) n) ∈ GX

/-- **The γ'-residue, root slice**: a blocker at the context root descends to a
single-column context — the shift case, outside `GX`'s reach. -/
def CoreBlocked0 : Prop :=
  ∀ (u : ℕ) (Y M : TrioSeq),
    Aop W u GX Y → based Y → Y ≠ [] →
    argOK M → 2 ≤ M.length →
    ¬ hasParent Y (srow Y (Y.length - 1)) (Y.length - 1) →
    hasParent (graft M Y) (srow (graft M Y) ((graft M Y).length - 1))
      ((graft M Y).length - 1) →
    parent (graft M Y) (srow (graft M Y) ((graft M Y).length - 1))
      ((graft M Y).length - 1) = 0 →
    ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
    ∀ a t n : ℕ, 2 * (v + t) + z ≤ a → 1 ≤ n →
      Lift1 (((0, v, z) : ℕ × ℕ × ℕ)
        :: graft (M.take 1)
          (shiftl0 (entry M 0 0)
            (gcopies (graft M Y) 0 ((graft M Y).length - 1)
              (if 0 < srow (graft M Y) ((graft M Y).length - 1)
                then entry (graft M Y) 0 ((graft M Y).length - 1)
                  - entry (graft M Y) 0 0 else 0)
              (if 1 < srow (graft M Y) ((graft M Y).length - 1)
                then entry (graft M Y) 1 ((graft M Y).length - 1)
                  - entry (graft M Y) 1 0 else 0) n))) t ∈ W a

/-- **γ' reduces to (element membership + the root slice)**: away from the
root, the descended context `M.take (p+1)` is equipped by restriction, so the
package is a `GX` application of the copies element. -/
theorem coreBlocked_of_elt (he : CoreBlockedElt) (h0 : CoreBlocked0) :
    CoreBlocked := by
  intro u Y M p AY hbased hy hMarg hM2 hpY hpG hpar hplt
    v z hz1 hctx a t n hva hn
  rcases Nat.eq_zero_or_pos p with rfl | hp1
  · exact h0 u Y M AY hbased hy hMarg hM2 hpY hpG hpar
      v z hz1 hctx a t n hva hn
  · have helt := he u Y M p AY hbased hy hMarg hM2 hpY hpG hpar hplt
      v z hz1 hctx n hn
    have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
    have hyl : 0 < Y.length := List.length_pos_iff.mpr hy
    have hplt' : p < (graft M Y).length - 1 := by rw [graft_length]; omega
    have hlow : entry (graft M Y) 0 p = entry M 0 p := by
      rw [← entry_take (t := p + 1) (N := graft M Y) (by omega),
        take_graft_low (by omega), entry_take (by omega)]
    have hbe := based_blocked_element (M := M) (y := Y)
      (d0 := if 0 < srow (graft M Y) ((graft M Y).length - 1)
        then entry (graft M Y) 0 ((graft M Y).length - 1)
          - entry (graft M Y) 0 p else 0)
      (d1 := if 1 < srow (graft M Y) ((graft M Y).length - 1)
        then entry (graft M Y) 1 ((graft M Y).length - 1)
          - entry (graft M Y) 1 p else 0)
      n hn hplt' hlow
    have htk2 : 2 ≤ (M.take (p + 1)).length := by
      rw [List.length_take]; omega
    exact GX_full helt hbe (argOK_take hMarg (p + 1)) htk2
      (ctxOK_take hctx (p + 1)) hz1 hva

/-- **Core β, single-step form**: at a β-site (the argument's dead trailing
orphan `(w0, w1, w2)` revived by the root via row 2), grafting any `W`-element
at the sub-orphan stage `2*w1 + z` onto the argument lands in `GX`.  Since
`z < w2` at the site, this stage sits strictly below the orphan level
`lev = 2*w1 + w2` — the structural source of the probe's `t2 → t2` descent. -/
def CoreT2EStep : Prop :=
  ∀ (u : ℕ) (Y M : TrioSeq),
    (∀ n, 1 ≤ n → Y⟦n⟧ ∈ GX) → based Y → Y ≠ [] →
    argOK M → 2 ≤ M.length →
    srow (graft M Y) ((graft M Y).length - 1) = 2 →
    (∃ m, domT (graft M Y) m) →
    ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
      hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y)
        (srow (graft M Y) ((graft M Y).length - 1)) (graft M Y).length →
      ∀ e : TrioSeq,
        e ∈ W (2 * entry (graft M Y) 1 ((graft M Y).length - 1) + z) →
        based e → graft Y e ∈ GX

/-- **The family core reduces to the single-step core**: induction on the copy
index.  The base is the peel of the clause-2 datum (`Y.dropLast ∈ GX`, or the
context package when `Y` is a singleton); at the step, the previous obligation's
own `Wstar2` package puts the next tower element in `W (2*w1 + z)`, and the
step core re-expresses its graft through `graft_assoc` over the equipped
context. -/
theorem coreT2EFam_of_step (hs : CoreT2EStep) : CoreT2EFam := by
  classical
  intro u Y M hop hbased hy hMarg hM2 hs2 hdG v z hz1 hctx hpN
  obtain ⟨m, hdm⟩ := hdG
  have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
  have hylen : 0 < Y.length := List.length_pos_iff.mpr hy
  have hpY : ¬ hasParent Y (srow Y (Y.length - 1)) (Y.length - 1) :=
    fun hp => hdm.2 (hasParent_graft_inner hMne hy hp)
  have hR : argOK (graft M Y) := argOK_graft hMne hMarg Y
  have hRne : graft M Y ≠ [] :=
    List.length_pos_iff.mp (by rw [graft_length]; omega)
  set R : TrioSeq := graft M Y with hRdef
  set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
  set Nb : TrioSeq := p0 :: R with hNdef
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hNlen : Nb.length - 1 = R.length := by rw [hNdef]; simp
  have hE : ∀ i, entry Nb i R.length = entry R i (R.length - 1) :=
    fun i => entry_cons_last hRne i
  have hL : Nb.length - 1 ≠ 0 := by rw [hNlen]; omega
  have hxpos : 0 < entry R 0 (R.length - 1) :=
    hR _ (entry_pair_mem (B := R) (by omega))
  have hzz : ¬ (entry Nb 0 (Nb.length - 1) = 0 ∧ entry Nb 1 (Nb.length - 1) = 0 ∧
      entry Nb 2 (Nb.length - 1) = 0) := by
    rw [hNlen]; rintro ⟨h1, -, -⟩; rw [hE 0] at h1; omega
  have hsrN : srow Nb (Nb.length - 1) = 2 := by
    rw [hNlen, hNdef, srow_cons_last hRne, hs2]
  have hpN' : hasParent Nb (srow Nb (Nb.length - 1)) (Nb.length - 1) := by
    rw [hsrN, hNlen, hNdef, ← hs2]; exact hpN
  have hpar0 : parent Nb (srow Nb (Nb.length - 1)) (Nb.length - 1) = 0 := by
    rw [hsrN, hNlen]
    have := parent_cons_eq_zero (v := v) (z := z) hRne hdm hpN
    rwa [hs2] at this
  have hroot1 : entry Nb 1 0 = v := by rw [hNdef]; simp [entry, hp0]
  have hnr := parent_nextR hpN'
  rw [hpar0, hsrN] at hnr
  have hn2 : nextrel2 Nb 0 (Nb.length - 1) := by
    unfold nextR at hnr
    rw [if_neg (by omega), if_neg (by omega)] at hnr
    exact hnr
  have hle1lp : le1 Nb 0 (Nb.length - 1) := hn2.2.2.2.2.1
  have hwv : v < entry R 1 (R.length - 1) := by
    have := le1_entry1_lt hle1lp (by omega)
    rw [hroot1, hNlen, hE 1] at this
    exact this
  set d1 : ℕ := entry R 1 (R.length - 1) - v with hd1
  have hvd1 : v + d1 = entry R 1 (R.length - 1) := by omega
  have hN0 : Nb⟦0⟧ = [] := by
    rw [oper_gcopies 0 hL hzz hpN', hpar0]
    simp [gcopies]
  have hstep : ∀ i, Nb⟦i + 1⟧ = p0 :: graft R (Lift1 (Nb⟦i⟧) d1) := by
    intro i
    rw [hd1]
    exact oper_cons_tower2 hR hRne hdm hs2 hpN
  intro j
  induction j with
  | zero =>
      rw [hN0, Lift1_nil, graft_nil, hRdef, graft_dropLast hy]
      by_cases hY2 : 2 ≤ Y.length
      · have hYL : Y.length - 1 ≠ 0 := by omega
        have hpred : Y⟦1⟧ = Y.dropLast := by
          have he : Y⟦1⟧ = Pred Y := by
            by_cases hz0 : entry Y 0 (Y.length - 1) = 0 ∧
                entry Y 1 (Y.length - 1) = 0 ∧ entry Y 2 (Y.length - 1) = 0
            · exact oper_eq_pred_of_zero 1 hYL hz0
            · exact oper_eq_pred_of_noParent 1 hYL hz0 hpY
          rw [he]
          unfold Pred
          rw [if_neg (by omega)]
        have hYd : Y.dropLast ∈ GX := by
          have h := hop 1 le_rfl
          rwa [hpred] at h
        exact fun hargOK a' s ha =>
          GX_full hYd (based_dropLast hbased) hMarg hM2 hctx hz1 ha
      · have hYd : Y.dropLast = [] := by
          rw [List.dropLast_eq_take, show Y.length - 1 = 0 from by omega]
          rfl
        rw [hYd, graft_nil]
        intro hargOK a' s ha
        rw [List.dropLast_eq_take]
        exact hctx (M.length - 1) (by omega) a' s ha
  | succ i ih =>
      rw [hstep i]
      set Oj : TrioSeq := graft R (Lift1 (Nb⟦i⟧) d1) with hOj
      have hOarg : argOK Oj := argOK_graft hRne hR _
      have he : Lift1 (p0 :: Oj) d1 ∈ W (2 * (v + d1) + z) :=
        ih hOarg (2 * (v + d1) + z) d1 (le_refl _)
      have he' : Lift1 (p0 :: Oj) d1 ∈ W (2 * entry R 1 (R.length - 1) + z) := by
        rwa [hvd1] at he
      have hbe : based (Lift1 (p0 :: Oj) d1) :=
        based_Lift1 d1 (by simp [based, entry, hp0])
      have hgYe : graft Y (Lift1 (p0 :: Oj) d1) ∈ GX :=
        hs u Y M hop hbased hy hMarg hM2 hs2 ⟨m, hdm⟩ v z hz1 hctx hpN _ he' hbe
      intro hargOK a' s ha
      have hb2 : based (graft Y (Lift1 (p0 :: Oj) d1)) :=
        based_graft_arg hy hbased hbe
      have hres := GX_full hgYe hb2 hMarg hM2 hctx hz1 ha
      rw [← graft_assoc hy] at hres
      exact hres

/-- Direct wiring: the single-step core suffices for β. -/
theorem coreT2E_of_step (hs : CoreT2EStep) : CoreT2E :=
  coreT2E_of_fam (coreT2EFam_of_step hs)

theorem nil_mem_GX : ([] : TrioSeq) ∈ GX := by
  intro _ M _ hM2 v z _ hctx i _ a t hva
  rw [List.take_nil, graft_nil, List.dropLast_eq_take]
  exact hctx (M.length - 1) (by omega) a t hva

/-- **The shape-complete reduction of β**: the single-step core follows
outright from the machine's own inclusion `W ⊆ GX` — the composite's full and
prefix obligations all route through the equipped composite context
(`ctxOK_graft` + `take_graft_low/high` + `graft_assoc`).  The sole remaining
content of β is well-founding this self-reference. -/
theorem coreT2EStep_of_le (h : ∀ σ : ℕ, W σ ⊆ GX) : CoreT2EStep := by
  classical
  intro u Y M hop hbased hy hMarg hM2 hs2 hdG v z hz1 hctx hpN e he hbe
  obtain ⟨m, hdm⟩ := hdG
  have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
  have hylen : 0 < Y.length := List.length_pos_iff.mpr hy
  have hpY : ¬ hasParent Y (srow Y (Y.length - 1)) (Y.length - 1) :=
    fun hp => hdm.2 (hasParent_graft_inner hMne hy hp)
  have heGX : e ∈ GX := h _ he
  have hYd : Y.dropLast ∈ GX := by
    by_cases hY2 : 2 ≤ Y.length
    · have hYL : Y.length - 1 ≠ 0 := by omega
      have hpred : Y⟦1⟧ = Y.dropLast := by
        have hee : Y⟦1⟧ = Pred Y := by
          by_cases hz0 : entry Y 0 (Y.length - 1) = 0 ∧
              entry Y 1 (Y.length - 1) = 0 ∧ entry Y 2 (Y.length - 1) = 0
          · exact oper_eq_pred_of_zero 1 hYL hz0
          · exact oper_eq_pred_of_noParent 1 hYL hz0 hpY
        rw [hee]
        unfold Pred
        rw [if_neg (by omega)]
      have hh := hop 1 le_rfl
      rwa [hpred] at hh
    · have hYd0 : Y.dropLast = [] := by
        rw [List.dropLast_eq_take, show Y.length - 1 = 0 from by omega]
        rfl
      rw [hYd0]
      exact nil_mem_GX
  intro hbge M' hM'arg hM'2 v' z' hz' hctx' i hi a' t' ha'
  have hM'ne : M' ≠ [] := List.length_pos_iff.mp (by omega)
  rw [graft_length] at hi
  rcases Nat.lt_or_ge i Y.length with hiY | hiY
  · -- a prefix of the context part: the peel's own prefix obligation
    rw [take_graft_low (by omega)]
    have hres := hYd (based_dropLast hbased) M' hM'arg hM'2 v' z' hz' hctx' i
      (by rw [List.length_dropLast]; omega) a' t' ha'
    rwa [dropLast_take (by omega)] at hres
  · -- at or above the graft point: the element's prefix obligation over the
    -- equipped composite context
    have hSarg : argOK (graft M' Y) := argOK_graft hM'ne hM'arg Y
    have hS2 : 2 ≤ (graft M' Y).length := by rw [graft_length]; omega
    have hSctx : CtxOK (graft M' Y) v' z' :=
      ctxOK_graft hM'arg hM'2 hz' hctx' hYd hbased
    have hres := heGX hbe (graft M' Y) hSarg hS2 v' z' hz' hSctx
      (i - (Y.length - 1)) (by omega) a' t' ha'
    rw [graft_assoc hy] at hres
    rw [show i = Y.length - 1 + (i - (Y.length - 1)) from by omega,
      take_graft_high]
    exact hres

open Classical in
/-- **α reduces to the machine's own inclusion**: the lifted block is a
root-parented row-1 tower over the lifted composite context at stage `m + 2t`;
its closure obligations route through `GX` at that context, whose slice
equipment at the lifted root is synthesized by `ctxOK_ltail` — the stage is
free because the packages are stage-quantified. -/
theorem coreT1L_of_le (h : ∀ σ : ℕ, W σ ⊆ GX) : CoreT1L := by
  classical
  intro u Y M AY hbased hy hMarg hM2 hs1 hdG v z hz1 hctx a t hva hpN
  obtain ⟨m, hd⟩ := hdG
  have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
  have hylen : 0 < Y.length := List.length_pos_iff.mpr hy
  have hR : argOK (graft M Y) := argOK_graft hMne hMarg Y
  have hRne : graft M Y ≠ [] :=
    List.length_pos_iff.mp (by rw [graft_length]; omega)
  have hR2 : 2 ≤ (graft M Y).length := by rw [graft_length]; omega
  have hpY : ¬ hasParent Y (srow Y (Y.length - 1)) (Y.length - 1) :=
    fun hp => hd.2 (hasParent_graft_inner hMne hy hp)
  have hYd : Y.dropLast ∈ GX := by
    by_cases hY2 : 2 ≤ Y.length
    · rcases AY with ⟨hl, -⟩ | hop | ⟨m', -, -, hgr'⟩
      · omega
      · have hYL : Y.length - 1 ≠ 0 := by omega
        have hpred : Y⟦1⟧ = Y.dropLast := by
          have hee : Y⟦1⟧ = Pred Y := by
            by_cases hz0 : entry Y 0 (Y.length - 1) = 0 ∧
                entry Y 1 (Y.length - 1) = 0 ∧ entry Y 2 (Y.length - 1) = 0
            · exact oper_eq_pred_of_zero 1 hYL hz0
            · exact oper_eq_pred_of_noParent 1 hYL hz0 hpY
          rw [hee]
          unfold Pred
          rw [if_neg (by omega)]
        have hh := hop 1 le_rfl
        rwa [hpred] at hh
      · have hh := hgr' [] (W_nil m') based_nil
        rwa [graft_nil] at hh
    · have hYd0 : Y.dropLast = [] := by
        rw [List.dropLast_eq_take, show Y.length - 1 = 0 from by omega]
        rfl
      rw [hYd0]
      exact nil_mem_GX
  set R : TrioSeq := graft M Y with hRdef
  set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
  set Nb : TrioSeq := p0 :: R with hNbdef
  set Rt : TrioSeq := Wset.ltail v z R t with hRtdef
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hRtlen : Rt.length = R.length := Wset.ltail_length
  have hRtne : Rt ≠ [] := Wset.ltail_ne hRne
  have hRtOK : argOK Rt := Wset.argOK_ltail hR
  have hpar0 := parent_cons_eq_zero hRne hd hpN
  have hnr := parent_nextR hpN
  rw [hpar0, hs1] at hnr
  have hn1 : nextrel1 Nb 0 R.length := by
    unfold nextR at hnr
    rw [if_neg (by omega), if_pos rfl] at hnr
    exact hnr
  have hcone : le1 Nb 0 R.length :=
    ⟨hn1.1, hn1.2.1, Relation.ReflTransGen.single hn1⟩
  have hconej : le1 Nb 0 ((R.length - 1) + 1) := by
    rw [← len_succ hRne]
    exact hcone
  have hsrRt : srow Rt (Rt.length - 1) = 1 := by
    rw [hRtlen, hRtdef, Wset.srow_ltail]; exact hs1
  have hlevRt : lev Rt (Rt.length - 1) = (m + 2 * t) + 1 := by
    unfold lev
    rw [hRtlen, hRtdef, Wset.entry2_ltail, Wset.entry1_ltail_of_cone hconej]
    have hm := hd.1
    unfold lev at hm
    omega
  have hdRt : domT Rt (m + 2 * t) := by
    refine ⟨hlevRt, ?_⟩
    rw [hRtlen, hRtdef, Wset.srow_ltail, Wset.hasParent_ltail]
    exact hd.2
  have hpMt : hasParent (((0, v + t, z) : ℕ × ℕ × ℕ) :: Rt)
      (srow Rt (Rt.length - 1)) Rt.length := by
    rw [← Wset.lift_cons, hsrRt, hRtlen, ← hs1]
    exact hasParent_Lift1.mpr hpN
  have hRt2 : 2 ≤ Rt.length := by rw [hRtlen]; exact hR2
  have hctxRt : CtxOK Rt (v + t) z :=
    ctxOK_ltail hMarg hM2 hz1 hctx hYd hbased
  have hgr : ∀ y' ∈ W (m + 2 * t), based y' → argOK (graft Rt y') →
      ∀ a' : ℕ, 2 * (v + t) + z ≤ a' →
      Lift1 (((0, v + t, z) : ℕ × ℕ × ℕ) :: graft Rt y') 0 ∈ W a' := by
    intro y' hy' hb hargOK a' ha'
    exact GX_full (h _ hy') hb hRtOK hRt2 hctxRt hz1 (by omega)
  refine A1_intro (Or.inr (Or.inl (fun n hn => ?_)))
  rw [hNbdef, Wset.lift_cons, ← hRtdef,
    oper_cons_tower1 hRtOK hRtne hdRt hsrRt hpMt]
  exact tower1_mem2 hRtOK hRtne hz1 hva hdRt hsrRt hgr hpMt n

open Classical in
/-- **The GX machine closes** modulo the three cores. -/
theorem GX_closed (hb : CoreBlocked) (h1 : CoreT1L) (h2 : CoreT2E) :
    ∀ (u : ℕ) (Y : TrioSeq), Aop W u GX Y → Y ∈ GX := by
  intro u Y AY
  intro hbased M hMarg hM2 v z hz1 hctx i hi a t hva
  have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
  rcases Nat.lt_or_eq_of_le hi with hilt | hieq
  · -- element-prefix obligations: uniform one-step discharge from the datum
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      rw [List.take_zero, graft_nil, List.dropLast_eq_take]
      exact hctx (M.length - 1) (by omega) a t hva
    · have hY2 : 2 ≤ Y.length := by omega
      rcases AY with ⟨hl, -⟩ | hop | ⟨m, -, -, hgr⟩
      · omega
      · -- clause 2: prefixes are preserved by one expansion
        have hd1 := hop 1 le_rfl
        have hlen1 : i ≤ (Y⟦1⟧).length := by
          obtain ⟨R, hR⟩ := oper_eq_dropLast_append (M := Y) (n := 1)
            (by omega) le_rfl
          rw [hR, List.length_append, List.length_dropLast]
          omega
        have hres := hd1 (based_oper le_rfl hbased) M hMarg hM2 v z hz1 hctx
          i hlen1 a t hva
        rwa [oper_take_prefix (by omega) le_rfl (by omega)] at hres
      · -- clause 3: prefixes of the peel (`w := []`)
        have hd0 := hgr [] (W_nil m) based_nil
        rw [graft_nil] at hd0
        have hres := hd0 (based_dropLast hbased) M hMarg hM2 v z hz1 hctx i
          (by rw [List.length_dropLast]; omega) a t hva
        rwa [dropLast_take (by omega)] at hres
  rw [hieq, List.take_length]
  by_cases hy : Y = []
  · subst hy
    rw [graft_nil, List.dropLast_eq_take]
    exact hctx (M.length - 1) (by omega) a t hva
  have hylen : 0 < Y.length := List.length_pos_iff.mpr hy
  have hG : argOK (graft M Y) := argOK_graft hMne hMarg Y
  have hGne : graft M Y ≠ [] :=
    List.length_pos_iff.mp (by rw [graft_length]; omega)
  have hGlen : 2 ≤ (graft M Y).length := by rw [graft_length]; omega
  have hGL : (graft M Y).length - 1 ≠ 0 := by omega
  by_cases hpY : hasParent Y (srow Y (Y.length - 1)) (Y.length - 1)
  · -- (a) inner
    have hyL : Y.length - 1 ≠ 0 := by
      have := nextR_index_lt (parent_nextR hpY)
      omega
    refine A1_intro (Or.inr (Or.inl fun n hn => ?_))
    rw [lift_graft_inner_step v z t n hMne hy hyL hG hpY]
    rcases AY with ⟨hl, -⟩ | hop | ⟨m, -, hd, -⟩
    · omega
    · exact GX_full (hop n hn) (based_oper hn hbased) hMarg hM2 hctx hz1 hva
    · exact absurd hpY hd.2
  by_cases hpG : hasParent (graft M Y)
      (srow (graft M Y) ((graft M Y).length - 1)) ((graft M Y).length - 1)
  · -- (γ) blocked
    have hplt := blocked_parent_lt hMne hy hpY hpG
    refine A1_intro (Or.inr (Or.inl fun n hn => ?_))
    rw [lift_graft_blocked_step v z t n hMne hy hG hGL hpG rfl hplt]
    exact hb u Y M _ AY hbased hy hMarg hM2 hpY hpG rfl hplt
      v z hz1 hctx a t n hva hn
  -- trailing dead within the graft block
  have hdrop : Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y.dropLast) t ∈ W a := by
    by_cases hY2 : 2 ≤ Y.length
    · have hYd : Y.dropLast ∈ GX := by
        rcases AY with ⟨hl, -⟩ | hop | ⟨m, -, -, hgr⟩
        · omega
        · have hYL : Y.length - 1 ≠ 0 := by omega
          have hpred : Y⟦1⟧ = Y.dropLast := by
            have he : Y⟦1⟧ = Pred Y := by
              by_cases hz0 : entry Y 0 (Y.length - 1) = 0 ∧
                  entry Y 1 (Y.length - 1) = 0 ∧ entry Y 2 (Y.length - 1) = 0
              · exact oper_eq_pred_of_zero 1 hYL hz0
              · exact oper_eq_pred_of_noParent 1 hYL hz0 hpY
            rw [he]
            unfold Pred
            rw [if_neg (by omega)]
          have h := hop 1 le_rfl
          rwa [hpred] at h
        · have h := hgr [] (W_nil m) based_nil
          rwa [graft_nil] at h
      exact GX_full hYd (based_dropLast hbased) hMarg hM2 hctx hz1 hva
    · have hYd : Y.dropLast = [] := by
        rw [List.dropLast_eq_take, show Y.length - 1 = 0 from by omega]
        rfl
      rw [hYd, graft_nil, List.dropLast_eq_take]
      exact hctx (M.length - 1) (by omega) a t hva
  by_cases hw0 : lev (graft M Y) ((graft M Y).length - 1) = 0
  · -- (b) succ: the lifted block sheds unshifted copies
    have hsr0 : srow (graft M Y) ((graft M Y).length - 1) = 0 := by
      unfold srow
      unfold lev at hw0
      rw [if_neg (by omega), if_neg (by omega)]
    set N : TrioSeq := ((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y with hN
    set Rt : TrioSeq := Wset.ltail v z (graft M Y) t with hRt
    have hRtlen : Rt.length = (graft M Y).length := Wset.ltail_length
    have hRtne : Rt ≠ [] := Wset.ltail_ne hGne
    have hRtOK : argOK Rt := Wset.argOK_ltail hG
    have hwt : lev Rt (Rt.length - 1) = 0 := by
      rw [hRtlen, hRt]
      exact Wset.lev_ltail_of_zero hw0
    have hnpt : ¬ hasParent Rt 0 (Rt.length - 1) := by
      rw [hRtlen, hRt, Wset.hasParent_ltail]
      rw [← hsr0]
      exact hpG
    refine A1_intro (Or.inr (Or.inl fun n hn => ?_))
    rw [Wset.lift_cons, ← hRt, oper_cons_succ hRtOK hRtne hwt hnpt]
    refine W_flatMap_copies ?_ (rsum_self_cons (v + t) z _) n
    have hkey : ((0, v + t, z) : ℕ × ℕ × ℕ) :: Rt.dropLast
        = Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y.dropLast) t := by
      rw [hRt, Wset.ltail_dropLast, graft_dropLast hy]
    rw [hkey]
    exact hdrop
  · -- towers or dead
    by_cases hpN : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y)
        (srow (graft M Y) ((graft M Y).length - 1)) (graft M Y).length
    · -- revived by the root
      have hdG : domT (graft M Y) (lev (graft M Y) ((graft M Y).length - 1) - 1) :=
        ⟨by omega, hpG⟩
      have hsplit : srow (graft M Y) ((graft M Y).length - 1) = 1 ∨
          srow (graft M Y) ((graft M Y).length - 1) = 2 := by
        unfold srow
        unfold lev at hw0
        by_cases h2' : 0 < entry (graft M Y) 2 ((graft M Y).length - 1)
        · rw [if_pos h2']; exact Or.inr rfl
        · rw [if_neg h2', if_pos (by omega)]; exact Or.inl rfl
      rcases hsplit with hs1 | hs2
      · exact h1 u Y M AY hbased hy hMarg hM2 hs1 ⟨_, hdG⟩
          v z hz1 hctx a t hva (by rw [hs1] at hpN ⊢; exact hpN)
      · rcases AY with ⟨hl, hw⟩ | hop | ⟨m, -, hd, hgr⟩
        · exfalso
          have hY1 : Y.length = 1 := by omega
          have := lev_graft_last (M := M) hy
          rw [hY1] at this
          simp at this
          rw [this, hw] at hw0
          exact hw0 rfl
        · exact h2 u Y M hop hbased hy hMarg hM2 hs2 ⟨_, hdG⟩
            v z hz1 hctx a t hva (by rw [hs2] at hpN ⊢; exact hpN)
        · -- (d) the proven row-2 graft tower
          have hlev : lev (graft M Y) ((graft M Y).length - 1) = m + 1 := by
            rw [lev_graft_last hy]
            exact hd.1
          have hdGm : domT (graft M Y) m := ⟨hlev, hpG⟩
          refine towerGraft2_lift_mem hG hGne hz1 hva hdGm hs2 ?_
            (by rw [hs2] at hpN ⊢; exact hpN)
          intro w hw hbw hargOK a' s ha
          rw [graft_assoc hy]
          have hYw : graft Y w ∈ GX := hgr w hw hbw
          exact GX_full hYw (based_graft_arg hy hbased hbw) hMarg hM2 hctx
            hz1 ha
    · -- (c) still dead: peel
      refine A1_intro (Or.inr (Or.inl fun n hn => ?_))
      have hnp' : ¬ hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y)
          (srow (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y)
            ((((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y).length - 1))
          ((((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y).length - 1) := by
        rw [cons_length, srow_cons_last hGne]
        exact hpN
      rw [lift_graft_dead_step v z t n hMne hy
        (by simp only [List.length_cons]; omega) hnp']
      exact hdrop


/-- **A2 corollary**: every `W`-element is in the machine's set. -/
theorem W_le_GX (hb : CoreBlocked) (h1 : CoreT1L) (h2 : CoreT2E) (u : ℕ) :
    W u ⊆ GX :=
  A2' (fun Y hY => GX_closed hb h1 h2 u Y hY)

/-- **GraftAll for equipped contexts**, modulo the three cores: the missing
graft closure at every stage, for every context whose prefix packages are
supplied (by the master length induction). -/
theorem graftAll_of_GX (hb : CoreBlocked) (h1 : CoreT1L) (h2 : CoreT2E) :
    ∀ S : TrioSeq, argOK S → 2 ≤ S.length →
      (∀ v z : ℕ, z ≤ 1 → CtxOK S v z) →
      ∀ (u : ℕ) (y : TrioSeq), y ∈ W u → based y → graft S y ∈ Wstar2 := by
  intro S hS hS2 hctx u y hy hby
  have hyGX : y ∈ GX := W_le_GX hb h1 h2 u hy
  exact fun hargOK v z a t hz1 hva =>
    GX_full hyGX hby hS hS2 (hctx v z hz1) hz1 hva

/-- **The assembly loop, explicit**: modulo the γ'-core and the lifted-context
equipment, the machine's closure consumes only its own inclusion `W ⊆ GX`
(α via `coreT1L_of_le`, β via `coreT2EStep_of_le`).  Well-founding this
self-reference — with the provenance descent measured in `probe_strat`
(β-orphans = context material, position non-increasing; α-orphans = planted
roots, stage-bounded) — is the single remaining task of the campaign. -/
theorem GX_loop (he : CoreBlockedElt) (h0 : CoreBlocked0)
    (h : ∀ σ : ℕ, W σ ⊆ GX) :
    ∀ (u : ℕ) (Y : TrioSeq), Aop W u GX Y → Y ∈ GX :=
  GX_closed (coreBlocked_of_elt he h0) (coreT1L_of_le h)
    (coreT2E_of_step (coreT2EStep_of_le h))

end TRIO
