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
import Cgraft
import Aexp
import Croot

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
  {y | based y → ∀ M : TrioSeq, argOK M → 1 ≤ M.length →
    ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
    ∀ i, i ≤ y.length → ∀ a t : ℕ, 2 * (v + t) + z ≤ a →
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M (y.take i)) t ∈ W a}

/-- **The staircase-closed machine set**: `GX` together with all its staircase
lifts.  `slift` composes (`slift_slift` + `stair_comp`), so `GXs` is closed
under staircase lifts BY DEFINITION — that is the (e)-wall's data side. -/
def GXs : Set TrioSeq := {y | y ∈ GX ∧ ∀ φ : ℕ → ℕ, Stair φ → slift y φ ∈ GX}

theorem gxs_le_gx : GXs ⊆ GX := fun _ h => h.1

theorem gxs_slift {y : TrioSeq} (h : y ∈ GXs) {φ : ℕ → ℕ} (hφ : Stair φ) :
    slift y φ ∈ GXs := by
  refine ⟨h.2 φ hφ, fun ψ hψ => ?_⟩
  rw [slift_slift hφ hψ]
  exact h.2 (fun m => ψ (φ m)) (stair_comp hφ hψ)

/-- The ambient mask lift of a `GXs`-member stays in `GX`. -/
theorem gxs_mlift {y : TrioSeq} (h : y ∈ GXs) (v t : ℕ) : mlift y v t ∈ GX := by
  rw [mlift_eq_slift]
  exact h.2 (fun m => m + (if v < m then t else 0)) (stair_step v t)

/-- The full-element obligation of a `GX`-member. -/
theorem GX_full {y M : TrioSeq} {v z a t : ℕ} (h : y ∈ GX) (hb : based y)
    (hM : argOK M) (hM2 : 1 ≤ M.length) (hctx : CtxOK M v z)
    (hz1 : z ≤ 1) (hva : 2 * (v + t) + z ≤ a) :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M y) t ∈ W a := by
  have := h hb M hM hM2 v z hz1 hctx y.length le_rfl a t hva
  rwa [List.take_length] at this

/-- **Core γ' (blocked)**: the descended obligations. -/
def CoreBlocked : Prop :=
  ∀ (u : ℕ) (Y M : TrioSeq) (p : ℕ),
    Y.dropLast ∈ GXs → based Y → Y ≠ [] →
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
    Y.dropLast ∈ GXs → based Y → Y ≠ [] →
    argOK M → 1 ≤ M.length →
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
    Y.dropLast ∈ GX → based Y → Y ≠ [] →
    argOK M → 1 ≤ M.length →
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
    Y.dropLast ∈ GX → based Y → Y ≠ [] →
    argOK M → 1 ≤ M.length →
    srow (graft M Y) ((graft M Y).length - 1) = 2 →
    (∃ m, domT (graft M Y) m) →
    ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
    ∀ a t : ℕ, 2 * (v + t) + z ≤ a →
      hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y)
        (srow (graft M Y) ((graft M Y).length - 1)) (graft M Y).length →
      Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y) t ∈ W a


/-- The family core suffices: β's ∀-interface reduces to the family form. -/
theorem coreT2E_of_fam (hf : CoreT2EFam) : CoreT2E := by
  intro u Y M hYd hbased hy hMarg hM2 hs2 hdG v z hz1 hctx a t hva hpN
  obtain ⟨m, hdm⟩ := hdG
  have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
  have hG : argOK (graft M Y) := argOK_graft hMne hMarg Y
  have hGne : graft M Y ≠ [] :=
    List.length_pos_iff.mp (by
      rw [graft_length]
      have : 0 < Y.length := List.length_pos_iff.mpr hy
      omega)
  exact towerGraft2_lift_mem_fam hG hGne hz1 hva hdm hs2
    (hf u Y M hYd hbased hy hMarg hM2 hs2 ⟨m, hdm⟩ v z hz1 hctx hpN) hpN

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
    (hM2 : 1 ≤ M.length) (hz1 : z ≤ 1) (hctx : CtxOK M v z)
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
    (hM2 : 1 ≤ M.length) (hz1 : z ≤ 1) (hctx : CtxOK M v z)
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

/-! ## `GX` の閉包則（接頭辞・接ぎ木・塔）

The machine's set is closed under prefixes and under grafting.  The graft
closure is what makes a whole `tow`-tower ride on its own peel block: by
`graft_cons` the tower is *iterated grafting into the principal block*,
`tow v z R (k+1) = graft ((0,v,z) :: R) (tow v z R k)`, so
`(0, v, z) :: R.dropLast ∈ GX` already carries every tower element.  This
replaces the machine's unbounded self-reference (`∀ σ, W σ ⊆ GX`) — the towers
never need foreign `W`-elements, only their own peel. -/

theorem nil_mem_GX : ([] : TrioSeq) ∈ GX := by
  intro _ M _ hM2 v z _ hctx i _ a t hva
  rw [List.take_nil, graft_nil, List.dropLast_eq_take]
  exact hctx (M.length - 1) (by omega) a t hva

theorem nil_mem_GXs : ([] : TrioSeq) ∈ GXs := by
  refine ⟨nil_mem_GX, fun φ _ => ?_⟩
  have : slift ([] : TrioSeq) φ = [] := by simp [slift]
  rw [this]
  exact nil_mem_GX

/-- `GX` is prefix-closed: its obligations already range over all prefixes. -/
theorem gx_take {y : TrioSeq} (h : y ∈ GX) (j : ℕ) : y.take j ∈ GX := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [List.take_zero]
    exact nil_mem_GX
  · intro hb M hMarg hM2 v z hz1 hctx i hi a t hva
    have hby : based y := by
      unfold based at hb ⊢
      rwa [Wset.entry_take (X := y) (l := j) (i := 0) (j := 0) hj] at hb
    have hiy : i ≤ y.length :=
      le_trans hi (by rw [List.length_take]; omega)
    rw [List.take_take]
    exact h hby M hMarg hM2 v z hz1 hctx (min i j)
      (le_trans (Nat.min_le_left i j) hiy) a t hva

/-- **`GX` is closed under grafting**: the composite's prefix obligations split
into the head block's strict prefixes (supplied by `E.dropLast ∈ GX`) and the
argument's obligations over the equipped composite context `graft M E`
(`ctxOK_graft` + `graft_assoc`). -/
theorem gxs_take {y : TrioSeq} (h : y ∈ GXs) (j : ℕ) : y.take j ∈ GXs := by
  refine ⟨gx_take h.1 j, fun φ hφ => ?_⟩
  rcases Nat.le_total j y.length with hj | hj
  · rw [slift_take hj]
    exact gx_take (h.2 φ hφ) j
  · rw [List.take_of_length_le hj]
    exact h.2 φ hφ

theorem gx_graft {E w : TrioSeq} (hEne : E ≠ []) (hbE : based E)
    (hEd : E.dropLast ∈ GX) (hw : w ∈ GX) (hbw : based w) :
    graft E w ∈ GX := by
  intro _ M hMarg hM2 v z hz1 hctx i hi a t hva
  have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
  have hElen : 0 < E.length := List.length_pos_iff.mpr hEne
  rw [graft_length] at hi
  by_cases hlow : i ≤ E.length - 1
  · rw [take_graft_low hlow]
    have hres := hEd (based_dropLast hbE) M hMarg hM2 v z hz1 hctx i
      (by rw [List.length_dropLast]; omega) a t hva
    rwa [dropLast_take hlow] at hres
  · obtain ⟨j, rfl⟩ : ∃ j, i = E.length - 1 + j :=
      ⟨i - (E.length - 1), by omega⟩
    rw [take_graft_high, ← graft_assoc hEne]
    exact hw hbw (graft M E) (argOK_graft hMne hMarg E)
      (by rw [graft_length]; omega) v z hz1
      (ctxOK_graft hMarg hM2 hz1 hctx hEd hbE) j (by omega) a t hva

/-- **The tower rides on its peel block**: every element of the `tow` tower over
`R` is in `GX` as soon as the planted peel block is. -/
theorem tow_mem_GX {R : TrioSeq} {v z : ℕ} (hRne : R ≠ [])
    (hT : (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) ∈ GX) :
    ∀ k, Wset.tow v z R k ∈ GX := by
  intro k
  induction k with
  | zero => simpa [Wset.tow] using nil_mem_GX
  | succ k ih =>
      have heq : Wset.tow v z R (k + 1)
          = graft (((0, v, z) : ℕ × ℕ × ℕ) :: R) (Wset.tow v z R k) := by
        rw [graft_cons hRne]
        rfl
      rw [heq]
      refine gx_graft (by simp) (based_cons v z R) ?_ ih (Wset.based_tow v z R k)
      rwa [dropLast_cons hRne]

/-- **The lifted-plant core**: a planted principal block over an equipped
context, lifted, is again in the machine's set.  At `t = 0` this is
`gx_graft` applied to the context's own planted peel (`plantCtx_graft`); the
lift is the residual content. -/
def CoreLiftPlant : Prop :=
  ∀ (M D : TrioSeq), argOK M → 1 ≤ M.length → ∀ v z : ℕ, z ≤ 1 →
    CtxOK M v z → D ∈ GX → based D → ∀ t : ℕ,
      Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M D) t ∈ GX

/-! ### γ' の要素: ガードなしコピー塊も反復接ぎ木

`d1 = 0`（`srow ≤ 1`）のブロック済み展開では、コピー塊は行 0 シフトの
タイリングであり、`gcopies_succ_shift` はそのまま `graft` の再帰:
再基底化した窓に「ブロック列」を末尾として付けた `E` に対し
`copies (n+1) = graft E (copies n)`。よって `tow_mem_GX` と同じ帰納で、
コピー塊は**窓（末尾を除く）の `GX`-所属だけ**で `GX` に入る。 -/

theorem shiftl0_shiftr01_comm {c d : ℕ} {X : TrioSeq} (h : ∀ q ∈ X, c ≤ q.1) :
    shiftl0 c (shiftr01 d 0 X) = shiftr01 d 0 (shiftl0 c X) := by
  unfold shiftl0 shiftr01
  rw [List.map_map, List.map_map]
  refine List.map_congr_left ?_
  intro q hq
  have hc := h q hq
  simp only [Function.comp_apply]
  exact Prod.ext (by dsimp only; omega) rfl

theorem gcopies_depth_ge {R : TrioSeq} {p L d0 d1 n c : ℕ}
    (h : ∀ j, p ≤ j → j < p + L → c ≤ entry R 0 j) :
    ∀ q ∈ gcopies R p L d0 d1 n, c ≤ q.1 := by
  intro q hq
  unfold gcopies gcopy at hq
  rw [List.mem_flatMap] at hq
  obtain ⟨k, -, hq⟩ := hq
  rw [List.mem_map] at hq
  obtain ⟨j, hj, rfl⟩ := hq
  rw [List.mem_range'_1] at hj
  have := h j hj.1 hj.2
  dsimp only
  omega

/-- The re-based window with the blocked column re-attached: the block whose
graft recursion generates the copies. -/
noncomputable def cwin (R : TrioSeq) (p L d0 c : ℕ) : TrioSeq :=
  shiftl0 c (seg R p L) ++ [((d0, 0, 0) : ℕ × ℕ × ℕ)]

theorem cwin_dropLast {R : TrioSeq} {p L d0 c : ℕ} :
    (cwin R p L d0 c).dropLast = shiftl0 c (seg R p L) := by
  unfold cwin
  exact List.dropLast_concat

theorem cwin_last {R : TrioSeq} {p L d0 c : ℕ} :
    entry (cwin R p L d0 c) 0 ((cwin R p L d0 c).length - 1) = d0 := by
  have hlen : (shiftl0 c (seg R p L)).length = L := by
    rw [shiftl0_length, seg_length]
  have h : (cwin R p L d0 c).length - 1 = (shiftl0 c (seg R p L)).length + 0 := by
    unfold cwin
    rw [List.length_append, hlen]
    simp
  rw [h]
  unfold cwin
  rw [entry_append_right]
  rfl

/-- **The copies block is iterated grafting** (no row-1 ascension). -/
theorem shiftl0_gcopies_succ {R : TrioSeq} {p L d0 c n : ℕ}
    (h : ∀ j, p ≤ j → j < p + L → c ≤ entry R 0 j) :
    shiftl0 c (gcopies R p L d0 0 (n + 1))
      = graft (cwin R p L d0 c) (shiftl0 c (gcopies R p L d0 0 n)) := by
  rw [gcopies_succ_shift, shiftl0_append, gcopy_zero,
    shiftl0_shiftr01_comm (gcopies_depth_ge h)]
  unfold graft
  rw [cwin_dropLast, cwin_last]
  rfl

/-- **The copies block rides on the window**: if the re-based window (without
the blocked column) is in `GX`, so is every copies block over it. -/
theorem gcopies_mem_GX {R : TrioSeq} {p L d0 c : ℕ}
    (h : ∀ j, p ≤ j → j < p + L → c ≤ entry R 0 j)
    (hbase : entry R 0 p = c) (hL : 0 < L)
    (hW : shiftl0 c (seg R p L) ∈ GX) :
    ∀ n, shiftl0 c (gcopies R p L d0 0 n) ∈ GX := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have hb0 : (R.getD p ((0, 0, 0) : ℕ × ℕ × ℕ)).1 = c := hbase
  have hseg : shiftl0 c (seg R p (L' + 1))
      = ((entry R 0 p - c, entry R 1 p, entry R 2 p) : ℕ × ℕ × ℕ)
        :: shiftl0 c (seg R (p + 1) L') := by
    rw [seg_cons, shiftl0_cons]
  have hbW : based (shiftl0 c (seg R p (L' + 1))) := by
    rw [hseg]
    simp only [based, entry, List.getD_cons_zero, if_pos]
    omega
  have hbcw : based (cwin R p (L' + 1) d0 c) := by
    unfold cwin
    rw [hseg, List.cons_append]
    simp only [based, entry, List.getD_cons_zero, if_pos]
    omega
  have hbc : ∀ n, based (shiftl0 c (gcopies R p (L' + 1) d0 0 n)) := by
    intro n
    cases n with
    | zero => simp [gcopies]
    | succ n =>
        rw [shiftl0_gcopies_succ h]
        unfold graft
        rw [cwin_dropLast, hseg, List.cons_append]
        simp only [based, entry, List.getD_cons_zero, if_pos]
        omega
  intro n
  induction n with
  | zero =>
      simp only [gcopies, List.range_zero, List.flatMap_nil, shiftl0_nil]
      exact nil_mem_GX
  | succ n ih =>
      rw [shiftl0_gcopies_succ h]
      exact gx_graft (by unfold cwin; simp) hbcw
        (by rw [cwin_dropLast]; exact hW) ih (hbc n)

/-! ### 根を植える: 段の厳密降下

すべての残差核は `gx_graft` による分解で「文脈/要素の断片」に落ち、断片の
再帰の**底は単列ブロック `[(0,v,z)]`（植えた根）**である。その `Aop` は
節3 で、データ段は `2v+z-1` — 根のレベルより**厳密に低い**。つまり残差の
最終的な内容は「一段下の `W` が `GX` に入る」ことに集約される。 -/

/-- **Planting a root descends the stage**: the bare planted root's `Aop`
datum lives at stage `2v+z-1`, strictly below the root's own level. -/
theorem om_Aop {v z : ℕ} (h : ∀ w ∈ W (2 * v + z - 1), based w → w ∈ GX) :
    Aop W (2 * v + z) GX [((0, v, z) : ℕ × ℕ × ℕ)] := by
  rcases Nat.eq_zero_or_pos (2 * v + z) with h0 | hpos
  · exact Or.inl ⟨by simp, by simp [lev, entry]; omega⟩
  · refine Or.inr (Or.inr ⟨2 * v + z - 1, by omega, domT_Om hpos, ?_⟩)
    intro y hy hb
    rw [graft_Om]
    exact h y hy hb

/-- **The lift-closure core**: the machine's set is closed under the intrinsic
row-1 lift.  (The composite lift does *not* push through a graft as the
argument's own `Lift1` — `probe_liftplant` refutes that — so this is a genuine
residue, the purest form of the (e)-wall.) -/
def CoreLift : Prop :=
  ∀ y : TrioSeq, y ∈ GX → based y → ∀ t : ℕ, Lift1 y t ∈ GX

/-- **The planted-context core**: the ambient context's own peel, with a
planted root, is in the machine's set.  This is a pure *context*-side statement
(no element data) — the master length induction's job. -/
def CorePlantCtx : Prop :=
  ∀ M : TrioSeq, argOK M → 1 ≤ M.length → ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
    (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast) ∈ GX

/-- **The unlifted plant is free**: given the context's own planted peel
(`(0,v,z) :: M.dropLast ∈ GX`), grafting any `GX`-datum keeps the planted block
in `GX`. -/
theorem plantCtx_graft {M D : TrioSeq} {v z : ℕ} (hMne : M ≠ [])
    (hp : (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast) ∈ GX)
    (hD : D ∈ GX) (hbD : based D) :
    (((0, v, z) : ℕ × ℕ × ℕ) :: graft M D) ∈ GX := by
  rw [← graft_cons hMne]
  refine gx_graft (by simp) (based_cons v z M) ?_ hD hbD
  rwa [dropLast_cons hMne]

/-- **The lifted-plant core splits**: lift-closure plus the planted context. -/
theorem coreLiftPlant_of (hl : CoreLift) (hp : CorePlantCtx) : CoreLiftPlant := by
  intro M D hMarg hM2 v z hz1 hctx hD hbD t
  have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
  exact hl _ (plantCtx_graft hMne (hp M hMarg hM2 v z hz1 hctx) hD hbD)
    (based_cons v z _) t

/-! ### v0.118: 接ぎ木リフト計算則による α 残差の分割

`lift_graft_mask`（Cgraft.lean）で、リフトした植えブロックは

    Lift1 ((0,v,z) :: graft M D) t
      = (0, v+t, z) :: graft (ltail v z M t) (mlift D v t)      （SiteHigh のとき）

と分解する。右辺は「リフトした植え文脈」に「データの**環境マスクリフト**」を
接ぎ木した形なので、`plantCtx_graft` で 2 つの核に割れる。 -/

/-- **マスクリフト核**: 機械の集合は環境マスクリフトで閉じる。これが (e)-壁の
最終形。一般のデータでは複合ブロックの錐はデータ自身の錐ではなく `coneV` なので
（`cone_graft_mask`）、`CoreLift`（データ自身の `Lift1`）ではなくこちらが要る。 -/
def CoreMaskLift : Prop :=
  ∀ D : TrioSeq, D ∈ GX → based D → ∀ v t : ℕ, mlift D v t ∈ GX

/-- **リフトした植え文脈核**: 文脈自身の植えた peel をリフトしたものが機械の
集合に入る。データを含まない純粋な文脈側の言明（MASTER 長さ帰納の担当）。 -/
def CorePlantCtxLift : Prop :=
  ∀ M : TrioSeq, argOK M → 1 ≤ M.length → ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
    ∀ t : ℕ, Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast) t ∈ GX

open Classical in
/-- **α 残差の分割**: リフトした植えブロックは、リフトした植え文脈にデータの
マスクリフトを接ぎ木したもの。 -/
theorem liftPlant_of_plant {M D : TrioSeq} {v z t : ℕ}
    (hp : Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast) t ∈ GX)
    (hMarg : argOK M) (hM2 : 1 ≤ M.length)
    (hD : D ∈ GX) (hbD : based D) (hm : mlift D v t ∈ GX) :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M D) t ∈ GX := by
  classical
  have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
  have hElen : (((0, v, z) : ℕ × ℕ × ℕ) :: M).length = M.length + 1 := by simp
  have hE2 : 2 ≤ (((0, v, z) : ℕ × ℕ × ℕ) :: M).length := by rw [hElen]; omega
  have hE0 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: M) 0 0 = 0 := based_cons v z M
  have hEs : ∀ l, 0 < l → l < (((0, v, z) : ℕ × ℕ × ℕ) :: M).length →
      0 < entry (((0, v, z) : ℕ × ℕ × ℕ) :: M) 0 l := by
    intro l hl0 hlE
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    rw [entry_cons]
    exact hMarg _ (entry_pair_mem (by rw [hElen] at hlE; omega))
  have hE1 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: M) 1 0 = v := by
    show ((((0, v, z) : ℕ × ℕ × ℕ) :: M).getD 0 (0, 0, 0)).2.1 = v
    rfl
  set B : TrioSeq :=
    if SiteHigh (((0, v, z) : ℕ × ℕ × ℕ) :: M) then mlift D v t else D with hB
  have hbB : based B := by
    rw [hB]; split
    · show entry (mlift D v t) 0 0 = 0
      rw [entry0_mlift]; exact hbD
    · exact hbD
  have hBG : B ∈ GX := by
    rw [hB]; split
    · exact hm
    · exact hD
  have hcalc : Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M D) t
      = graft (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: M) t) B := by
    rw [← graft_cons hMne, lift_graft_mask hE0 hEs hE2 hbD t, hE1, hB]
  rw [hcalc, Wset.lift_cons, graft_cons (Wset.ltail_ne hMne)]
  refine plantCtx_graft (Wset.ltail_ne hMne) ?_ hBG hbB
  rw [Wset.ltail_dropLast]
  exact hp

theorem liftPlant_of_mask (hp : CorePlantCtxLift) {M D : TrioSeq} {v z t : ℕ}
    (hMarg : argOK M) (hM2 : 1 ≤ M.length) (hz1 : z ≤ 1) (hctx : CtxOK M v z)
    (hD : D ∈ GX) (hbD : based D) (hm : mlift D v t ∈ GX) :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M D) t ∈ GX :=
  liftPlant_of_plant (hp M hMarg hM2 v z hz1 hctx t) hMarg hM2 hD hbD hm

open Classical in
/-- **α 残差の分割**: リフトした植えブロックは、リフトした植え文脈にデータの
マスクリフトを接ぎ木したもの。 -/
theorem coreLiftPlant_of_mask (hp : CorePlantCtxLift) (hm : CoreMaskLift) :
    CoreLiftPlant := fun M D hMarg hM2 v z hz1 hctx hD hbD t =>
  liftPlant_of_mask hp hMarg hM2 hz1 hctx hD hbD (hm D hD hbD v t)

/-! ### ガード付きコピー塊（`d1 > 0`）も窓に乗る

`Croot.gcopies_succ_graft_lift` により、行 2 ブロッカーのコピー塊は
「窓への接ぎ木 + **根リフト**」の反復である。外側のリフトは (ML)
`mlift_Lift1_cons` でデータ側に吸収されるので、必要なのは**窓とその根リフト
全部が `GX` に入ること**だけ。 -/

theorem entry_gcopies_pos {B : TrioSeq} {L d0 d1 n i : ℕ} (hLb : 0 < L)
    (hup : ∀ l, 0 < l → l ≤ L → entry B 0 0 < entry B 0 l)
    (hbase : entry B 0 0 = 0) (hd0pos : 0 < d0)
    (hi0 : 0 < i) (hi : i < (gcopies B 0 L d0 d1 n).length) :
    0 < entry (gcopies B 0 L d0 d1 n) 0 i := by
  classical
  rw [gcopies_length] at hi
  obtain ⟨k, q, hk, hq, rfl⟩ := index_decomp hLb hi
  have hgc := gcopies_getD (M := B) (r := 0) (L := L) (d0 := d0) (d1 := d1)
    (k := k) (q := q) (n := n) hk hq
  have h0 : entry (gcopies B 0 L d0 d1 n) 0 (k * L + q)
      = entry B 0 (0 + q) + k * d0 := by
    show ((gcopies B 0 L d0 d1 n).getD (k * L + q) ((0, 0, 0) : ℕ × ℕ × ℕ)).1 = _
    rw [hgc]
  rw [h0]
  rcases Nat.eq_zero_or_pos q with rfl | hqpos
  · have hkpos : 0 < k := by
      by_contra hc
      have hk0 : k = 0 := by omega
      subst hk0
      simp at hi0
    have hkd : 0 < k * d0 := Nat.mul_pos hkpos hd0pos
    simp only [Nat.add_zero, Nat.zero_add]
    omega
  · have := hup q hqpos (by omega)
    simp only [Nat.zero_add]
    omega

theorem argOK_gcopies_tail {B : TrioSeq} {L d0 d1 n : ℕ} (hLb : 0 < L)
    (hup : ∀ l, 0 < l → l ≤ L → entry B 0 0 < entry B 0 l)
    (hbase : entry B 0 0 = 0) (hd0pos : 0 < d0) :
    argOK (gcopies B 0 L d0 d1 n).tail := by
  classical
  intro x hx
  cases hX : (gcopies B 0 L d0 d1 n) with
  | nil =>
      rw [hX] at hx
      simp at hx
  | cons a Xt =>
      rw [hX] at hx
      simp only [List.tail_cons] at hx
      obtain ⟨t, ht, rfl⟩ := mem_index hx
      have hpos := entry_gcopies_pos (B := B) (L := L) (d0 := d0) (d1 := d1)
        (n := n) (i := t + 1) hLb hup hbase hd0pos (by omega)
        (by rw [hX]; simp; omega)
      rw [hX] at hpos
      show 0 < (Xt.getD t ((0, 0, 0) : ℕ × ℕ × ℕ)).1
      have hshift : entry (a :: Xt) 0 (t + 1)
          = (Xt.getD t ((0, 0, 0) : ℕ × ℕ × ℕ)).1 := by
        unfold entry
        simp
      rwa [hshift] at hpos

/-- The copies block's root is the block's own root. -/
theorem gcopies_cons_root {B T : TrioSeq} {L d0 d1 n v z : ℕ} (hLb : 0 < L)
    (hn : 0 < n) (hBcons : B = ((0, v, z) : ℕ × ℕ × ℕ) :: T) :
    gcopies B 0 L d0 d1 n
      = ((0, v, z) : ℕ × ℕ × ℕ) :: (gcopies B 0 L d0 d1 n).tail := by
  classical
  have hXne : gcopies B 0 L d0 d1 n ≠ [] := by
    intro h
    have hl := congrArg List.length h
    rw [gcopies_length] at hl
    have : 0 < n * L := Nat.mul_pos hn hLb
    simp at hl
    omega
  have hgd : (gcopies B 0 L d0 d1 n).getD 0 ((0, 0, 0) : ℕ × ℕ × ℕ)
      = (entry B 0 0, entry B 1 0, entry B 2 0) := by
    have h := gcopies_getD (M := B) (r := 0) (L := L) (d0 := d0) (d1 := d1)
      (k := 0) (q := 0) (n := n) hn hLb
    simpa using h
  have he0 : entry B 0 0 = 0 := by rw [hBcons]; rfl
  have he1 : entry B 1 0 = v := by rw [hBcons]; rfl
  have he2 : entry B 2 0 = z := by rw [hBcons]; rfl
  rw [he0, he1, he2] at hgd
  cases hX : (gcopies B 0 L d0 d1 n) with
  | nil => exact absurd hX hXne
  | cons a Xt =>
      have ha : a = ((0, v, z) : ℕ × ℕ × ℕ) := by
        rw [hX] at hgd
        simpa using hgd
      rw [ha]
      simp

/-- **The guarded copies block rides on the lifted window**: with the row-1
ascension realised as a root lift (`gcopies_succ_graft_lift`), the copy-index
induction stays inside `GX` as soon as the window and all its root lifts are. -/
theorem gcopiesLift_mem_GX {B T : TrioSeq} {L d0 d1 v z : ℕ}
    (hBcons : B = ((0, v, z) : ℕ × ℕ × ℕ) :: T)
    (hTlen : T.length = L) (hLb : 0 < L) (hargT : argOK T)
    (hup : ∀ l, 0 < l → l ≤ L → entry B 0 0 < entry B 0 l)
    (hd0pos : 0 < d0) (hd0e : entry B 0 L = d0)
    (hd1pos : 0 < d1) (hlp : le1 B 0 L)
    (hw : ∀ s : ℕ, Lift1 B.dropLast s ∈ GX) :
    ∀ n s : ℕ, Lift1 (gcopies B 0 L d0 d1 n) s ∈ GX := by
  classical
  have hbase : entry B 0 0 = 0 := by rw [hBcons]; rfl
  have hlen : L + 1 = B.length := by rw [hBcons]; simp; omega
  have hTne : T ≠ [] := by
    intro h
    rw [h] at hTlen
    simp at hTlen
    omega
  have hdrop : B.dropLast = ((0, v, z) : ℕ × ℕ × ℕ) :: T.dropLast := by
    rw [hBcons, dropLast_cons hTne]
  have hgcons : ∀ Z : TrioSeq,
      graft B Z = ((0, v, z) : ℕ × ℕ × ℕ) :: graft T Z := by
    intro Z
    rw [hBcons]
    exact graft_cons hTne
  intro n
  induction n with
  | zero =>
      intro s
      simp only [gcopies, List.range_zero, List.flatMap_nil, Lift1_nil]
      exact nil_mem_GX
  | succ n ih =>
      intro s
      rw [gcopies_succ_graft_lift hlen hLb hup hd0pos hbase hd0e hd1pos hlp,
        hgcons]
      have hZG : Lift1 (gcopies B 0 L d0 d1 n) d1 ∈ GX := ih d1
      have hbZ : based (Lift1 (gcopies B 0 L d0 d1 n) d1) := by
        show entry (Lift1 (gcopies B 0 L d0 d1 n) d1) 0 0 = 0
        rw [entry0_Lift1]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [gcopies, entry]
        · rw [gcopies_cons_root hLb hn hBcons]
          rfl
      have hmask : mlift (Lift1 (gcopies B 0 L d0 d1 n) d1) v s ∈ GX := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · have hnil : gcopies B 0 L d0 d1 0 = [] := by simp [gcopies]
          rw [hnil, Lift1_nil]
          have : mlift ([] : TrioSeq) v s = [] := by simp [mlift]
          rw [this]
          exact nil_mem_GX
        · have hcons := gcopies_cons_root (B := B) (T := T) (d0 := d0)
            (d1 := d1) (n := n) hLb hn hBcons
          have hargXt : argOK (gcopies B 0 L d0 d1 n).tail :=
            argOK_gcopies_tail hLb hup hbase hd0pos
          rw [hcons, mlift_Lift1_cons hargXt hd1pos, ← hcons]
          exact ih (d1 + s)
      have hplant : Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: T.dropLast) s ∈ GX := by
        rw [← hdrop]
        exact hw s
      exact liftPlant_of_plant hplant hargT (by omega) hZG hbZ hmask

/-- **The γ'-residue, element form**: the descended copies block is in the
machine's set (independent of the ambient root `(v, z, t)`). -/
def CoreBlockedElt : Prop :=
  ∀ (u : ℕ) (Y M : TrioSeq) (p : ℕ),
    Y.dropLast ∈ GXs → based Y → Y ≠ [] →
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

/-- The composite's window is the context's suffix followed by the shifted
peel of the datum. -/
theorem seg_graft_eq {M Y : TrioSeq} {p : ℕ} (hy : Y ≠ []) (hM2 : 2 ≤ M.length)
    (hp : p < M.length - 1) :
    seg (graft M Y) p ((graft M Y).length - 1 - p)
      = seg M p (M.length - 1 - p)
        ++ shiftr01 (entry M 0 (M.length - 1)) 0 Y.dropLast := by
  classical
  have hylen : 0 < Y.length := List.length_pos_iff.mpr hy
  have hRlen : (graft M Y).length = M.length - 1 + Y.length := graft_length M Y
  have hsplit : (graft M Y).length - 1 - p
      = (M.length - 1 - p) + (Y.length - 1) := by rw [hRlen]; omega
  rw [hsplit, seg_append]
  refine congrArg₂ _ ?_ ?_
  · -- below the graft point the composite's entries are the context's
    unfold seg
    refine List.map_congr_left ?_
    intro j hj
    rw [List.mem_range'_1] at hj
    have hjlt : j < M.length - 1 := by omega
    have hent : ∀ i, entry (graft M Y) i j = entry M i j := by
      intro i
      rw [← Wset.entry_take (X := graft M Y) (l := M.length - 1) (i := i)
          (j := j) hjlt, take_graft_low le_rfl, Wset.entry_take hjlt]
    rw [hent 0, hent 1, hent 2]
  · -- at and above the graft point they are the shifted datum's
    have hidx : p + (M.length - 1 - p) = M.dropLast.length := by
      rw [List.length_dropLast]; omega
    rw [hidx, graft_eq_shift,
      seg_append_context _ _ (by rw [shiftr01_length]; omega),
      shiftr01_take, List.dropLast_eq_take]

theorem shiftl0_shiftr01_sub {c e : ℕ} (h : c ≤ e) (X : TrioSeq) :
    shiftl0 c (shiftr01 e 0 X) = shiftr01 (e - c) 0 X := by
  unfold shiftl0 shiftr01
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro q _
  simp only [Function.comp_apply]
  exact Prod.ext (by dsimp only; omega) rfl

theorem entry0_shiftl0 {c : ℕ} {L : TrioSeq} {j : ℕ} (hj : j < L.length) :
    entry (shiftl0 c L) 0 j = entry L 0 j - c := by
  unfold entry shiftl0
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj]
  simp

theorem entry0_seg {M : TrioSeq} {a l i : ℕ} (hi : i < l) :
    entry (seg M a l) 0 i = entry M 0 (a + i) := by
  unfold entry
  rw [seg_getD hi]
  simp [entry]

theorem shiftl0_seg_dropLast {M : TrioSeq} {p c : ℕ} (hp : p < M.length - 1) :
    (shiftl0 c (seg M p (M.length - p))).dropLast
      = shiftl0 c (seg M p (M.length - 1 - p)) := by
  rw [show M.length - p = (M.length - 1 - p) + 1 from by omega, seg_snoc]
  unfold shiftl0
  simp only [List.map_append, List.map_cons, List.map_nil]
  exact List.dropLast_concat

/-- **The re-based window is the context's re-based suffix grafted with the
datum's peel.** -/
theorem shiftl0_seg_graft {M Y : TrioSeq} {p : ℕ} (hy : Y ≠ [])
    (hM2 : 2 ≤ M.length) (hp : p < M.length - 1)
    (hle : entry M 0 p ≤ entry M 0 (M.length - 1)) :
    shiftl0 (entry M 0 p) (seg (graft M Y) p ((graft M Y).length - 1 - p))
      = graft (shiftl0 (entry M 0 p) (seg M p (M.length - p))) Y.dropLast := by
  classical
  set c : ℕ := entry M 0 p with hc
  have hseg : M.length - p = (M.length - 1 - p) + 1 := by omega
  have hdl := shiftl0_seg_dropLast (M := M) (p := p) (c := c) hp
  have hlen : (shiftl0 c (seg M p (M.length - p))).length = M.length - p := by
    rw [shiftl0_length, seg_length]
  have hlast : entry (shiftl0 c (seg M p (M.length - p))) 0 (M.length - p - 1)
      = entry M 0 (M.length - 1) - c := by
    rw [entry0_shiftl0 (by rw [seg_length]; omega), entry0_seg (by omega),
      show p + (M.length - p - 1) = M.length - 1 from by omega]
  rw [seg_graft_eq hy hM2 hp, shiftl0_append, shiftl0_shiftr01_sub hle,
    graft_eq_shift, hdl, hlen, hlast]

/-- **The composite's infix that crosses the graft point**, general length. -/
theorem seg_graft_cross {M E : TrioSeq} {p k j : ℕ} (hM2 : 2 ≤ M.length)
    (hp : p < M.length - 1) (hj : (M.length - 1 - p) + j = k + 1)
    (hjE : j ≤ E.length) :
    seg (graft M E) p (k + 1)
      = seg M p (M.length - 1 - p)
        ++ shiftr01 (entry M 0 (M.length - 1)) 0 (E.take j) := by
  classical
  rw [← hj, seg_append]
  refine congrArg₂ _ ?_ ?_
  · unfold seg
    refine List.map_congr_left ?_
    intro q hq
    rw [List.mem_range'_1] at hq
    rw [entry_graft_low (by omega), entry_graft_low (by omega),
      entry_graft_low (by omega)]
  · have hidx : p + (M.length - 1 - p) = M.dropLast.length := by
      rw [List.length_dropLast]; omega
    rw [hidx, graft_eq_shift,
      seg_append_context _ _ (by rw [shiftr01_length]; omega), shiftr01_take]

/-- **The re-based crossing infix is a graft of the datum's prefix.** -/
theorem shiftl0_seg_graft_cross {M E : TrioSeq} {p k j : ℕ} (hM2 : 2 ≤ M.length)
    (hp : p < M.length - 1) (hj : (M.length - 1 - p) + j = k + 1)
    (hjE : j ≤ E.length)
    (hle : entry M 0 p ≤ entry M 0 (M.length - 1)) :
    shiftl0 (entry M 0 p) (seg (graft M E) p (k + 1))
      = graft (shiftl0 (entry M 0 p) (seg M p (M.length - p))) (E.take j) := by
  classical
  set c : ℕ := entry M 0 p with hc
  have hdl := shiftl0_seg_dropLast (M := M) (p := p) (c := c) hp
  have hlen : (shiftl0 c (seg M p (M.length - p))).length = M.length - p := by
    rw [shiftl0_length, seg_length]
  have hlast : entry (shiftl0 c (seg M p (M.length - p))) 0 (M.length - p - 1)
      = entry M 0 (M.length - 1) - c := by
    rw [entry0_shiftl0 (by rw [seg_length]; omega), entry0_seg (by omega),
      show p + (M.length - p - 1) = M.length - 1 from by omega]
  rw [seg_graft_cross hM2 hp hj hjE, shiftl0_append, shiftl0_shiftr01_sub hle,
    graft_eq_shift, hdl, hlen, hlast]

/-- **The γ'-window core**: the re-based window of the composite — the columns
from the blocker `p` up to (but excluding) the blocked trailing column — is in
the machine's set.  This is a *context piece* statement: the window is
`graft (M's re-based suffix from p) (Y.dropLast)`. -/
def CoreWindow : Prop :=
  ∀ (u : ℕ) (Y M : TrioSeq) (p : ℕ),
    Y.dropLast ∈ GXs → based Y → Y ≠ [] →
    argOK M → 2 ≤ M.length →
    ¬ hasParent Y (srow Y (Y.length - 1)) (Y.length - 1) →
    hasParent (graft M Y) (srow (graft M Y) ((graft M Y).length - 1))
      ((graft M Y).length - 1) →
    parent (graft M Y) (srow (graft M Y) ((graft M Y).length - 1))
      ((graft M Y).length - 1) = p →
    p < M.length - 1 →
    ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
      shiftl0 (entry M 0 p)
        (seg (graft M Y) p ((graft M Y).length - 1 - p)) ∈ GX

/-- **The context-suffix core**: the context's own re-based suffix (from the
blocker `p`, minus its trailing column) is in the machine's set — a statement
about the *context alone*. -/
def CoreCtxSuffix : Prop :=
  ∀ (M : TrioSeq) (p : ℕ), argOK M → 2 ≤ M.length → p < M.length - 1 →
    ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
      shiftl0 (entry M 0 p) (seg M p (M.length - 1 - p)) ∈ GX

theorem le0_of_le1 {X : TrioSeq} {a b : ℕ} (h : le1 X a b) : le0 X a b := by
  obtain ⟨ha, hb, hch⟩ := h
  refine ⟨ha, hb, ?_⟩
  induction hch with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y w hay hyw ih => exact (ih hyw.1).trans hyw.2.2.2.2.1.2.2

/-- **The window core reduces to the context-suffix core**: the window is the
context's suffix grafted with the datum's peel (`shiftl0_seg_graft`), so
`gx_graft` splits it. -/
theorem coreWindow_of_suffix (hs : CoreCtxSuffix) : CoreWindow := by
  classical
  intro u Y M p hYdG hbased hy hMarg hM2 hpY hpG hpar hplt v z hz1 hctx
  have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
  have hylen : 0 < Y.length := List.length_pos_iff.mpr hy
  set R : TrioSeq := graft M Y with hRdef
  have hRlen : R.length = M.length - 1 + Y.length := by rw [hRdef, graft_length]
  have hYd : Y.dropLast ∈ GX := hYdG.1
  -- the blocker sits strictly above the graft point
  have hchain : Relation.ReflTransGen (nextrel0 R) p (R.length - 1) := by
    have hnr := parent_nextR hpG
    rw [hpar] at hnr
    unfold nextR at hnr
    by_cases h0 : srow R (R.length - 1) = 0
    · rw [h0, if_pos rfl] at hnr
      exact Relation.ReflTransGen.single hnr
    · by_cases h1 : srow R (R.length - 1) = 1
      · rw [h1, if_neg one_ne_zero, if_pos rfl] at hnr
        exact hnr.2.2.2.2.1.2.2
      · rw [if_neg h0, if_neg h1] at hnr
        exact (le0_of_le1 hnr.2.2.2.2.1).2.2
  have hwin := window_of_rtg0 hchain (by omega)
  have hlowp : entry R 0 p = entry M 0 p := by
    rw [← Wset.entry_take (X := R) (l := p + 1) (i := 0) (j := p) (by omega),
      hRdef, take_graft_low (by omega), Wset.entry_take (by omega)]
  have hgp : entry R 0 (M.length - 1) = entry M 0 (M.length - 1) := by
    have hidx : M.length - 1 = M.dropLast.length + 0 := by
      rw [List.length_dropLast]; omega
    rw [hRdef, graft_eq_shift, hidx, entry_append_right]
    cases Y with
    | nil => exact absurd rfl hy
    | cons a l =>
        have hb : a.1 = 0 := hbased
        unfold shiftr01 entry
        simp [hb]
  have hle : entry M 0 p ≤ entry M 0 (M.length - 1) := by
    have := hwin (M.length - 1) (by omega) (by omega)
    omega
  rw [hRdef, shiftl0_seg_graft hy hM2 hplt hle]
  refine gx_graft ?_ ?_ ?_ hYd (based_dropLast hbased)
  · intro hnil
    have := congrArg List.length hnil
    rw [shiftl0_length, seg_length] at this
    simp at this
    omega
  · unfold based
    rw [entry0_shiftl0 (by rw [seg_length]; omega), entry0_seg (by omega)]
    simp
  · rw [shiftl0_seg_dropLast hplt]
    exact hs M p hMarg hM2 hplt v z hz1 hctx

/-- **The γ'-residue at a row-2 blocker**: there the copies ascend in row 1
(`d1 > 0`), so the graft recursion carries a lift. -/
def CoreBlockedEltHi : Prop :=
  ∀ (u : ℕ) (Y M : TrioSeq) (p : ℕ),
    Y.dropLast ∈ GXs → based Y → Y ≠ [] →
    argOK M → 2 ≤ M.length →
    ¬ hasParent Y (srow Y (Y.length - 1)) (Y.length - 1) →
    hasParent (graft M Y) (srow (graft M Y) ((graft M Y).length - 1))
      ((graft M Y).length - 1) →
    parent (graft M Y) (srow (graft M Y) ((graft M Y).length - 1))
      ((graft M Y).length - 1) = p →
    p < M.length - 1 →
    srow (graft M Y) ((graft M Y).length - 1) = 2 →
    ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
    ∀ n : ℕ, 1 ≤ n →
      shiftl0 (entry M 0 p)
        (gcopies (graft M Y) p ((graft M Y).length - 1 - p)
          (entry (graft M Y) 0 ((graft M Y).length - 1)
            - entry (graft M Y) 0 p)
          (entry (graft M Y) 1 ((graft M Y).length - 1)
            - entry (graft M Y) 1 p) n) ∈ GX

/-- **γ' element from the window**: at a row-0/row-1 blocker the copies carry
no row-1 ascension, so the copies block is iterated grafting over the window
(`shiftl0_gcopies_succ`) and rides on the window's own membership. -/
theorem coreBlockedElt_of_window (hw : CoreWindow) (hhi : CoreBlockedEltHi) :
    CoreBlockedElt := by
  classical
  intro u Y M p AY hbased hy hMarg hM2 hpY hpG hpar hplt v z hz1 hctx n hn
  have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
  have hylen : 0 < Y.length := List.length_pos_iff.mpr hy
  set R : TrioSeq := graft M Y with hRdef
  have hRlen : R.length = M.length - 1 + Y.length := by rw [hRdef, graft_length]
  have hlow : entry R 0 p = entry M 0 p := by
    rw [← Wset.entry_take (X := R) (l := p + 1) (i := 0) (j := p) (by omega),
      hRdef, take_graft_low (by omega), Wset.entry_take (by omega)]
  by_cases hs2 : srow R (R.length - 1) = 2
  · rw [hs2, if_pos (by omega : (0:ℕ) < 2), if_pos (by omega : (1:ℕ) < 2)]
    exact hhi u Y M p AY hbased hy hMarg hM2 hpY hpG hpar hplt hs2 v z hz1 hctx
      n hn
  · -- row-0 / row-1 blocker: no ascension
    have hs1 : srow R (R.length - 1) ≤ 1 := by
      have := srow_le2 (M := R) (j := R.length - 1)
      omega
    -- the row-0 depths strictly increase away from the blocker
    have hchain : Relation.ReflTransGen (nextrel0 R) p (R.length - 1) := by
      have hnr := parent_nextR hpG
      rw [hpar] at hnr
      by_cases h0 : srow R (R.length - 1) = 0
      · rw [h0] at hnr
        unfold nextR at hnr
        rw [if_pos rfl] at hnr
        exact Relation.ReflTransGen.single hnr
      · have h1 : srow R (R.length - 1) = 1 := by omega
        rw [h1] at hnr
        unfold nextR at hnr
        rw [if_neg one_ne_zero, if_pos rfl] at hnr
        exact hnr.2.2.2.2.1.2.2
    have hwin := window_of_rtg0 hchain (by omega)
    have hdep : ∀ j, p ≤ j → j < p + (R.length - 1 - p) →
        entry M 0 p ≤ entry R 0 j := by
      intro j hj1 hj2
      rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt
      · rw [hlow]
      · have := hwin j hlt (by omega)
        omega
    have hbaseR : entry R 0 p = entry M 0 p := hlow
    have hL : 0 < R.length - 1 - p := by omega
    by_cases h0d : srow R (R.length - 1) = 0
    · rw [h0d, if_neg (by omega : ¬ (0:ℕ) < 0), if_neg (by omega : ¬ (1:ℕ) < 0)]
      exact gcopies_mem_GX hdep hbaseR hL
        (hw u Y M p AY hbased hy hMarg hM2 hpY hpG hpar hplt v z hz1 hctx) n
    · have h1d : srow R (R.length - 1) = 1 := by omega
      rw [h1d, if_pos (by omega : (0:ℕ) < 1), if_neg (by omega : ¬ (1:ℕ) < 1)]
      exact gcopies_mem_GX hdep hbaseR hL
        (hw u Y M p AY hbased hy hMarg hM2 hpY hpG hpar hplt v z hz1 hctx) n

/-- **The lifted γ'-window core**: the composite's re-based window AND all its
root lifts are in the machine's set.  At `s = 0` this is `CoreWindow`; the
lifts are what the row-2 blocker's ascending copies consume. -/
def CoreWindowLift : Prop :=
  ∀ (u : ℕ) (Y M : TrioSeq) (p : ℕ),
    Y.dropLast ∈ GXs → based Y → Y ≠ [] →
    argOK M → 2 ≤ M.length →
    ¬ hasParent Y (srow Y (Y.length - 1)) (Y.length - 1) →
    hasParent (graft M Y) (srow (graft M Y) ((graft M Y).length - 1))
      ((graft M Y).length - 1) →
    parent (graft M Y) (srow (graft M Y) ((graft M Y).length - 1))
      ((graft M Y).length - 1) = p →
    p < M.length - 1 →
    ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
    ∀ s : ℕ,
      Lift1 (shiftl0 (entry M 0 p)
        (seg (graft M Y) p ((graft M Y).length - 1 - p))) s ∈ GX

/-- **The lifted context-suffix core**: the context's own re-based suffix (from
the blocker `p`, minus its trailing column) AND all its root lifts are in the
machine's set — a statement about the *context alone*. -/
def CoreCtxSuffixLift : Prop :=
  ∀ (M : TrioSeq) (p : ℕ), argOK M → 2 ≤ M.length → p < M.length - 1 →
    (∀ j, p < j → j ≤ M.length - 1 → entry M 0 p < entry M 0 j) →
    ∀ v z : ℕ, z ≤ 1 → CtxOK M v z → ∀ s : ℕ,
      Lift1 (shiftl0 (entry M 0 p) (seg M p (M.length - 1 - p))) s ∈ GX

open Classical in
/-- **The lifted window core reduces to the lifted context suffix**: the window
is the context's re-based suffix grafted with the datum's peel
(`shiftl0_seg_graft`), and the suffix is itself a planted block, so
`liftPlant_of_plant` splits the lift into the suffix's own root lift and the
datum's ambient mask (`gxs_mlift`). -/
theorem coreWindowLift_of_ctxSuffixLift (hs : CoreCtxSuffixLift) :
    CoreWindowLift := by
  classical
  intro u Y M p hYdG hbased hy hMarg hM2 hpY hpG hpar hplt v z hz1 hctx s
  have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
  have hylen : 0 < Y.length := List.length_pos_iff.mpr hy
  set R : TrioSeq := graft M Y with hRdef
  have hRlen : R.length = M.length - 1 + Y.length := by rw [hRdef, graft_length]
  have hchain : Relation.ReflTransGen (nextrel0 R) p (R.length - 1) := by
    have hnr := parent_nextR hpG
    rw [hpar] at hnr
    unfold nextR at hnr
    by_cases h0 : srow R (R.length - 1) = 0
    · rw [h0, if_pos rfl] at hnr
      exact Relation.ReflTransGen.single hnr
    · by_cases h1 : srow R (R.length - 1) = 1
      · rw [h1, if_neg one_ne_zero, if_pos rfl] at hnr
        exact hnr.2.2.2.2.1.2.2
      · rw [if_neg h0, if_neg h1] at hnr
        exact (le0_of_le1 hnr.2.2.2.2.1).2.2
  have hwin := window_of_rtg0 hchain (by omega)
  have hlowp : entry R 0 p = entry M 0 p := by
    rw [← Wset.entry_take (X := R) (l := p + 1) (i := 0) (j := p) (by omega),
      hRdef, take_graft_low (by omega), Wset.entry_take (by omega)]
  have hgp : entry R 0 (M.length - 1) = entry M 0 (M.length - 1) := by
    have hidx : M.length - 1 = M.dropLast.length + 0 := by
      rw [List.length_dropLast]; omega
    rw [hRdef, graft_eq_shift, hidx, entry_append_right]
    cases Y with
    | nil => exact absurd rfl hy
    | cons a l =>
        have hb : a.1 = 0 := hbased
        unfold shiftr01 entry
        simp [hb]
  have hle : entry M 0 p ≤ entry M 0 (M.length - 1) := by
    have := hwin (M.length - 1) (by omega) (by omega)
    omega
  set c : ℕ := entry M 0 p with hc
  -- the M-side of the window is strictly deeper than the blocker
  have hMstrict : ∀ j, p < j → j ≤ M.length - 1 → c < entry M 0 j := by
    intro j hj0 hj1
    rcases Nat.lt_or_ge j (M.length - 1) with hjlt | hjge
    · have hent : entry R 0 j = entry M 0 j := by
        rw [← Wset.entry_take (X := R) (l := M.length - 1) (i := 0) (j := j)
          (by omega), hRdef, take_graft_low le_rfl, Wset.entry_take (by omega)]
      have := hwin j hj0 (by omega)
      omega
    · have hjeq : j = M.length - 1 := by omega
      subst hjeq
      have := hwin (M.length - 1) hj0 (by omega)
      omega
  -- the re-based suffix as a planted block
  have hsegc : seg M p (M.length - p)
      = ((entry M 0 p, entry M 1 p, entry M 2 p) : ℕ × ℕ × ℕ)
        :: seg M (p + 1) (M.length - p - 1) := by
    rw [show M.length - p = (M.length - p - 1) + 1 from by omega, seg_cons,
      Nat.add_sub_cancel]
  set T : TrioSeq := shiftl0 c (seg M (p + 1) (M.length - p - 1)) with hT
  have hTlen : T.length = M.length - p - 1 := by
    rw [hT, shiftl0_length, seg_length]
  have hTne : T ≠ [] := by
    intro h
    rw [h] at hTlen
    simp at hTlen
    omega
  have hEcons : shiftl0 c (seg M p (M.length - p))
      = ((0, entry M 1 p, entry M 2 p) : ℕ × ℕ × ℕ) :: T := by
    rw [hsegc, shiftl0_cons, hT, show entry M 0 p - c = 0 from by omega]
  have hargT : argOK T := by
    intro x hx
    rw [hT, mem_shiftl0] at hx
    obtain ⟨y, hy', rfl⟩ := hx
    unfold seg at hy'
    rw [List.mem_map] at hy'
    obtain ⟨j, hj, rfl⟩ := hy'
    rw [List.mem_range'_1] at hj
    have := hMstrict j (by omega) (by omega)
    dsimp only
    omega
  have hplant : Lift1 (((0, entry M 1 p, entry M 2 p) : ℕ × ℕ × ℕ)
      :: T.dropLast) s ∈ GX := by
    have hEd : (shiftl0 c (seg M p (M.length - p))).dropLast
        = shiftl0 c (seg M p (M.length - 1 - p)) := shiftl0_seg_dropLast hplt
    rw [hEcons, dropLast_cons hTne] at hEd
    rw [hEd]
    exact hs M p hMarg hM2 hplt hMstrict v z hz1 hctx s
  rw [hRdef, shiftl0_seg_graft hy hM2 hplt hle, hEcons, graft_cons hTne]
  exact liftPlant_of_plant hplant hargT (by omega) hYdG.1
    (based_dropLast hbased) (gxs_mlift hYdG (entry M 1 p) s)

/-! ### 文脈成分 `CtxInf`（中間ブロックの装備、階段閉包）

`InfEquip` を装備側から供給するための文脈成分。素朴な「中間ブロックの根
リフト」版はリフト文脈で偽（tools/probe_infltail.py）なので、`GXs` と同じく
**階段閉包**にしておく（`Croot.seg_slift` / `Croot.seg_mlift`）。 -/

/-- **Infix equipment, staircase-closed.**  Every re-based window-infix of the
context that avoids the trailing column — and every staircase lift of it — is a
planted `W`-package. -/
def CtxInf (M : TrioSeq) : Prop :=
  ∀ p k, p + k < M.length - 1 →
    (∀ q, q < k + 1 → Relation.ReflTransGen (nextrel0 M) p (p + q)) →
    entry M 2 p ≤ 1 ∧
    ∀ φ : ℕ → ℕ, Stair φ → ∀ a t : ℕ,
      2 * (φ (entry M 1 p) + t) + entry M 2 p ≤ a →
      Lift1 (slift (shiftl0 (entry M 0 p) (seg M p (k + 1))) φ) t ∈ W a

theorem ctxInf_take {M : TrioSeq} (h : CtxInf M) (j : ℕ) : CtxInf (M.take j) := by
  intro p k hk hwin
  have hjM : p + k < M.length - 1 := by
    rw [List.length_take] at hk
    omega
  have hlt : p + k < j := by rw [List.length_take] at hk; omega
  have hwin' : ∀ q, q < k + 1 → Relation.ReflTransGen (nextrel0 M) p (p + q) := by
    intro q hq
    have hb : le0 (M.take j) p (p + q) :=
      ⟨by rw [List.length_take]; omega, by rw [List.length_take]; omega,
        hwin q hq⟩
    rcases Nat.le_total j M.length with hj | hj
    · exact ((le0_take (X := M) (l := j) (a := p) (b := p + q) hj
        (by omega)).mp hb).2.2
    · rw [List.take_of_length_le hj] at hb
      exact hb.2.2
  have hent : ∀ i, entry (M.take j) i p = entry M i p :=
    fun i => Wset.entry_take (by omega)
  have hseg : seg (M.take j) p (k + 1) = seg M p (k + 1) := by
    unfold seg
    refine List.map_congr_left ?_
    intro q hq
    rw [List.mem_range'_1] at hq
    rw [Wset.entry_take (X := M) (l := j) (i := 0) (j := q) (by omega),
      Wset.entry_take (X := M) (l := j) (i := 1) (j := q) (by omega),
      Wset.entry_take (X := M) (l := j) (i := 2) (j := q) (by omega)]
  obtain ⟨h2, hpk⟩ := h p k hjM hwin'
  rw [hent 0, hent 1, hent 2, hseg]
  exact ⟨h2, hpk⟩

open Classical in
/-- **The lifted context keeps the infix equipment** — this is where the naive
"infix root lift" form fails and the staircase closure is needed
(`Croot.seg_mlift`): the ambient mask restricts to the infix as the infix's own
ambient mask, which is a staircase lift. -/
theorem ctxInf_ltail {M : TrioSeq} (hMarg : argOK M) (h : CtxInf M) (v z t : ℕ) :
    CtxInf (Wset.ltail v z M t) := by
  classical
  have hml : Wset.ltail v z M t = mlift M v t := ltail_eq_mlift hMarg
  intro p k hk hwin
  rw [hml] at hk hwin ⊢
  rw [mlift_length] at hk
  have hwin' : ∀ q, q < k + 1 → Relation.ReflTransGen (nextrel0 M) p (p + q) := by
    intro q hq
    exact (rtg0_slift (A := M)).mp (by
      rw [← mlift_eq_slift]; exact hwin q hq)
  obtain ⟨h2, hpk⟩ := h p k hk hwin'
  have hplen : p < M.length := by omega
  have he0 : entry (mlift M v t) 0 p = entry M 0 p := entry0_mlift M v t p
  have he2 : entry (mlift M v t) 2 p = entry M 2 p := entry2_mlift M v t p
  have he1 : entry (mlift M v t) 1 p
      = entry M 1 p + (if coneV M v p then t else 0) := entry1_mlift hplen
  have hlen' : p + (k + 1) ≤ M.length := by omega
  have hseg := seg_mlift (R := M) (p := p) (k := k) (v := v) (t := t)
    hlen' hwin'
  refine ⟨by rw [he2]; exact h2, ?_⟩
  intro φ hφ a t' hva
  rw [he1, he2] at hva
  rw [he0, hseg]
  by_cases hc : coneV M v p
  · rw [if_pos hc] at hva ⊢
    set ψ : ℕ → ℕ := fun m => m + (if v < m then t else 0) with hψ
    have hψs : Stair ψ := stair_step v t
    have hc1 : v < entry M 1 p := by
      have h1 := coneV_iff_amin.mp hc
      have h2 := amin_self_le M p
      omega
    have hψr : ψ (entry M 1 p) = entry M 1 p + t := by
      rw [hψ]; simp only []; rw [if_pos hc1]
    have hcmp : Stair (fun m => φ (ψ m)) := stair_comp hψs hφ
    have hmk : ∀ x ∈ seg M p (k + 1), entry M 0 p ≤ x.1 := by
      intro x hx
      unfold seg at hx
      rw [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      rw [List.mem_range'_1] at hq
      rcases Nat.eq_or_lt_of_le hq.1 with heq | hlt
      · rw [← heq]
      · have := rtg0_entry0_lt (hwin' (q - p) (by omega))
          (by omega : p ≠ p + (q - p))
        rw [show p + (q - p) = q from by omega] at this
        dsimp only
        omega
    rw [shiftl0_mlift hmk, mlift_eq_slift, slift_slift hψs hφ]
    refine hpk (fun m => φ (ψ m)) hcmp a t' ?_
    show 2 * (φ (ψ (entry M 1 p)) + t') + entry M 2 p ≤ a
    rw [hψr]
    exact hva
  · rw [if_neg hc] at hva ⊢
    exact hpk φ hφ a t' hva

theorem stair_id : Stair (fun m => m) :=
  ⟨fun _ => le_rfl, fun _ _ _ => by omega, rfl⟩

theorem slift_id (A : TrioSeq) : slift A (fun m => m) = A := by
  refine list_ext_getD ?_ ?_
  · rw [slift_length]
  · intro i hi
    rw [slift_length] at hi
    rw [slift_getD hi, getD_eq_entries]
    simp

theorem seg_take {M : TrioSeq} {a l k : ℕ} (hk : k ≤ l) :
    (seg M a l).take k = seg M a k := by
  refine list_ext_getD ?_ ?_
  · rw [List.length_take, seg_length, seg_length]
    omega
  · intro i hi
    rw [List.length_take, seg_length] at hi
    rw [getD_take (by omega), seg_getD (by omega), seg_getD (by omega)]

/-- **`CtxInf` discharges `InfEquip` pointwise**: the infix equipment is exactly
the `φ = id` slice of the staircase-closed context component. -/
theorem infEquip_at_of_ctxInf {M : TrioSeq} (h : CtxInf M) {p : ℕ}
    (hM2 : 2 ≤ M.length) (hplt : p < M.length - 1)
    (hwin : ∀ j, p < j → j ≤ M.length - 1 → entry M 0 p < entry M 0 j) :
    entry M 2 p ≤ 1 ∧
    CtxOK (shiftl0 (entry M 0 p) (seg M (p + 1) (M.length - 1 - p)))
      (entry M 1 p) (entry M 2 p) := by
  classical
  set c : ℕ := entry M 0 p with hc
  set L : ℕ := M.length - 1 - p with hL
  have hchain : ∀ p' q, p' = p → q < L → Relation.ReflTransGen (nextrel0 M) p (p + q) := by
    intro _ q _ hq
    refine rtg0_of_window (by omega) (by omega) ?_
    intro l hl0 hl1
    exact hwin l hl0 (by omega)
  have hwin0 : ∀ k, k < L → ∀ q, q < k + 1 →
      Relation.ReflTransGen (nextrel0 M) p (p + q) := by
    intro k hk q hq
    exact hchain p q rfl (by omega)
  refine ⟨(h p 0 (by omega) (hwin0 0 (by omega))).1, ?_⟩
  intro k hk a t hva
  rw [shiftl0_length, seg_length] at hk
  have hcons : ((0, entry M 1 p, entry M 2 p) : ℕ × ℕ × ℕ)
      :: (shiftl0 c (seg M (p + 1) L)).take k
      = shiftl0 c (seg M p (k + 1)) := by
    have htk : (shiftl0 c (seg M (p + 1) L)).take k
        = shiftl0 c (seg M (p + 1) k) := by
      unfold shiftl0
      rw [← List.map_take, seg_take (by omega)]
    rw [htk, seg_cons, shiftl0_cons]
    congr 1
    exact Prod.ext (by dsimp only; omega) rfl
  rw [hcons]
  have hres := (h p k (by omega) (hwin0 k hk)).2 (fun m => m) stair_id a t
    (by simpa using hva)
  rwa [slift_id] at hres

open Classical in
/-- **`CtxInf` for a composite context, away from the graft point.**  The infix
either lies inside the head block `M` (`seg_graft_low`) or inside the datum `E`
(`shiftl0_seg_graft_high`); the crossing case is isolated as `hcross`, and by
`Croot.shiftl0_seg_graft` + `slift_graft` it is a `GX` obligation for a
STAIRCASE LIFT of `E`'s prefix at the re-based `M`-suffix context. -/
theorem ctxInf_graft_of_cross {M E : TrioSeq} (hMne : M ≠ []) (hEne : E ≠ [])
    (hM : CtxInf M) (hE : CtxInf E)
    (hcross : ∀ p k, p < M.length - 1 → M.length - 1 ≤ p + k →
      p + k < (graft M E).length - 1 →
      (∀ q, q < k + 1 →
        Relation.ReflTransGen (nextrel0 (graft M E)) p (p + q)) →
      entry (graft M E) 2 p ≤ 1 ∧
      ∀ φ : ℕ → ℕ, Stair φ → ∀ a t : ℕ,
        2 * (φ (entry (graft M E) 1 p) + t) + entry (graft M E) 2 p ≤ a →
        Lift1 (slift (shiftl0 (entry (graft M E) 0 p)
          (seg (graft M E) p (k + 1))) φ) t ∈ W a) :
    CtxInf (graft M E) := by
  classical
  have hMlen : 0 < M.length := List.length_pos_iff.mpr hMne
  have hElen : 0 < E.length := List.length_pos_iff.mpr hEne
  have hGlen : (graft M E).length = M.length - 1 + E.length := graft_length M E
  intro p k hk hwin
  rw [hGlen] at hk
  rcases Nat.lt_or_ge (p + k) (M.length - 1) with hlow | hge
  · -- the infix lies inside the head block
    have hwin' : ∀ q, q < k + 1 → Relation.ReflTransGen (nextrel0 M) p (p + q) := by
      intro q hq
      have hb : le0 (graft M E) p (p + q) :=
        ⟨by rw [hGlen]; omega, by rw [hGlen]; omega, hwin q hq⟩
      have h1 : le0 ((graft M E).take (M.length - 1)) p (p + q) :=
        (le0_take (X := graft M E) (l := M.length - 1)
          (by rw [hGlen]; omega) (by omega)).mpr hb
      rw [take_graft_low le_rfl] at h1
      exact ((le0_take (X := M) (l := M.length - 1) (by omega)
        (by omega)).mp h1).2.2
    obtain ⟨h2, hpk⟩ := hM p k (by omega) hwin'
    rw [entry_graft_low (by omega), entry_graft_low (by omega),
      entry_graft_low (by omega), seg_graft_low (by omega)]
    exact ⟨h2, hpk⟩
  · rcases Nat.lt_or_ge p (M.length - 1) with hcr | hhi
    · -- the infix crosses the graft point
      exact hcross p k hcr hge (by rw [hGlen]; omega) hwin
    · -- the infix lies inside the datum
      obtain ⟨j0, rfl⟩ : ∃ j0, p = M.length - 1 + j0 := ⟨p - (M.length - 1), by omega⟩
      have hj0k : j0 + k < E.length - 1 := by omega
      have hwin' : ∀ q, q < k + 1 → Relation.ReflTransGen (nextrel0 E) j0 (j0 + q) := by
        intro q hq
        have hb : le0 (graft M E) (M.length - 1 + j0)
            (M.length - 1 + (j0 + q)) := by
          refine ⟨by rw [hGlen]; omega, by rw [hGlen]; omega, ?_⟩
          rw [show M.length - 1 + (j0 + q) = M.length - 1 + j0 + q from by omega]
          exact hwin q hq
        exact ((le0_graft_high M E j0 (j0 + q)).mp hb).2.2
      obtain ⟨h2, hpk⟩ := hE j0 k hj0k hwin'
      rw [entry1_graft_high, entry2_graft_high,
        shiftl0_seg_graft_high (by omega)]
      exact ⟨h2, hpk⟩

/-! ### 中間ブロックの装備（`W` レベル）だけで接尾核は植え核に落ちる

`CoreCtxSuffixLift` の対象は、再基底化した中間ブロックを**自身の根で植えた
ブロック**そのもの。したがって `CorePlantCtxLift` を文脈
`M' = shiftl0 c (seg M (p+1) (|M|-1-p))` ／根 `(entry M 1 p, entry M 2 p)` に
適用すればよい。要るのは `M'` の**装備**（純粋に `∈ W a` の言明で、`GX` を
含まない）と `entry M 2 p ≤ 1` だけ。 -/

/-- **Infix equipment**: the ambient context's re-based infix, planted at its
own root, is itself equipped — a pure `W`-level statement about the context
(no `GX`), exactly the kind the `Wstar2s` induction supplies for prefixes. -/
def InfEquip : Prop :=
  ∀ (M : TrioSeq) (p : ℕ), argOK M → 2 ≤ M.length → p < M.length - 1 →
    (∀ j, p < j → j ≤ M.length - 1 → entry M 0 p < entry M 0 j) →
    ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
      entry M 2 p ≤ 1 ∧
      CtxOK (shiftl0 (entry M 0 p) (seg M (p + 1) (M.length - 1 - p)))
        (entry M 1 p) (entry M 2 p)

/-- **The context-suffix core falls to the plant core**, given the infix
equipment.  ⟹ the whole machine closes on `CorePlantCtxLift` plus a `W`-level
equipment statement. -/
theorem coreCtxSuffixLift_of_plantctx (hp : CorePlantCtxLift) (hie : InfEquip) :
    CoreCtxSuffixLift := by
  classical
  intro M p hMarg hM2 hplt hMstrict v z hz1 hctx s
  set c : ℕ := entry M 0 p with hc
  set L : ℕ := M.length - 1 - p with hL
  have hLpos : 0 < L := by omega
  set M' : TrioSeq := shiftl0 c (seg M (p + 1) L) with hM'
  have hM'len : M'.length = L := by rw [hM', shiftl0_length, seg_length]
  have hM'arg : argOK M' := by
    intro x hx
    rw [hM', mem_shiftl0] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    unfold seg at hy
    rw [List.mem_map] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    rw [List.mem_range'_1] at hj
    have := hMstrict j (by omega) (by omega)
    dsimp only
    omega
  obtain ⟨hz2, hctx'⟩ := hie M p hMarg hM2 hplt hMstrict v z hz1 hctx
  have hres := hp M' hM'arg (by omega) (entry M 1 p) (entry M 2 p) hz2 hctx' s
  have hseg : seg M p L
      = ((entry M 0 p, entry M 1 p, entry M 2 p) : ℕ × ℕ × ℕ)
        :: seg M (p + 1) (L - 1) := by
    rw [show L = (L - 1) + 1 from by omega, seg_cons, Nat.add_sub_cancel]
  have hdrop : M'.dropLast = shiftl0 c (seg M (p + 1) (L - 1)) := by
    rw [hM', show L = (L - 1) + 1 from by omega, seg_snoc, shiftl0_append]
    exact List.dropLast_concat
  have hkey : ((0, entry M 1 p, entry M 2 p) : ℕ × ℕ × ℕ) :: M'.dropLast
      = shiftl0 c (seg M p L) := by
    rw [hdrop, hseg, shiftl0_cons, show entry M 0 p - c = 0 from by omega]
  rwa [hkey] at hres

theorem coreWindow_of_lift (hl : CoreWindowLift) : CoreWindow := by
  intro u Y M p hYd hbased hy hMarg hM2 hpY hpG hpar hplt v z hz1 hctx
  have h := hl u Y M p hYd hbased hy hMarg hM2 hpY hpG hpar hplt v z hz1 hctx 0
  rwa [Lift1_zero] at h

open Classical in
/-- **The row-2 blocker's guarded copies ride on the lifted window**: the
ascending copies block is `graft window (root lift of the previous block)`
(`Croot.gcopies_succ_graft_lift` after re-basing), so `CoreWindowLift` alone
carries it — `CoreBlockedEltHi` is not an independent core. -/
theorem coreBlockedEltHi_of_windowLift (hl : CoreWindowLift) :
    CoreBlockedEltHi := by
  classical
  intro u Y M p hYd hbased hy hMarg hM2 hpY hpG hpar hplt hs2 v z hz1 hctx n hn
  have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
  have hylen : 0 < Y.length := List.length_pos_iff.mpr hy
  set R : TrioSeq := graft M Y with hRdef
  have hRlen : R.length = M.length - 1 + Y.length := by
    rw [hRdef, graft_length]
  have hplt' : p < R.length - 1 := by omega
  set c : ℕ := entry M 0 p with hc
  have hlow : entry R 0 p = c := by
    rw [hc, hRdef, ← Wset.entry_take (X := graft M Y) (l := p + 1) (i := 0)
      (j := p) (by omega), take_graft_low (by omega), Wset.entry_take (by omega)]
  set L : ℕ := R.length - 1 - p with hLdef
  have hLpos : 0 < L := by omega
  have hpL : p + L = R.length - 1 := by omega
  -- the row-2 blocker's own chain
  have hnr := parent_nextR hpG
  rw [hpar, hs2] at hnr
  unfold nextR at hnr
  rw [if_neg (by omega : ¬ (2 : ℕ) = 0), if_neg (by omega : ¬ (2 : ℕ) = 1)] at hnr
  have hle1 : le1 R p (R.length - 1) := hnr.2.2.2.2.1
  have hchain : Relation.ReflTransGen (nextrel0 R) p (R.length - 1) :=
    (le0_of_le1 hle1).2.2
  have hwin := window_of_rtg0 hchain (by omega)
  have hstrict : ∀ j, p < j → j ≤ R.length - 1 → c < entry R 0 j := by
    intro j hj0 hj1
    have := hwin j hj0 hj1
    omega
  set d0 : ℕ := entry R 0 (R.length - 1) - entry R 0 p with hd0def
  set d1 : ℕ := entry R 1 (R.length - 1) - entry R 1 p with hd1def
  have hd0pos : 0 < d0 := by
    have := rtg0_entry0_lt hchain (by omega)
    omega
  have hd1pos : 0 < d1 := by
    have := le1_entry1_lt hle1 (by omega)
    omega
  -- the cut-out block and its window
  set S : TrioSeq := seg R p (L + 1) with hSdef
  set B : TrioSeq := shiftl0 c S with hBdef
  have hSlen : S.length = L + 1 := by rw [hSdef, seg_length]
  have hSc : ∀ x ∈ S, c ≤ x.1 := by
    refine le_of_mem_seg ?_
    intro j hj0 hj1
    rcases Nat.eq_or_lt_of_le hj0 with rfl | hlt
    · omega
    · have := hstrict j hlt (by omega)
      omega
  have hentB0 : ∀ q, q < L + 1 → entry B 0 q = entry R 0 (p + q) - c := by
    intro q hq
    rw [hBdef, entry0_shiftl0', hSdef, entry_seg hq]
  have hbase : entry B 0 0 = 0 := by
    have h := hentB0 0 (by omega)
    rw [Nat.add_zero, hlow] at h
    rw [h]
    omega
  have hup : ∀ l, 0 < l → l ≤ L → entry B 0 0 < entry B 0 l := by
    intro l hl0 hl1
    rw [hbase, hentB0 l (by omega)]
    have := hstrict (p + l) (by omega) (by omega)
    omega
  have hd0e : entry B 0 L = d0 := by
    rw [hentB0 L (by omega), hpL, hd0def, hlow]
  have hlp : le1 B 0 L := by
    rw [hBdef, le1_shiftl0 hSc, hSdef, le1_seg_root (by omega) (by omega), hpL]
    exact hle1
  -- the block splits as a planted root over the window's tail
  have hScons : S = ((entry R 0 p, entry R 1 p, entry R 2 p) : ℕ × ℕ × ℕ)
      :: seg R (p + 1) L := by
    rw [hSdef, seg_cons]
  have hBcons : B = ((0, entry R 1 p, entry R 2 p) : ℕ × ℕ × ℕ)
      :: shiftl0 c (seg R (p + 1) L) := by
    rw [hBdef, hScons, shiftl0_cons,
      show entry R 0 p - c = 0 from by omega]
  have hTlen : (shiftl0 c (seg R (p + 1) L)).length = L := by
    rw [shiftl0_length, seg_length]
  have hargT : argOK (shiftl0 c (seg R (p + 1) L)) := by
    intro x hx
    rw [mem_shiftl0] at hx
    obtain ⟨y, hy', rfl⟩ := hx
    unfold seg at hy'
    rw [List.mem_map] at hy'
    obtain ⟨j, hj, rfl⟩ := hy'
    rw [List.mem_range'_1] at hj
    have := hstrict j (by omega) (by omega)
    dsimp only
    omega
  -- the window is the block's peel
  have hdropB : B.dropLast = shiftl0 c (seg R p L) := by
    rw [hBdef, hSdef, seg_snoc, shiftl0_append]
    exact List.dropLast_concat
  have hwlift : ∀ s : ℕ, Lift1 B.dropLast s ∈ GX := by
    intro s
    rw [hdropB]
    exact hl u Y M p hYd hbased hy hMarg hM2 hpY hpG hpar hplt v z hz1 hctx s
  -- re-base the copies block and run the induction
  have hrebase : shiftl0 c (gcopies R p L d0 d1 n) = gcopies B 0 L d0 d1 n := by
    rw [hBdef, hSdef]
    refine shiftl0_gcopies_seg (by omega) ?_
    intro j hj0 hj1
    rcases Nat.eq_or_lt_of_le hj0 with rfl | hlt
    · omega
    · have := hstrict j hlt (by omega)
      omega
  have hmain := gcopiesLift_mem_GX hBcons hTlen hLpos hargT hup hd0pos hd0e
    hd1pos hlp hwlift n 0
  rw [Lift1_zero] at hmain
  rw [hrebase]
  exact hmain

/-- **γ' reduces to element membership**: the descended context `M.take (p+1)`
is equipped by restriction, so the package is a `GX` application of the copies
element.  Since `GX` now also carries the singleton contexts (`1 ≤ |M|`), the
root slice `p = 0` needs no separate core. -/
theorem coreBlocked_of_elt (he : CoreBlockedElt) : CoreBlocked := by
  intro u Y M p AY hbased hy hMarg hM2 hpY hpG hpar hplt
    v z hz1 hctx a t n hva hn
  have helt := he u Y M p AY hbased hy hMarg hM2 hpY hpG hpar hplt
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
  have htk1 : 1 ≤ (M.take (p + 1)).length := by
    rw [List.length_take]; omega
  exact GX_full helt hbe (argOK_take hMarg (p + 1)) htk1
    (ctxOK_take hctx (p + 1)) hz1 hva

/-- **The family core from the lifted-plant core**: the row-2 tower's elements
are exactly the lifted planted blocks `Lift1 (Nb⟦j⟧) d1` over the equipped
composite context, so the copy-index induction stays inside `GX` — no foreign
`W`-elements and no self-reference. -/
theorem coreT2EFam_of_plantctx (hp : CorePlantCtxLift) : CoreT2EFam := by
  classical
  intro u Y M hYd hbased hy hMarg hM2 hs2 hdG v z hz1 hctx hpN
  obtain ⟨m, hdm⟩ := hdG
  have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
  have hylen : 0 < Y.length := List.length_pos_iff.mpr hy
  have hR : argOK (graft M Y) := argOK_graft hMne hMarg Y
  have hRne : graft M Y ≠ [] :=
    List.length_pos_iff.mp (by rw [graft_length]; omega)
  have hR2 : 1 ≤ (graft M Y).length := by rw [graft_length]; omega
  have hctxR : CtxOK (graft M Y) v z :=
    ctxOK_graft hMarg hM2 hz1 hctx hYd hbased
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
  set d1 : ℕ := entry R 1 (R.length - 1) - v with hd1
  have hN0 : Nb⟦0⟧ = [] := by
    rw [oper_gcopies 0 hL hzz hpN', hpar0]
    simp [gcopies]
  have hstep : ∀ i, Nb⟦i + 1⟧ = p0 :: graft R (Lift1 (Nb⟦i⟧) d1) := by
    intro i
    rw [hd1]
    exact oper_cons_tower2 hR hRne hdm hs2 hpN
  have hbNb : ∀ j, based (Nb⟦j⟧) := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [hN0]; exact based_nil
    · exact based_oper hj (by rw [hNdef]; exact based_cons v z R)
  have hNb1 : entry Nb 1 0 = v := by
    rw [hNdef, hp0]
    show ((((0, v, z) : ℕ × ℕ × ℕ) :: R).getD 0 (0, 0, 0)).2.1 = v
    rfl
  have hn2 : nextrel2 Nb 0 R.length := by
    have h := parent_nextR hpN'
    rw [hpar0, hsrN, hNlen] at h
    unfold nextR at h
    rw [if_neg (by omega), if_neg (by omega)] at h
    exact h
  have hd1pos : 0 < d1 := by
    have hlt := le1_entry1_lt hn2.2.2.2.2.1 (by omega)
    rw [hE 1, hNb1] at hlt
    rw [hd1]; omega
  have hcons : ∀ j, Nb⟦j⟧ = [] ∨ ∃ S : TrioSeq, argOK S ∧ Nb⟦j⟧ = p0 :: S := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact Or.inl hN0
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      exact Or.inr ⟨graft R (Lift1 (Nb⟦i⟧) d1), argOK_graft hRne hR _, hstep i⟩
  -- the tower's elements never leave `GX`, at EVERY lift above `d1`:
  -- the ambient mask lift of a tower element is absorbed by its own root lift
  -- (`mlift_Lift1_cons`), so no `CoreMaskLift` is needed.
  have hfam : ∀ j s, Lift1 (Nb⟦j⟧) (d1 + s) ∈ GX := by
    intro j
    induction j with
    | zero =>
        intro s
        rw [hN0, Lift1_nil]
        exact nil_mem_GX
    | succ i ih =>
        intro s
        have hbD : based (Lift1 (Nb⟦i⟧) d1) := based_Lift1 d1 (hbNb i)
        have hDG : Lift1 (Nb⟦i⟧) d1 ∈ GX := by
          have h := ih 0
          rwa [Nat.add_zero] at h
        have hmask : mlift (Lift1 (Nb⟦i⟧) d1) v (d1 + s) ∈ GX := by
          rcases hcons i with h0 | ⟨S, hS, hSe⟩
          · have hnil : mlift ([] : TrioSeq) v (d1 + s) = [] := by simp [mlift]
            rw [h0, Lift1_nil, hnil]
            exact nil_mem_GX
          · have h := ih (d1 + s)
            rw [hSe, hp0] at h ⊢
            rw [mlift_Lift1_cons hS hd1pos]
            exact h
        rw [hstep i]
        exact liftPlant_of_mask hp hR hR2 hz1 hctxR hDG hbD hmask
  intro j _ a s ha
  have hj0 := hfam j 0
  rw [Nat.add_zero] at hj0
  exact GX_full hj0 (based_Lift1 d1 (hbNb j)) hR hR2 hctxR hz1 ha

/-- Direct wiring: **β needs only the lifted planted CONTEXT** — no datum-side
mask core, because the tower's data are root lifts of the tower's own previous
level and the ambient mask is absorbed by `mlift_Lift1_cons`. -/
theorem coreT2E_of_plantctx (hp : CorePlantCtxLift) : CoreT2E :=
  coreT2E_of_fam (coreT2EFam_of_plantctx hp)

open Classical in
/-- **α reduces to the lifted-plant core**: the lifted block is a
root-parented row-1 tower over the lifted composite context, and the tower is
iterated grafting into its own principal block (`tow_mem_GX`), so the whole
tower is carried by the lifted planted peel `Lift1 ((0,v,z) :: graft M Y↓) t`
— no `W`-data at the raised stage `m + 2t` is needed. -/
theorem coreT1L_of_plantctx (hp : CorePlantCtxLift) : CoreT1L := by
  classical
  intro u Y M hYd hbased hy hMarg hM2 hs1 hdG v z hz1 hctx a t hva hpN
  obtain ⟨m, hd⟩ := hdG
  have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
  have hylen : 0 < Y.length := List.length_pos_iff.mpr hy
  have hR : argOK (graft M Y) := argOK_graft hMne hMarg Y
  have hRne : graft M Y ≠ [] :=
    List.length_pos_iff.mp (by rw [graft_length]; omega)
  have hR2 : 1 ≤ (graft M Y).length := by rw [graft_length]; omega
  have hpY : ¬ hasParent Y (srow Y (Y.length - 1)) (Y.length - 1) :=
    fun hp => hd.2 (hasParent_graft_inner hMne hy hp)
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
  have hRt2 : 1 ≤ Rt.length := by rw [hRtlen]; exact hR2
  have hctxRt : CtxOK Rt (v + t) z :=
    ctxOK_ltail hMarg hM2 hz1 hctx hYd.1 hbased
  -- the lifted planted peel block carries the whole tower
  have hTplant : (((0, v + t, z) : ℕ × ℕ × ℕ) :: Rt.dropLast) ∈ GX := by
    rw [hRtdef, Wset.ltail_dropLast, hRdef, graft_dropLast hy]
    exact liftPlant_of_mask hp hMarg hM2 hz1 hctx hYd.1 (based_dropLast hbased)
      (gxs_mlift hYd v t)
  have hTow : ∀ k, Wset.tow (v + t) z Rt k ∈ GX := tow_mem_GX hRtne hTplant
  refine A1_intro (Or.inr (Or.inl (fun n hn => ?_)))
  rw [hNbdef, Wset.lift_cons, ← hRtdef,
    oper_cons_tower1 hRtOK hRtne hdRt hsrRt hpMt]
  rcases n with _ | k
  · simpa [Wset.tow] using W_nil a
  · have hres := GX_full (hTow k) (Wset.based_tow (v + t) z Rt k) hRtOK hRt2
      hctxRt hz1 (t := 0) (by omega)
    rw [Lift1_zero] at hres
    exact hres

open Classical in
/-- **The GX machine closes** modulo the three cores. -/
theorem gx_of_pieces (hb : CoreBlocked) (h1 : CoreT1L) (h2 : CoreT2E) :
    ∀ (u : ℕ) (Y : TrioSeq), Y.dropLast ∈ GXs →
      (hasParent Y (srow Y (Y.length - 1)) (Y.length - 1) →
        ∀ n, 1 ≤ n → Y⟦n⟧ ∈ GXs) → Y ∈ GX := by
  intro u Y hYd hin
  intro hbased M hMarg hM2 v z hz1 hctx i hi a t hva
  have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
  rcases Nat.lt_or_eq_of_le hi with hilt | hieq
  · -- element-prefix obligations: uniform one-step discharge from the datum
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      rw [List.take_zero, graft_nil, List.dropLast_eq_take]
      exact hctx (M.length - 1) (by omega) a t hva
    · have hY2 : 2 ≤ Y.length := by omega
      have hres := hYd.1 (based_dropLast hbased) M hMarg hM2 v z hz1 hctx i
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
  have hGpos : 1 ≤ (graft M Y).length := by rw [graft_length]; omega
  by_cases hpY : hasParent Y (srow Y (Y.length - 1)) (Y.length - 1)
  · -- (a) inner
    have hyL : Y.length - 1 ≠ 0 := by
      have := nextR_index_lt (parent_nextR hpY)
      omega
    refine A1_intro (Or.inr (Or.inl fun n hn => ?_))
    rw [lift_graft_inner_step v z t n hMne hy hyL hG hpY]
    exact GX_full (hin hpY n hn).1 (based_oper hn hbased) hMarg hM2 hctx hz1 hva
  -- trailing dead within the graft block
  have hYdrop : Y.dropLast ∈ GXs := hYd
  by_cases hpG : hasParent (graft M Y)
      (srow (graft M Y) ((graft M Y).length - 1)) ((graft M Y).length - 1)
  · -- (γ) blocked
    have hplt := blocked_parent_lt hMne hy hpY hpG
    have hM2' : 2 ≤ M.length := by omega
    have hGL : (graft M Y).length - 1 ≠ 0 := by
      have := nextR_index_lt (parent_nextR hpG)
      omega
    refine A1_intro (Or.inr (Or.inl fun n hn => ?_))
    rw [lift_graft_blocked_step v z t n hMne hy hG hGL hpG rfl hplt]
    exact hb u Y M _ hYdrop hbased hy hMarg hM2' hpY hpG rfl hplt
      v z hz1 hctx a t n hva hn
  have hdrop : Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: graft M Y.dropLast) t ∈ W a :=
    GX_full hYdrop.1 (based_dropLast hbased) hMarg hM2 hctx hz1 hva
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
      · exact h1 u Y M hYdrop hbased hy hMarg hM2 hs1 ⟨_, hdG⟩
          v z hz1 hctx a t hva (by rw [hs1] at hpN ⊢; exact hpN)
      · exact h2 u Y M hYdrop.1 hbased hy hMarg hM2 hs2 ⟨_, hdG⟩
          v z hz1 hctx a t hva (by rw [hs2] at hpN ⊢; exact hpN)
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


open Classical in
/-- **The machine closes**: `Aop` supplies exactly the two pieces
(`gx_take` makes the peel a `GXs`-member in the clause-2 case). -/
theorem GX_closed (hb : CoreBlocked) (h1 : CoreT1L) (h2 : CoreT2E) :
    ∀ (u : ℕ) (Y : TrioSeq), Aop W u GXs Y → Y ∈ GX := by
  classical
  intro u Y AY
  have hYd : Y.dropLast ∈ GXs := by
    by_cases hY2 : 2 ≤ Y.length
    · rcases AY with ⟨hl, -⟩ | hop | ⟨m, -, -, hgr⟩
      · omega
      · have h := gxs_take (hop 1 le_rfl) (Y.length - 1)
        rwa [oper_take_prefix (by omega) le_rfl (le_refl _),
          ← List.dropLast_eq_take] at h
      · have h := hgr [] (W_nil m) based_nil
        rwa [graft_nil] at h
    · have hYd0 : Y.dropLast = [] := by
        rw [List.dropLast_eq_take, show Y.length - 1 = 0 from by omega]
        rfl
      rw [hYd0]
      exact nil_mem_GXs
  refine gx_of_pieces hb h1 h2 u Y hYd (fun hp n hn => ?_)
  rcases AY with ⟨hl, -⟩ | hop | ⟨m, -, hd, -⟩
  · exact absurd (nextR_index_lt (parent_nextR hp)) (by omega)
  · exact hop n hn
  · exact absurd hp hd.2

/-- **The planted-root staircase core**: the ONE place where the staircase
transport of `Aop` fails.  A length-1 element `[(0,b,c)]` expands to itself, so
it can only satisfy `Aop`'s clause 3, whose datum lives at stage `2b+c-1`; the
staircase lift raises the root to `φ b`, hence the required stage to
`2(φ b)+c-1`.  Everything else transports: clause 1 by `Stair.zero`, clause 2 by
`slift_oper` (G2), and clause 3 collapses to clause 2 because `domT`'s second
component is `¬ hasParent`. -/
def CoreStairOm : Prop :=
  ∀ (u : ℕ) (Y : TrioSeq), Aop W u GXs Y → based Y → Y.length = 1 →
    ∀ φ : ℕ → ℕ, Stair φ → slift Y φ ∈ GX

open Classical in
/-- **The planted root is in the machine's set**, with all its staircase lifts:
a length-1 sequence's last column has no parent, so `gx_of_pieces` runs on it
with the empty peel and a vacuous inner clause. -/
theorem singleton_mem_GXs (hb : CoreBlocked) (h1 : CoreT1L) (h2 : CoreT2E)
    (b c : ℕ) : [((0, b, c) : ℕ × ℕ × ℕ)] ∈ GXs := by
  classical
  have key : ∀ B C : ℕ, [((0, B, C) : ℕ × ℕ × ℕ)] ∈ GX := by
    intro B C
    refine gx_of_pieces hb h1 h2 0 _ ?_ (fun hp n hn => ?_)
    · show ([((0, B, C) : ℕ × ℕ × ℕ)]).dropLast ∈ GXs
      exact nil_mem_GXs
    · exact absurd (nextR_index_lt (parent_nextR hp)) (by simp)
  refine ⟨key b c, fun φ hφ => ?_⟩
  rw [slift_singleton b c hφ]
  exact key _ _

/-! ### 装備クラスの自己支持性は機械の操作で保たれる

`SelfSup M v z` = 装備つき文脈 `M` の**植えた接頭辞がすべて `GX` に入る**。
`CorePlantCtxLift` はこれの `k = |M|-1` 版（`equipSelf_of_corePlantCtxLift`）。
以下の 3 補題は「自己支持的な装備つき文脈のクラスは `take` / `graft` /
`ltail` で閉じる」ことを示す — 将来そのクラスを構成するときの閉包則。 -/

def SelfSup (M : TrioSeq) (v z : ℕ) : Prop :=
  ∀ k, k < M.length → ∀ t : ℕ,
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: M.take k) t ∈ GX

theorem selfSup_take {M : TrioSeq} {v z : ℕ} (h : SelfSup M v z) (j : ℕ) :
    SelfSup (M.take j) v z := by
  intro k hk t
  rw [List.length_take] at hk
  rw [List.take_take, Nat.min_eq_left (by omega)]
  exact h k (by omega) t

open Classical in
/-- **自己支持性は接ぎ木で保たれる**: 接頭辞は文脈側か「植え文脈 + データの
マスク」に分解する（`liftPlant_of_plant`）。 -/
theorem selfSup_graft {M Y : TrioSeq} {v z : ℕ} (hMarg : argOK M)
    (hM2 : 1 ≤ M.length) (hz1 : z ≤ 1) (hctx : CtxOK M v z)
    (hself : SelfSup M v z) (hYd : Y.dropLast ∈ GXs) (hbY : based Y) :
    SelfSup (graft M Y) v z := by
  classical
  intro k hk t
  rw [graft_length] at hk
  rcases Nat.lt_or_ge k M.length with hkM | hkM
  · rw [take_graft_low (by omega)]
    exact hself k (by omega) t
  · obtain ⟨j, rfl⟩ : ∃ j, k = M.length - 1 + j := ⟨k - (M.length - 1), by omega⟩
    have hjY : j < Y.length := by omega
    rw [take_graft_high]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [List.take_zero, graft_nil, List.dropLast_eq_take]
      exact hself (M.length - 1) (by omega) t
    · have hYtj : Y.take j ∈ GXs := by
        have h := gxs_take hYd j
        rwa [dropLast_take (by omega)] at h
      have hbtj : based (Y.take j) := by
        show entry (Y.take j) 0 0 = 0
        rw [Wset.entry_take (X := Y) (l := j) (i := 0) (j := 0) (by omega)]
        exact hbY
      have hplant : Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast) t ∈ GX := by
        rw [List.dropLast_eq_take]
        exact hself (M.length - 1) (by omega) t
      exact liftPlant_of_plant hplant hMarg hM2
        hYtj.1 hbtj (gxs_mlift hYtj v t)

/-- **自己支持性はリフト文脈でも保たれる**（`ltail_take` + `Lift1_Lift1`）。 -/
theorem selfSup_ltail {R : TrioSeq} {v z t : ℕ} (h : SelfSup R v z) :
    SelfSup (Wset.ltail v z R t) (v + t) z := by
  intro k hk s
  rw [Wset.ltail_length] at hk
  rw [Wset.ltail_take (by omega), ← Wset.lift_cons, Lift1_Lift1]
  exact h k hk (t + s)

/-- **The equipment class is self-supporting**: every equipped context's own
planted prefixes are in the machine's set.  This is EXACTLY `CorePlantCtxLift`
(`ctxOK_take` moves between a general `k` and `k = |M| - 1`), which identifies
the core as a property of the *equipment class*, not of any single context. -/
def EquipSelf : Prop :=
  ∀ (M : TrioSeq), argOK M → 1 ≤ M.length → ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
    ∀ k, k < M.length → ∀ t : ℕ,
      Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: M.take k) t ∈ GX

theorem corePlantCtxLift_of_equipSelf (h : EquipSelf) : CorePlantCtxLift := by
  intro M hMarg hM2 v z hz1 hctx t
  rw [List.dropLast_eq_take]
  exact h M hMarg hM2 v z hz1 hctx (M.length - 1) (by omega) t

theorem equipSelf_of_corePlantCtxLift (h : CorePlantCtxLift) : EquipSelf := by
  intro M hMarg hM2 v z hz1 hctx k hk t
  have h2 : 1 ≤ (M.take (k + 1)).length := by rw [List.length_take]; omega
  have hres := h (M.take (k + 1)) (argOK_take hMarg (k + 1)) h2 v z hz1
    (ctxOK_take hctx (k + 1)) t
  rwa [List.dropLast_eq_take, List.length_take, List.take_take,
    show min (min (k + 1) M.length - 1) (k + 1) = k from by omega] at hres

/-- **`CorePlantCtxLift` is bounded above by the self-reference**: the equipment
`CtxOK M v z` already puts the lifted planted peel in `W a` (take `k = |M|-1`),
so the core is at most "every based `W`-element is in `GX`".  This is only an
upper bound — the point of the campaign is to prove the core WITHOUT the
self-reference (by induction on the context's length). -/
theorem corePlantCtxLift_of_self
    (hs : ∀ (u : ℕ) (y : TrioSeq), y ∈ W u → based y → y ∈ GX) :
    CorePlantCtxLift := by
  intro M hMarg hM2 v z hz1 hctx t
  have hW := hctx (M.length - 1) (by omega) (2 * (v + t) + z) t (le_refl _)
  rw [← List.dropLast_eq_take] at hW
  exact hs _ _ hW (by
    show entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast) t) 0 0 = 0
    rw [entry0_Lift1]
    exact based_cons v z M.dropLast)

open Classical in
/-- **The planted-root staircase core is DISCHARGED**: a length-1 element's own
last column can have no parent (there is no earlier index), so `gx_of_pieces`
runs on it with the empty peel and a vacuous inner clause — no `Aop`, hence no
stage, is consumed. -/
theorem coreStairOm_holds (hb : CoreBlocked) (h1 : CoreT1L) (h2 : CoreT2E) :
    CoreStairOm := by
  intro u Y _ _ hlen φ _
  refine gx_of_pieces hb h1 h2 u (slift Y φ) ?_ (fun hp n hn => ?_)
  · have h0 : (slift Y φ).dropLast = [] := by
      rw [List.dropLast_eq_take, slift_length, hlen]
      rfl
    rw [h0]
    exact nil_mem_GXs
  · exact absurd (nextR_index_lt (parent_nextR hp))
      (by rw [slift_length, hlen]; omega)

open Classical in
/-- **Staircase transport of `Aop`** (length ≥ 2, so no planted-root case). -/
theorem aop_slift {u : ℕ} {Y : TrioSeq} (AY : Aop W u GXs Y) (hY2 : 2 ≤ Y.length)
    {φ : ℕ → ℕ} (hφ : Stair φ) : Aop W u GXs (slift Y φ) := by
  classical
  have hYL : Y.length - 1 ≠ 0 := by omega
  rcases AY with ⟨hl, -⟩ | hop | ⟨m, -, hd, hgr⟩
  · omega
  · exact Or.inr (Or.inl fun n hn => by
      rw [← slift_oper hφ]
      exact gxs_slift (hop n hn) hφ)
  · have hYd : Y.dropLast ∈ GXs := by
      have h := hgr [] (W_nil m) based_nil
      rwa [graft_nil] at h
    refine Or.inr (Or.inl fun n hn => ?_)
    rw [← slift_oper hφ]
    have hpred : Y⟦n⟧ = Y.dropLast := by
      have hee : Y⟦n⟧ = Pred Y := by
        by_cases hz0 : entry Y 0 (Y.length - 1) = 0 ∧
            entry Y 1 (Y.length - 1) = 0 ∧ entry Y 2 (Y.length - 1) = 0
        · exact oper_eq_pred_of_zero n hYL hz0
        · exact oper_eq_pred_of_noParent n hYL hz0 hd.2
      rw [hee]
      unfold Pred
      rw [if_neg (by omega)]
    rw [hpred]
    exact gxs_slift hYd hφ

open Classical in
/-- **The machine closes on the staircase-closed set** modulo the four cores. -/
theorem GXs_closed (hb : CoreBlocked) (h1 : CoreT1L) (h2 : CoreT2E) :
    ∀ (u : ℕ) (Y : TrioSeq), Aop W u GXs Y → Y ∈ GXs := by
  classical
  have hom : CoreStairOm := coreStairOm_holds hb h1 h2
  intro u Y AY
  refine ⟨GX_closed hb h1 h2 u Y AY, fun φ hφ => ?_⟩
  by_cases hY2 : 2 ≤ Y.length
  · exact GX_closed hb h1 h2 u (slift Y φ) (aop_slift AY hY2 hφ)
  · rcases Nat.eq_zero_or_pos Y.length with h0 | h1'
    · have hYnil : Y = [] := List.length_eq_zero_iff.mp h0
      subst hYnil
      have hnil : slift ([] : TrioSeq) φ = [] := by simp [slift]
      rw [hnil]
      exact nil_mem_GX
    · intro hbs
      have hbY : based Y := by
        show entry Y 0 0 = 0
        rw [← entry0_slift Y φ 0]
        exact hbs
      exact hom u Y AY hbY (by omega) φ hφ hbs

/-- **A2 corollary**: every `W`-element is in the staircase-closed set. -/
theorem W_le_GXs (hb : CoreBlocked) (h1 : CoreT1L) (h2 : CoreT2E) (u : ℕ) :
    W u ⊆ GXs :=
  A2' (fun Y hY => GXs_closed hb h1 h2 u Y hY)

/-- **A2 corollary**: every `W`-element is in the machine's set. -/
theorem W_le_GX (hb : CoreBlocked) (h1 : CoreT1L) (h2 : CoreT2E) (u : ℕ) :
    W u ⊆ GX :=
  fun _ hy => (W_le_GXs hb h1 h2 u hy).1

/-- **`GraftAll` holds modulo the three cores.**  `GraftAll` now carries the
context's own slice equipment (supplied by the `Wstar2s` induction,
`Wset.take_mem_Wstar2_of_Aop`), so the machine matches it exactly — the old
"unequipped contexts" gap is closed. -/
theorem graftAll_of_GX (hb : CoreBlocked) (h1 : CoreT1L) (h2 : CoreT2E) :
    Wset.GraftAll := by
  intro S hS hSne v z hz1 hctx u y hy hby _ a t hva
  have hyGX : y ∈ GX := W_le_GX hb h1 h2 u hy
  have hSlen : 1 ≤ S.length := List.length_pos_iff.mpr hSne
  exact GX_full hyGX hby hS hSlen hctx hz1 hva

/-- **The assembly loop, explicit**: modulo the γ'-core and the lifted-context
equipment, the machine's closure consumes only its own inclusion `W ⊆ GX`
(α via `coreT1L_of_le`, β via `coreT2EStep_of_le`).  Well-founding this
self-reference — with the provenance descent measured in `probe_strat`
(β-orphans = context material, position non-increasing; α-orphans = planted
roots, stage-bounded) — is the single remaining task of the campaign. -/
theorem GX_loop (he : CoreBlockedElt) (hp : CorePlantCtxLift) :
    ∀ (u : ℕ) (Y : TrioSeq), Aop W u GXs Y → Y ∈ GXs :=
  GXs_closed (coreBlocked_of_elt he) (coreT1L_of_plantctx hp)
    (coreT2E_of_plantctx hp)

/-- **The assembly loop, window form**: the honest residue list.  `CoreWindow`
is the composite's own window (context suffix + the datum's shifted peel);
`CoreCtxSuffix` below is the strictly stronger context-only form, and reducing
to it throws away the datum's hypotheses — keep both statements in view. -/
theorem GX_loop_window (hw : CoreWindow) (hhi : CoreBlockedEltHi)
    (hp : CorePlantCtxLift) :
    ∀ (u : ℕ) (Y : TrioSeq), Aop W u GXs Y → Y ∈ GXs :=
  GX_loop (coreBlockedElt_of_window hw hhi) hp

/-- **The assembly loop, context-piece form**: every residue in its finest
currently known shape — three *context* statements (`CoreCtxSuffix` = the
re-based suffix, `CoreBlocked0` = the root slice, `CorePlantCtxLift` = the
lifted planted peel), the row-2 blocker's guarded copies (`CoreBlockedEltHi`),
and the planted-root staircase core (`CoreStairOm`).  **No datum-side lift
core survives**: beta absorbs its mask into the tower's own root lift
(`mlift_Lift1_cons`) and alpha reads it off `GXs`. -/
theorem GX_loop_pieces (hsuf : CoreCtxSuffix) (hhi : CoreBlockedEltHi)
    (hp : CorePlantCtxLift) :
    ∀ (u : ℕ) (Y : TrioSeq), Aop W u GXs Y → Y ∈ GXs :=
  GX_loop (coreBlockedElt_of_window (coreWindow_of_suffix hsuf) hhi) hp

/-- **The assembly loop, two-core form**: the whole machine closes on
`CoreWindowLift` (the composite's re-based window and all its root lifts) and
`CorePlantCtxLift` (the equipped context's lifted planted peel).  The row-2
blocker's guarded copies are NOT an independent core — they are iterated
grafting into the window with a root lift at each stage
(`coreBlockedEltHi_of_windowLift`). -/
theorem GX_loop_lift (hwl : CoreWindowLift) (hp : CorePlantCtxLift) :
    ∀ (u : ℕ) (Y : TrioSeq), Aop W u GXs Y → Y ∈ GXs :=
  GX_loop (coreBlockedElt_of_window (coreWindow_of_lift hwl)
    (coreBlockedEltHi_of_windowLift hwl)) hp

/-- **The assembly loop, pure-context form**: both surviving cores speak only
about the *context* — no datum, no expansion.  `CoreCtxSuffixLift` is the
context's re-based infix from the blocker with all its root lifts;
`CorePlantCtxLift` is the context's planted peel with all its root lifts. -/
theorem GX_loop_ctx (hsl : CoreCtxSuffixLift) (hp : CorePlantCtxLift) :
    ∀ (u : ℕ) (Y : TrioSeq), Aop W u GXs Y → Y ∈ GXs :=
  GX_loop_lift (coreWindowLift_of_ctxSuffixLift hsl) hp

/-- **The assembly loop, one-`GX`-core form**: a single `GX`-level core
(`CorePlantCtxLift`) plus a pure `W`-level equipment statement (`InfEquip`). -/
theorem GX_loop_plant (hie : InfEquip) (hp : CorePlantCtxLift) :
    ∀ (u : ℕ) (Y : TrioSeq), Aop W u GXs Y → Y ∈ GXs :=
  GX_loop_ctx (coreCtxSuffixLift_of_plantctx hp hie) hp

/-! ### ⚠ 逆向き: 核は `GraftAll` より弱くない

`graftAll_of_cores` の逆も成り立つ。したがって「2 本の文脈核」への還元は
**同値変形**であって強さを落としてはいない。閉じるには「さらに小さい核へ
還元する」のではなく、**新しい帰納法**が要る（この事実を明示しておかないと
還元を証明と取り違える危険がある）。 -/

open Classical in
/-- **The plant core is no weaker than `GraftAll` itself.**  Every prefix of the
lifted planted peel is a `W`-package (that IS the equipment), so `GraftAll`
hands the graft obligations straight back. -/
theorem corePlantCtxLift_of_graftAll (hga : Wset.GraftAll) :
    CorePlantCtxLift := by
  classical
  intro M hMarg hM1 v z hz1 hctx t
  intro _hb N hNarg hNlen v' z' hz1' hctxN i hi a t' hva
  have hNne : N ≠ [] := List.length_pos_iff.mp (by omega)
  have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
  have hplen : (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast).length = M.length := by
    rw [List.length_cons, List.length_dropLast]
    omega
  have hi' : i ≤ (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast).length := by
    rwa [Lift1_length] at hi
  set Q : TrioSeq := (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast) t).take i
    with hQdef
  have hQW : Q ∈ W (2 * (v + t) + z) := by
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [hQdef, List.take_zero]
      exact W_nil _
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hjM : j ≤ M.length - 1 := by rw [hplen] at hi'; omega
      have hcons : (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast).take (j + 1)
          = ((0, v, z) : ℕ × ℕ × ℕ) :: M.take j := by
        rw [List.take_succ_cons, dropLast_take hjM]
      rw [hQdef, Lift1_take hi', hcons]
      exact hctx j (by omega) (2 * (v + t) + z) t le_rfl
  have hbQ : based Q := by
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [hQdef, List.take_zero]
      exact based_nil
    · show entry Q 0 0 = 0
      rw [hQdef, Wset.entry_take (l := i) (by omega), entry0_Lift1]
      rfl
  have hc : 0 < entry N 0 (N.length - 1) := by
    have hmem : N.getD (N.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) ∈ N := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega : N.length - 1 < N.length)]
      exact List.getElem_mem _
    exact hNarg _ hmem
  have hargOK : argOK (graft N Q) := by
    rw [graft_eq_shift]
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hNarg x (List.dropLast_subset _ h)
    · unfold shiftr01 at h
      rw [List.mem_map] at h
      obtain ⟨q, -, rfl⟩ := h
      dsimp only
      omega
  exact hga N hNarg hNne v' z' hz1' hctxN (2 * (v + t) + z) Q hQW hbQ hargOK
    a t' hva

/-! ## 全体の組み上げ

2 つの文脈核から `GraftAll`、そして「`W` の元とその接頭辞はすべて植えブロック
package」（`Wstar2s`）まで一気に通る。装備は `Wstar2s` 帰納法自身が供給する
（`Wset.take_mem_Wstar2_of_Aop`）ので、文脈側のギャップは残っていない。 -/

/-- **The three machine cores from the two context cores.** -/
theorem coreBlocked_of_ctxSuffixLift (hsl : CoreCtxSuffixLift) : CoreBlocked :=
  coreBlocked_of_elt (coreBlockedElt_of_window
    (coreWindow_of_lift (coreWindowLift_of_ctxSuffixLift hsl))
    (coreBlockedEltHi_of_windowLift (coreWindowLift_of_ctxSuffixLift hsl)))

/-- **`GraftAll` from the two context cores.** -/
theorem graftAll_of_cores (hsl : CoreCtxSuffixLift) (hp : CorePlantCtxLift) :
    Wset.GraftAll :=
  graftAll_of_GX (coreBlocked_of_ctxSuffixLift hsl) (coreT1L_of_plantctx hp)
    (coreT2E_of_plantctx hp)

/-- **`GraftAll` from one `GX`-core plus the `W`-level infix equipment.** -/
theorem graftAll_of_plant (hie : InfEquip) (hp : CorePlantCtxLift) :
    Wset.GraftAll :=
  graftAll_of_cores (coreCtxSuffixLift_of_plantctx hp hie) hp

/-- **The campaign's headline**: modulo the two *context* cores, every
`W`-element and every one of its prefixes is a planted `W`-package. -/
theorem W_le_Wstar2s_of_cores (hsl : CoreCtxSuffixLift) (hp : CorePlantCtxLift)
    (u : ℕ) : Wset.W u ⊆ Wset.Wstar2s :=
  W_le_Wstar2s (graftAll_of_cores hsl hp) u

end TRIO
