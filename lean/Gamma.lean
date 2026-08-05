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
    (hM : argOK M) (hM2 : 2 ≤ M.length) (hctx : CtxOK M v z)
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
    Y.dropLast ∈ GX → based Y → Y ≠ [] →
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
    Y.dropLast ∈ GX → based Y → Y ≠ [] →
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
  ∀ (M D : TrioSeq), argOK M → 2 ≤ M.length → ∀ v z : ℕ, z ≤ 1 →
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
  ∀ M : TrioSeq, argOK M → 2 ≤ M.length → ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
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
  ∀ M : TrioSeq, argOK M → 2 ≤ M.length → ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
    ∀ t : ℕ, Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast) t ∈ GX

open Classical in
/-- **α 残差の分割**: リフトした植えブロックは、リフトした植え文脈にデータの
マスクリフトを接ぎ木したもの。 -/
theorem liftPlant_of_mask (hp : CorePlantCtxLift) {M D : TrioSeq} {v z t : ℕ}
    (hMarg : argOK M) (hM2 : 2 ≤ M.length) (hz1 : z ≤ 1) (hctx : CtxOK M v z)
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
  exact hp M hMarg hM2 v z hz1 hctx t

open Classical in
/-- **α 残差の分割**: リフトした植えブロックは、リフトした植え文脈にデータの
マスクリフトを接ぎ木したもの。 -/
theorem coreLiftPlant_of_mask (hp : CorePlantCtxLift) (hm : CoreMaskLift) :
    CoreLiftPlant := fun M D hMarg hM2 v z hz1 hctx hD hbD t =>
  liftPlant_of_mask hp hMarg hM2 hz1 hctx hD hbD (hm D hD hbD v t)

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
      shiftl0 (entry M 0 p)
        (seg (graft M Y) p ((graft M Y).length - 1 - p)) ∈ GX

/-- **The context-suffix core**: the context's own re-based suffix (from the
blocker `p`, minus its trailing column) is in the machine's set — a statement
about the *context alone*. -/
def CoreCtxSuffix : Prop :=
  ∀ (M : TrioSeq) (p : ℕ), argOK M → 2 ≤ M.length → p < M.length - 1 →
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
  intro u Y M p hYdG hbased hy hMarg hM2 hpY hpG hpar hplt
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
    exact hs M p hMarg hM2 hplt

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
    exact hhi u Y M p AY hbased hy hMarg hM2 hpY hpG hpar hplt hs2 n hn
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
        (hw u Y M p AY hbased hy hMarg hM2 hpY hpG hpar hplt) n
    · have h1d : srow R (R.length - 1) = 1 := by omega
      rw [h1d, if_pos (by omega : (0:ℕ) < 1), if_neg (by omega : ¬ (1:ℕ) < 1)]
      exact gcopies_mem_GX hdep hbaseR hL
        (hw u Y M p AY hbased hy hMarg hM2 hpY hpG hpar hplt) n

/-- **The γ'-residue, root slice**: a blocker at the context root descends to a
single-column context — the shift case, outside `GX`'s reach. -/
def CoreBlocked0 : Prop :=
  ∀ (u : ℕ) (Y M : TrioSeq),
    Y.dropLast ∈ GXs → based Y → Y ≠ [] →
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
  have hR2 : 2 ≤ (graft M Y).length := by rw [graft_length]; omega
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
  have hR2 : 2 ≤ (graft M Y).length := by rw [graft_length]; omega
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
  have hRt2 : 2 ≤ Rt.length := by rw [hRtlen]; exact hR2
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
  have hGlen : 2 ≤ (graft M Y).length := by rw [graft_length]; omega
  have hGL : (graft M Y).length - 1 ≠ 0 := by omega
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
    refine A1_intro (Or.inr (Or.inl fun n hn => ?_))
    rw [lift_graft_blocked_step v z t n hMne hy hG hGL hpG rfl hplt]
    exact hb u Y M _ hYdrop hbased hy hMarg hM2 hpY hpG rfl hplt
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
    (hp : CorePlantCtxLift) :
    ∀ (u : ℕ) (Y : TrioSeq), Aop W u GXs Y → Y ∈ GXs :=
  GXs_closed (coreBlocked_of_elt he h0) (coreT1L_of_plantctx hp)
    (coreT2E_of_plantctx hp)

/-- **The assembly loop, context-piece form**: every residue in its finest
currently known shape — three *context* statements (`CoreCtxSuffix` = the
re-based suffix, `CoreBlocked0` = the root slice, `CorePlantCtxLift` = the
lifted planted peel), the row-2 blocker's guarded copies (`CoreBlockedEltHi`),
and the planted-root staircase core (`CoreStairOm`).  **No datum-side lift
core survives**: beta absorbs its mask into the tower's own root lift
(`mlift_Lift1_cons`) and alpha reads it off `GXs`. -/
theorem GX_loop_pieces (hsuf : CoreCtxSuffix) (hhi : CoreBlockedEltHi)
    (h0 : CoreBlocked0) (hp : CorePlantCtxLift) :
    ∀ (u : ℕ) (Y : TrioSeq), Aop W u GXs Y → Y ∈ GXs :=
  GX_loop (coreBlockedElt_of_window (coreWindow_of_suffix hsuf) hhi) h0 hp

end TRIO
