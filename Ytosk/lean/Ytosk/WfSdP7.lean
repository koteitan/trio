/-
**WfSdP7: one absorption hypothesis at `x − 1` for the seed and the base (2026-11-01).**

`UAwRA`: at `i = x − 1` with a failed strong absorption, every component of `V + 1` (`V = v(P₁ i)`, the dropped
`v′(i)`) at every level is at most `Ω_{V+1}` or dominated by a component of `v(i)` (the `VrDomQ` form; `UAwR` is its
restriction to the levels `u ≤ v(i)`). It replaces the `SmallSelf` alternative in both readers:
- `UAwRA.toR` → `qr_seedC2_of` (the seed, WfSdP1);
- `frameMapT1_takeG3`: `frameMapT1_takeG2` (the base `FrameMapT1 ∧ VrDomQ` at `M.take x`) with `UAwRA`.
- `qr_t1_D2`: `qr_t1_D` with the base frame map from `frameMapT1_takeG3`.
-/
import Ytosk.WfSdP6

namespace Ytosk

open T

/-- The component condition at every level. -/
def WCSA (a w : T) : Prop := ∀ u, ∀ g ∈ comps u w, g ≤ psi w z z ∨ ∃ d ∈ comps u a, g ≤ d

theorem WCSA.toWCS2 {a w : T} (h : WCSA a w) : WCS2 a w := fun u _ g hg => h u g hg

/-- **The absorption at `x − 1`, the component condition at every level.** -/
def UAwRA (M : Mat) (ρ : Valn) (x : Nat) : Prop :=
  ∀ i k W, i + 1 = x → upg M i = some k → ρ.v k = add (vOpt ρ (par M 1 i)) W → W ≠ z →
    (∀ s ∈ summands (vOpt ρ (par M 1 i)), s < W → Lhd z s W) ∨
      WCSA (ρ.v i) (add (vOpt ρ (par M 1 i)) one)

theorem UAwRA.toR {M : Mat} {ρ : Valn} {x : Nat} (h : UAwRA M ρ x) : UAwR M ρ x :=
  fun i k W hi hu hv hW => (h i k W hi hu hv hW).imp id WCSA.toWCS2

section

/-- **The base**: `M.take x` with the drop valuation. -/
theorem frameMapT1_takeG3 {M : Mat} {ρ ρ' : Valn} {rk : Bool → Nat → Nat} {r L : Nat} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) (hC' : Cons (M.take (r + L)) ρ') (hRk' : Rk (M.take (r + L)) rk)
    (hlen : r + L + 1 = M.length) (hx2 : entry M 2 (r + L) = 0)
    (hdrop : ∀ i, i < r + L → PO ρ ρ' i ∧ PV2 M ρ ρ' i)
    (hUAs : ∀ k W, r + 1 = r + L → upg M r = some k → ρ.v k = add (vOpt ρ (par M 1 r)) W → W ≠ z →
      (∀ s ∈ summands (vOpt ρ (par M 1 r)), s < W → Lhd z s W) ∨ WCSA (ρ.v r) (add (vOpt ρ (par M 1 r)) one))
    (h3 : par M 0 (r + L) = some r → NoBad3 M ρ ∨ r + 2 = M.length) :
    FrameMapT1 M ρ r L (M.take (r + L)) ρ' ∧ VrDomQ M ρ r L (M.take (r + L)) ρ' := by
  constructor
  · intro k c Lc R s y hcl hsy ht
    left
    have hcT : c ∈ CL (M.take (r + L)) k := by rw [hcl]; simp
    have hcc := cl_mem_children hcT
    have hcx : c < r + L := by have := (mem_children hcc).2; rw [lenT hlen] at this; exact this
    have hkc : k < c := (mem_children hcc).1
    obtain ⟨hv, hL, ⟨Tl, hM⟩, yM, hsyM, hyy, htM⟩ :=
      frame_take_rw2 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hC hG hC' hRk' hdrop hcl hsy ht
    rw [phiT1_lt (show k < r + L by omega), phiT1_lt hcx]
    exact ⟨Lc, R ++ Tl, yM, hM, hv, hL.symm, hsyM, hyy, htM⟩
  · intro hq u g hg
    have hrx : r < r + L := par_lt M 0 _ r hq
    rcases (hdrop r hrx).2.1 with h | ⟨_, _, hnc⟩
    · rcases h with h | h
      · exact Or.inr ⟨g, h ▸ hg, le_refl g⟩
      · obtain ⟨d, hd, hgd⟩ := h.2 u (ρ.v r) h.1 (le_refl _) g hg
        rcases List.mem_append.mp hd with hd | hd
        · exact Or.inr ⟨d, hd, hgd⟩
        · simp [Gc, comps] at hd; subst hd; exact Or.inl (le_trans hgd (z_le _))
    · have common : ∀ k W, r + 2 = M.length → upg M r = some k → ρ.v k = add (vOpt ρ (par M 1 r)) W → W ≠ z →
          ¬ (∀ s ∈ summands (vOpt ρ (par M 1 r)), s < W → Lhd z s W) →
          g ≤ psi (ρ'.v r) z z ∨ ∃ d ∈ comps u (ρ.v r), g ≤ d := by
        intro k W hi2 hu hvk hWz hbad
        rcases hUAs k W (by omega) hu hvk hWz with h | hSm
        · exact absurd h hbad
        · have h12 := upg_e12 hu
          have h2r : entry M 2 r = 0 := by have := S.z2 r; omega
          have hvr := v_last_take (x := r + L) (by omega) S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hC hG hC' hRk'
            (r := r) (by omega) h12.1 h2r
          have hVot : isOT (add (vOpt ρ (par M 1 r)) one) = true :=
            isOT_add (vOpt_ot hG (by omega)) isOT_one
          rw [hvr, sf_ot hVot] at hg ⊢
          exact hSm u g hg
      rcases hnc with hn | ⟨_, _, k, W, hi2, hu, hvk, hWz, hbad⟩ | ⟨_, hub, hbp⟩
      rotate_left 2
      · rcases h3 hq with h3 | h3
        · exact absurd ⟨hub, hbp⟩ h3
        obtain ⟨k, W, _, hu, hvk, hWz, hbad⟩ := hub
        have e : M.length - 2 = r := by omega
        rw [e] at hu hvk hbad
        exact common k W h3 hu hvk hWz hbad
      · exfalso
        have hxch : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
        apply hn (r + L) hxch
        refine ⟨fun h => ?_, fun h => ?_⟩
        · have : entry M 2 (r + L) = (bump M r).2.2 := by rw [← h]; rfl
          rw [hx2] at this; simp [bump] at this
        · rw [not_isUpg_e2z hx2] at h; cases h.1
      · -- `r = x − 1` lost its upgrade: `v′(r) = v(P_1 r) + 1`, whose components are below `Ω_{v′(r)}`
        exact common k W hi2 hu hvk hWz hbad
end


theorem qr_t1_D2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (I : Inv3V2 M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hL0 : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r))
    (hr : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    (hPR : PassRootRes M r L ρ)
    (hdrop : ∀ i, i < r + L → PO ρ (drop1 M (r + L) rk) i ∧ PV2 M ρ (drop1 M (r + L) rk) i)
    (hUAR : UAwRA M ρ (r + L)) (hr2 : r + 2 = M.length)
    (hcore : T1Core r ρ (M.take (r + L)) (drop1 M (r + L) rk)) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
      Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) rkN ∧
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
      (T1Core r ρ (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
        (FrameMapT1 M ρ r L (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
          VrDomQ M ρ r L (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN)) ∧
      isOT (root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN) = true ∧
      root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN < root M ρ := by
  have hcnt := hcnt_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
  exact qr_t1_D S I hlen hL0 hd0e hr hx2 hq hPR hdrop hUAR.toR hr2
    ⟨hcore, frameMapT1_takeG3 S I.cons I.good hC1 hRk1 hlen hx2 hdrop
      (fun k W hi hu hvk hWz => hUAR r k W hi hu hvk hWz) (fun _ => Or.inr hr2)⟩

end Ytosk
