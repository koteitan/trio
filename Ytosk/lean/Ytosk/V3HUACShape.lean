/-
HUAC from a structural/value shape only at dangerous absorbed summands.
All component bounds are derived from finite support and literal summand
survival; no decreasing-list invariant is required by the bridge.
-/
import Ytosk.V3HUACSupport

namespace Ytosk.HUACShapes
open T
open HUACSupport

/-- The two actual inputs of a row-2-zero vRhs. -/
def increment (M : Mat) (ρ : Valn) (m : Nat) : T :=
  match upg M m with
  | none => one
  | some t => last (ρ.v t)

/-- A genuinely dangerous absorption has a nonzero component at level zero. -/
def Danger (V W : T) : Prop :=
  ∃ q ∈ summands V, q < W ∧ ∃ g ∈ comps z q, g ≠ z

/-- First surviving bump child and its first child, with finite input support.
The two explicit summand memberships express survival and avoid relying on
an extra decreasing-list field absent from HUAC's input context. -/
def SupportWitness (M : Mat) (ρ : Valn) (n k m : Nat) : Prop :=
  ∃ L j R c C, children M k = L ++ j :: R ∧ col M j = bump M k ∧
    bumpTerm M ρ k j ∈ summands (sumN (one :: (children M k).map (bumpTerm M ρ k))) ∧
    (∀ d ∈ L, col M d = bump M k →
      bumpTerm M ρ k d ∉ summands (sumN (one :: (children M k).map (bumpTerm M ρ k)))) ∧
    children M j = c :: C ∧ ρ.o c ∈ summands (sumN ((children M j).map ρ.o)) ∧
    c < n ∧ Support (vOpt ρ (par M 1 m)) (ρ.v c) ∧ Support (increment M ρ m) (ρ.v c)

/-- The finite two-input support witness supplies HUAC's full component bound. -/
theorem dom_of_support_witness {M : Mat} {ρ : Valn} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {n k m : Nat}
    (hn : n < M.length) (hu : upg M n = some k) (hkn : k < n)
    (hkm : par M 0 k = some m) (hw : SupportWitness M ρ n k m) :
    ∀ u, Dom (comps u (vOpt ρ (par M 1 n))) (comps u (ρ.v n) ++ [z]) := by
  obtain ⟨L, j, R, c, C, hL, hjb, hBP, _, hCc, hoG, hcn, hparent, htail⟩ := hw
  have hc : c ∈ children M j := by rw [hCc]; simp
  have hcN := (mem_children hc).2
  have hmN : m < M.length := by have := par_lt M 0 k m hkm; omega
  obtain ⟨m', hm', hk0⟩ := upg_target_par0 S.r0p hu
  rw [hkm] at hk0; cases hk0
  obtain ⟨m'', hm'', _, hcol, _⟩ := upg_spec hu
  rw [hm'] at hm''; cases hm''
  have hm2 : entry M 2 m = 0 := by have := e2_of_col hcol; have := S.z2 k; omega
  have hsupport : Support (ρ.v m) (ρ.v c) :=
    support_value_of_inputs hC hG hmN hm2 hparent (fun t ht => by simpa only [increment, ht] using htail)
  obtain ⟨y, hy⟩ := o_psi_sub hC hcN
  rw [sf_ot (hG.ot_v c hcN)] at hy
  have hV_o : ∀ u, Dom (comps u (ρ.v m)) (comps u (ρ.o c) ++ [z]) := by
    rw [hy]
    exact dom_of_index_support (hG.ot_v c hcN) hsupport
  have ho_G : ∀ u, Dom (comps u (ρ.o c))
      (comps u (sumN ((children M j).map ρ.o)) ++ [z]) :=
    fun u g hg => ⟨g, List.mem_append_left _ (comps_summand_subH u hoG g hg), le_refl _⟩
  have hGot : isOT (sumN ((children M j).map ρ.o)) = true :=
    isOT_sumN _ (by intro q hq; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq; exact hG.ot_o d (mem_children hd).2)
  have hG_B : ∀ u, Dom (comps u (sumN ((children M j).map ρ.o)))
      (comps u (bumpTerm M ρ k j) ++ [z]) := by
    unfold bumpTerm
    rw [if_pos hjb]
    exact OmegaComps.dom_comps_omega hGot
  let P := sumN (one :: (children M k).map (bumpTerm M ρ k))
  have hB_P : ∀ u, Dom (comps u (bumpTerm M ρ k j)) (comps u P ++ [z]) :=
    fun u g hg => ⟨g, List.mem_append_left _ (comps_summand_subH u hBP g hg), le_refl _⟩
  have hP_W : ∀ u, Dom (comps u P) (comps u (bumpW M ρ k) ++ [z]) :=
    OmegaComps.dom_comps_omega (isOT_bumpP hG k)
  have hW_v : ∀ u, Dom (comps u (bumpW M ρ k)) (comps u (ρ.v n) ++ [z]) := by
    intro u g hg
    refine ⟨g, List.mem_append_left _ ?_, le_refl _⟩
    rw [value_at_target S hC hG hn hu]
    exact SumComps.mem_add_right hg
  rw [hm']
  simp only [vOpt]
  exact HUACPath.comp_dom_trans hV_o (HUACPath.comp_dom_trans ho_G
    (HUACPath.comp_dom_trans hG_B (HUACPath.comp_dom_trans hB_P (HUACPath.comp_dom_trans hP_W hW_v))))

/-- With no dangerous absorption, zero witnesses suffice at every level. -/
theorem dom_of_no_danger {M : Mat} {ρ : Valn} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {n k : Nat}
    (hn : n < M.length) (hu : upg M n = some k)
    (h : ¬ Danger (vOpt ρ (par M 1 n)) (bumpW M ρ k)) :
    ∀ u, Dom (comps u (vOpt ρ (par M 1 n))) (comps u (ρ.v n) ++ [z]) := by
  rw [value_at_target S hC hG hn hu]
  apply dom_add_of_absorbed (vOpt_ot hG hn)
  intro q hq hlt u g hg
  have hgz : g = z := by
    by_contra hg0
    exact h ⟨q, hq, hlt, g, comps_anti (z_le u) hg, hg0⟩
  exact ⟨z, List.mem_append_right _ (by simp), by simp [hgz]⟩

/-- At dangerous absorption only a zero head, a return copy, or a finite
support witness remains. Six measured full sets contain 228,257 dangerous
occurrences: 220,937 return copies, 1,108 zero heads, and 6,212 positive
support cases. Non-dangerous occurrences impose no shape obligation.
The statement is a residual, not a proof that these shapes always exist. -/
def HUACShape : Prop :=
  ∀ N σ rk, Std N → N ≠ SRO → Cons N σ → Rk N rk → Good3 N σ →
    ∀ n k m, upg N n = some k → k < n → par N 0 k = some m →
      Danger (vOpt σ (par N 1 n)) (bumpW N σ k) →
      lev (bumpW N σ k) = z ∨ HUACCopy.ReturnWitness N n k m ∨ SupportWitness N σ n k m

/-- All component domination follows from the shape and finite support inputs. -/
theorem hUAC_of (hS : HUACShape) : HUAC := by
  intro N σ rk hN hNe hC hR hG n k hu hkn
  have S := sInv_std hN hNe
  have hn : n < N.length := by have := upg_succ_lt hu; omega
  obtain ⟨m, _, hkm⟩ := upg_target_par0 S.r0p hu
  by_cases hd : Danger (vOpt σ (par N 1 n)) (bumpW N σ k)
  · rcases hS N σ rk hN hNe hC hR hG n k m hu hkn hkm hd with hzero | hw | hw
    · exact HUACZero.dom_of_zero S hC hG hn hu hzero
    · exact HUACCopy.dom_of_return S hC hG hn hu hkn hkm hw
    · exact dom_of_support_witness S hC hG hn hu hkn hkm hw
  · exact dom_of_no_danger S hC hG hn hu hd

end Ytosk.HUACShapes
