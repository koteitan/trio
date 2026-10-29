/-
Component certificates for the small increments of a row-1 value chain.
Unlike StepFacts3, these lemmas do not assert a lower bound for every target
having a bump child: even a leaf bump child can give a small increment.
There is no new global residual in this file.
-/
import Ytosk.WfStepFacts3

namespace Ytosk.HUACIncrement
open T WfHUACDeep WfStepFacts WfStepFacts3

/-- It suffices to certify absorbed base summands and small upgrade increments.
Large increments are kept, and increments equal to one have only zero components. -/
theorem chain_absorbed {M : Mat} {ρ : Valn} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {W : T} {a x : Nat}
    (hA : Up1 M a x) (hxN : x < M.length) (hx2 : entry M 2 x = 0)
    (hbase : ∀ q ∈ summands (ρ.v a), q < W →
      ∀ u, Dom (comps u q) (comps u W ++ [z]))
    (hinc : ∀ y t, Up1 M a y → Up1 M y x → y ≠ a → upg M y = some t →
      last (ρ.v t) < W → ∀ u, Dom (comps u (last (ρ.v t))) (comps u W ++ [z])) :
    ∀ q ∈ summands (ρ.v x), q < W →
      ∀ u, Dom (comps u q) (comps u W ++ [z]) := by
  induction hA with
  | refl => exact hbase
  | @step x y hp hA ih =>
    have hyx := par_lt M 1 x y hp
    have hy2 : entry M 2 y = 0 := by
      have := par1_e2_ne_one S.z1c hp
      have := S.z2 y
      omega
    have hay := up1_le hA
    have hxa : x ≠ a := by omega
    have h1 : entry M 1 x ≠ 0 := by have := par1_entry_lt hp; omega
    have hpOT := vOpt_ot hG hxN
    rw [hp] at hpOT
    simp only [vOpt] at hpOT
    have ihy := ih (by omega) hy2
      (fun y' t h1 h2 hne hu => hinc y' t h1 (Up1.step hp h2) hne hu)
    rw [(hC x hxN).2]
    unfold vRhs
    rw [if_neg h1, if_pos hx2, hp]
    simp only [vOpt]
    cases hu : upg M x with
    | none =>
      rw [sf_ot (isOT_add hpOT isOT_one)]
      intro q hq hqW
      rcases summands_add_gen _ _ q hq with hq | ⟨hq, _⟩
      · have : q = one := by simpa [one, summands] using hq
        subst q
        intro u g hg
        exact ⟨z, List.mem_append_right _ (by simp), by simp [comps_one_eq hg]⟩
      · exact ihy q hq hqW
    | some t =>
      rw [sf_ot (isOT_add hpOT (isOT_last (hG.ot_v t (upg_lt hxN hu))))]
      intro q hq hqW
      rcases summands_add_gen _ _ q hq with hq | ⟨hq, _⟩
      · rw [summands_last hq] at hqW ⊢
        exact hinc x t (Up1.step hp hA) (Up1.refl x) hxa hu hqW
      · exact ihy q hq hqW

/-- The old chain facts imply the small-increment certificate. The converse
is deliberately not asserted: the standard leaf-bump graft refutes it. -/
theorem small_increments_of_facts3 {M : Mat} {ρ : Valn} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {a m k : Nat} (hmN : m < M.length)
    (hF : ChainFacts3 M ρ k m a) :
    ∀ y t, Up1 M a y → Up1 M y m → y ≠ a → upg M y = some t →
      last (ρ.v t) < bumpW M ρ k →
      ∀ u, Dom (comps u (last (ρ.v t))) (comps u (ρ.v a) ++ [z]) := by
  intro y t hay hym hne hyt hlt
  by_cases hb : HasBump M t
  · exact False.elim ((not_lt.mpr (hF.1 y t hay hym hne hyt hb)) hlt)
  · have hyN : y < M.length := by have := up1_le hym; omega
    have hnb : ∀ d ∈ children M t, col M d ≠ bump M t := by
      intro d hd heq
      exact hb ⟨d, hd, heq⟩
    rw [last_v_noBump S hC hG hyN hyt hnb]
    intro u g hg
    obtain ⟨rfl, hg'⟩ := comps_om1 hg
    rcases hg' with rfl | rfl
    · obtain ⟨d, hd, hle⟩ := hF.2 ⟨y, t, hay, hym, hne, hyt, hb⟩
      exact ⟨d, List.mem_append_left _ hd, hle⟩
    · exact ⟨z, List.mem_append_right _ (by simp), le_refl _⟩

/-- The deep return certifies the base value. Only small increments remain;
their component certificates can pass through that same base value. -/
theorem dom_of_small_increments {M : Mat} {ρ : Valn} (S : SInv M)
    (hC : Cons M ρ) (hG : Good3 M ρ) {n k m : Nat}
    (hn : n < M.length) (hu : upg M n = some k) (hkn : k < n)
    (hkm : par M 0 k = some m) {L R : List Nat} {j c a : Nat}
    (hL : children M k = L ++ j :: R) (hjb : col M j = bump M k)
    (hR : ∀ d ∈ R, col M d = bump M k → children M d = [])
    (hc : c ∈ children M j) (hoG : ρ.o c ∈ summands (sumN ((children M j).map ρ.o)))
    (hcn : c < n) (hA : Up1 M a m) (h1 : entry M 1 c = entry M 1 a)
    (hc2 : entry M 2 c = 0)
    (hinc : ∀ y t, Up1 M a y → Up1 M y m → y ≠ a → upg M y = some t →
      last (ρ.v t) < bumpW M ρ k →
      ∀ u, Dom (comps u (last (ρ.v t))) (comps u (ρ.v a) ++ [z])) :
    ∀ u, Dom (comps u (vOpt ρ (par M 1 n))) (comps u (ρ.v n) ++ [z]) := by
  have hj : j ∈ children M k := by rw [hL]; simp
  have hcN := (mem_children hc).2
  obtain ⟨m', hm', hk0⟩ := upg_target_par0 S.r0p hu
  rw [hkm] at hk0; cases hk0
  have hmN : m < M.length := by
    have := par_lt M 0 k m hkm
    have := upg_lt hn hu
    omega
  have hm2 : entry M 2 m = 0 := by
    obtain ⟨m'', hm'', _, hcol, _⟩ := upg_spec hu
    rw [hm'] at hm''; cases hm''
    have := e2_of_col hcol; have := S.z2 k; omega
  have ha2 := up1_e2 S hA hm2
  have haN : a < M.length := by have := up1_le hA; omega
  obtain ⟨hp, hup⟩ := deep_return S hn hu hkn hkm hj hjb hc hcn hA h1 hc2 ha2
  have hv := value_eq_of_same_rhs hC hcN haN h1 hc2 ha2 hp hup
  have hvaW : ∀ u, Dom (comps u (ρ.v a)) (comps u (bumpW M ρ k) ++ [z]) := by
    rw [← hv]
    exact dom_vc_W hC hG hjb (WfStepFacts2.bp_dom_of_lastKid hG hL hR) hc hoG
  have hsmall := chain_absorbed S hC hG hA hmN hm2
    (fun q hq _ u g hg => hvaW u g (comps_summand_subH u hq g hg))
    (fun y t hya hym hne hyt hlt =>
      HUACPath.comp_dom_trans (hinc y t hya hym hne hyt hlt) hvaW)
  rw [HUACSupport.value_at_target S hC hG hn hu, hm']
  simp only [vOpt]
  exact HUACSupport.dom_add_of_absorbed (hG.ot_v m hmN) hsmall

end Ytosk.HUACIncrement
