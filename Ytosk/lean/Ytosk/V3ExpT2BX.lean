/-
**3 行・t = 2: x より前の Good3（T2BelowX）を、変わる呼び出しの ◁ と標準形から組み立てる。**

`good_below_of`: D = DepS M S の外では値が M と同じ（hoff）、D の中（弱い呼び出し W を除く）では ◁ と標準形
（`deps_lhd_otW`）、種と弱い呼び出しの数える子の減少は仮定。このとき bnd より前のすべての列で
o・v は標準形で、数える子の値は減少する。
- D の中で v が変わる列は数える子がない（N でも）。
- D の中で o だけが変わる列は、数える子の並びが M と同じで、最後の子だけが ◁ で下がる。
- D の外の列は、数える子の並びも値も M と同じ。
-/
import Ytosk.V3DepOTW
import Ytosk.V3ExpT2CR

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- `cvals` as the values of the counted children, from the evaluation alone. -/
theorem cvals_eq_mapC {M : Mat} {ρ : Valn} (hC : Cons M ρ) (i : Nat) :
    cvals M ρ i = (CL M i).map ρ.o := by
  unfold cvals CL
  have : (children M i).map (cnt M ρ i) = (children M i).map (fun c => if Counted M i c then ρ.o c else z) := by
    apply List.map_congr_left; intro c _; exact cnt_eq_ite M ρ i c
  rw [this]
  apply nzs_map_ite
  intro c hc _
  obtain ⟨s, y, h⟩ := o_psi_form hC (mem_children hc).2
  rw [h]; simp

/-- **The shape of a frame of `N` against `M`**: the same, or the last counted child lowered by `◁`
(standard, with argument `0` if its `v` changed), or no counted child in either. -/
def FrameShape (M N : Mat) (ρ σ : Valn) (i : Nat) : Prop :=
  (σ.v i = ρ.v i ∧ CL N i = CL M i ∧ ∀ d ∈ CL M i, σ.o d = ρ.o d) ∨
  (σ.v i = ρ.v i ∧ ∃ Lc c, CL M i = Lc ++ [c] ∧ CL N i = Lc ++ [c] ∧ (∀ d ∈ Lc, σ.o d = ρ.o d) ∧
    Lhd z (σ.o c) (ρ.o c) ∧ isOT (σ.o c) = true ∧ (σ.v c ≠ ρ.v c → σ.o c = psi (σ.v c) z z)) ∨
  (CL N i = [] ∧ CL M i = [])

/-- **Good3 before `bnd`** from the agreement off `D`, the `◁` and standard form on `D`, and the seeds. -/
theorem good_below_of {M N : Mat} {S W : Bool → Nat → Prop} {bnd : Nat} {ρ σ : Valn}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hbM : bnd ≤ M.length) (hbN : bnd ≤ N.length)
    (hoff : ∀ i, i < bnd → (¬ DepS M S true i → σ.o i = ρ.o i) ∧ (¬ DepS M S false i → σ.v i = ρ.v i))
    (hD : ∀ b i, DepS M S b i → i < bnd → ¬ W b i →
      Lhd z (valB σ b i) (valB ρ b i) ∧ isOT (valB σ b i) = true)
    (hWv : ∀ i, ¬ W false i)
    (hWo : ∀ i c, c ∈ children M i → Counted M i c → W true c → S true i)
    (hWot : ∀ i, i < bnd → W true i → isOT (σ.o i) = true)
    (hSdec : ∀ i, i < bnd → (S true i ∨ W true i) → (cvals N σ i).Pairwise (fun a b => b ≤ a))
    (hDvCL : ∀ i, i < bnd → ¬ S true i → ¬ W true i → DepS M S false i → CL N i = [])
    (hDvCLM : ∀ i, i < bnd → ¬ S true i → ¬ W true i → DepS M S false i → CL M i = [])
    (hDvN : ∀ c, c < bnd → ¬ W true c → DepS M S false c → CL N c = [])
    (hOc : ∀ i, i < bnd → ¬ S true i → ¬ W true i → DepS M S true i → ¬ DepS M S false i →
      ∃ Lc c, CL M i = Lc ++ [c] ∧ CL N i = Lc ++ [c] ∧ DepS M S true c ∧ c < bnd ∧
        ∀ d ∈ Lc, ¬ DepS M S true d ∧ d < bnd)
    (hCLeq : ∀ i, i < bnd → ¬ S true i → ¬ W true i → ¬ DepS M S true i →
      CL N i = CL M i ∧ ∀ c ∈ CL M i, c < bnd)
    (hWb : ∀ i j c, entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → j ∈ children M i → col M j = bump M i →
      c ∈ children M j → W true c → S false i)
    (hVc : ∀ i, i < bnd → ¬ S false i → DepS M S false i →
      entry N 1 i = entry M 1 i ∧ entry N 2 i = entry M 2 i ∧ par N 1 i = par M 1 i ∧
      (∀ m, par M 1 i = some m → ¬ DepS M S false m) ∧ upg N i = upg M i ∧
      (∀ k, upg M i = some k → DepS M S false k → k < bnd) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ children N i = Lb ++ [j] ∧
        col M j = bump M i ∧ col N j = bump N i ∧ children M j = Kb ++ [k] ∧
        children N j = Kb ++ [k] ∧ k < bnd ∧ entry N 1 k = entry M 1 k ∧
        (∀ d ∈ Kb, ¬ DepS M S true d ∧ d < bnd) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M S true e) ∧
        (∀ d ∈ Lb, bumpTerm N σ i d = bumpTerm M ρ i d))) :
    ∀ i, i < bnd → isOT (σ.o i) = true ∧ isOT (σ.v i) = true ∧
      (cvals N σ i).Pairwise (fun a b => b ≤ a) ∧
      (¬ S true i → ¬ W true i → FrameShape M N ρ σ i) ∧ (¬ W true i → σ.o i ≤ ρ.o i) ∧
      (¬ S false i → DepS M S false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ children N i = Lb ++ [j] ∧ col M j = bump M i ∧
          col N j = bump N i ∧ children M j = Kb ++ [k] ∧ children N j = Kb ++ [k] ∧
          (∀ d ∈ Kb, σ.o d = ρ.o d) ∧ (∀ d ∈ Lb, bumpTerm N σ i d = bumpTerm M ρ i d) ∧
          (∀ d ∈ Lb, ∀ e ∈ children M d, e < bnd → σ.o e = ρ.o e) ∧
          Lhd z (σ.o k) (ρ.o k) ∧ isOT (σ.o k) = true) ∧
      (¬ DepS M S false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ j ∈ children M i, col M j = bump M i →
        ∀ k ∈ children M j, k < bnd → σ.o k = ρ.o k) := by
  intro i hi
  have hiM : i < M.length := by omega
  refine ⟨?_, ?_, ?_, fun hns hnw => ?_, fun hnw => ?_, fun hns hDv h1 h2 => ?_, fun hnd h1 h2 j hj hjb k hk hkb => ?_⟩
  · by_cases hd : DepS M S true i
    · by_cases hw : W true i
      · exact hWot i hi hw
      · exact (hD true i hd hi hw).2
    · rw [(hoff i hi).1 hd]; exact hG.ot_o i hiM
  · by_cases hd : DepS M S false i
    · exact (hD false i hd hi (hWv i)).2
    · rw [(hoff i hi).2 hd]; exact hG.ot_v i hiM
  · by_cases hs : S true i ∨ W true i
    · exact hSdec i hi hs
    have hns : ¬ S true i := fun h => hs (Or.inl h)
    have hnw : ¬ W true i := fun h => hs (Or.inr h)
    rw [cvals_eq_mapC hCN i]
    have hpM : ((CL M i).map ρ.o).Pairwise (fun a b => b ≤ a) := by
      rw [← cvals_eq_map hC hG i]; exact hG.dec i hiM
    by_cases hd : DepS M S true i
    · by_cases hv : DepS M S false i
      · rw [hDvCL i hi hns hnw hv]; simp
      · obtain ⟨Lc, c, hclM, hclN, hdc, hcb, hLc⟩ := hOc i hi hns hnw hd hv
        have hsame : ∀ d ∈ Lc, σ.o d = ρ.o d := fun d hd => (hoff d (hLc d hd).2).1 (hLc d hd).1
        have hWc : ¬ W true c := by
          intro hw
          have hcCL : c ∈ CL M i := by rw [hclM]; simp
          have hcnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
          exact hns (hWo i c (cl_mem_children hcCL) hcnt hw)
        have hlt := (hD true c hdc hcb hWc).1.1
        rw [hclM, List.map_append, List.map_singleton] at hpM
        rw [hclN, List.map_append, List.map_singleton, List.map_congr_left hsame]
        have hp1 := List.pairwise_append.mp hpM
        refine List.pairwise_append.mpr ⟨hp1.1, by simp, fun t ht b hb => ?_⟩
        simp at hb; rw [hb]
        exact le_trans (le_of_lt hlt) (hp1.2.2 t ht (ρ.o c) (List.mem_singleton_self _))
    · obtain ⟨hcl, hcb⟩ := hCLeq i hi hns hnw hd
      rw [hcl, List.map_congr_left (fun c hc => (hoff c (hcb c hc)).1 (fun hdc => hd (by
        have hcch := cl_mem_children hc
        have hcnt : Counted M i c := by unfold CL at hc; simpa using (List.mem_filter.mp hc).2
        exact DepS.ochild hcch hcnt.1 hcnt.2 hdc)))]
      exact hpM

  · by_cases hd : DepS M S true i
    · by_cases hv : DepS M S false i
      · exact Or.inr (Or.inr ⟨hDvCL i hi hns hnw hv, hDvCLM i hi hns hnw hv⟩)
      · obtain ⟨Lc, c, hclM, hclN, hdc, hcb, hLc⟩ := hOc i hi hns hnw hd hv
        have hWc : ¬ W true c := by
          intro hw
          have hcCL : c ∈ CL M i := by rw [hclM]; simp
          have hcnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
          exact hns (hWo i c (cl_mem_children hcCL) hcnt hw)
        obtain ⟨hl, hot⟩ := hD true c hdc hcb hWc
        refine Or.inr (Or.inl ⟨(hoff i hi).2 hv, Lc, c, hclM, hclN,
          fun d hd' => (hoff d (hLc d hd').2).1 (hLc d hd').1, hl, hot, fun hne => ?_⟩)
        have hdv : DepS M S false c := by by_contra h'; exact hne ((hoff c hcb).2 h')
        exact o_of_no_counted hCN (by omega) (hD false c hdv hcb (hWv c)).2
          (no_cnt_of_cl_nil (hDvN c hcb hWc hdv))
    · have hv : ¬ DepS M S false i := fun h => hd (DepS.ov h)
      obtain ⟨hcl, hcb⟩ := hCLeq i hi hns hnw hd
      refine Or.inl ⟨(hoff i hi).2 hv, hcl, fun c hc => (hoff c (hcb c hc)).1 (fun hdc => hd ?_)⟩
      have hcch := cl_mem_children hc
      have hcnt : Counted M i c := by unfold CL at hc; simpa using (List.mem_filter.mp hc).2
      exact DepS.ochild hcch hcnt.1 hcnt.2 hdc
  · by_cases hd : DepS M S true i
    · exact le_of_lt (hD true i hd hi hnw).1.1
    · rw [(hoff i hi).1 hd]
  · obtain ⟨_, _, _, hpnd, _, _, hbsh⟩ := hVc i hi hns hDv
    obtain ⟨Lb, Kb, j, k, hch, hchN, hjb, hjbN, hchj, hchjN, hkb, _, hKnd, hLnd, hbL⟩ := hbsh h2
    have hdk : DepS M S true k := by
      cases hDv with
      | seed h => exact absurd h hns
      | vpar _ hpm hdm => exact absurd hdm (hpnd _ hpm)
      | vupg _ h2' _ _ => exact absurd h2' h2
      | @vbump _ j0 k0 _ _ hj0 _ hk0 hdk0 =>
        have hjj : j0 = j := by
          rw [hch] at hj0
          rcases List.mem_append.mp hj0 with h | h
          · exact absurd hdk0 (hLnd j0 h k0 hk0)
          · exact List.mem_singleton.mp h
        subst hjj
        have hkk : k0 = k := by
          rw [hchj] at hk0
          rcases List.mem_append.mp hk0 with h | h
          · exact absurd hdk0 (hKnd k0 h).1
          · exact List.mem_singleton.mp h
        subst hkk
        exact hdk0
    have hj : j ∈ children M i := by rw [hch]; simp
    have hk : k ∈ children M j := by rw [hchj]; simp
    have hWk : ¬ W true k := fun hw => hns (hWb i j k h1 h2 hj hjb hk hw)
    obtain ⟨hl, hot⟩ := hD true k hdk hkb hWk
    exact ⟨Lb, Kb, j, k, hch, hchN, hjb, hjbN, hchj, hchjN,
      fun d hd => (hoff d (hKnd d hd).2).1 (hKnd d hd).1, hbL,
      fun d hd e he heb => (hoff e heb).1 (hLnd d hd e he), hl, hot⟩
  · exact (hoff k hkb).1 (fun hdk => hnd (DepS.vbump h1 h2 hj hjb hk hdk))

/-- **`N`-side hypothesis of `deps_lhd_ot`**: the subscript bound of a changed last child (`VSmallNew` form). -/
def T2VSN (N : Mat) (bnd : Nat) (ρ σ : Valn) : Prop :=
  ∀ i (Lc : List Nat) c, i < bnd → CL N i = Lc ++ [c] → σ.v c ≠ ρ.v c →
    ∀ g ∈ comps (ρ.v i) (σ.v c), g ≤ psi (σ.v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o))

/-- **`N`-side hypothesis of `deps_lhd_ot`**: the bound in the hard case (`HardArg` form). -/
def T2Hard (N : Mat) (bnd : Nat) (ρ σ : Valn) : Prop :=
  ∀ i (Lc : List Nat) c s y y', i < bnd → c < bnd → CL N i = Lc ++ [c] → ρ.o c = psi s y z →
    σ.o c = psi s y' z → lt (ρ.v i) s = true →
    (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y' = true ∧ lt (psi (ρ.v i) z z) (psi s y' z) = true) →
    (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) →
    (split y' (psi (succ s) z z)).1 < (split y (psi (succ s) z z)).1 →
    ∀ g ∈ comps (ρ.v i) y', g ≤ H s y'

end Ytosk