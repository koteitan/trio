/-
**WfT2X2U: the below assembler with upgrade-shape bad columns and foreign-allowance frames.**
-/
import Ytosk.WfT2X2
import Ytosk.WfT2X1U
import Ytosk.V3AbsUpgFrame

namespace Ytosk.WfT2X
open T Classical Ytosk.WfAbsW
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

theorem not_bd_of_clU {M N : Mat} {ρ σ : Valn} {Bd : Nat → Prop} {i c : Nat} {Lc : List Nat}
    (hBdCL : ∀ i, Bd i → CL M i = [] ∧ CL N i = []) (hcl : CL M i = Lc ++ [c]) : ¬ Bd i := by
  intro hb
  obtain ⟨hclMi, _⟩ := hBdCL i hb
  rw [hclMi] at hcl; simp at hcl

theorem good_below_ofXU {M N : Mat} {S W : Bool → Nat → Prop} {Bd : Nat → Prop} {bnd : Nat} {ρ σ : Valn}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hbM : bnd ≤ M.length) (hbN : bnd ≤ N.length)
    (hoff : ∀ i, i < bnd → (¬ DepS M S true i → σ.o i = ρ.o i) ∧ (¬ DepS M S false i → σ.v i = ρ.v i))
    (hD : ∀ b i, DepS M S b i → i < bnd → ¬ W b i → PX M Bd ρ σ b i)
    (hBdUp : ∀ i k, upg M i = some k → Bd k → Bd i)
    (hBdF : ∀ i c, Bd c → c ∈ CL M i → CL M c = [] ∧ CL N c = [] ∧
      (par M 1 c = some i ∨ ∀ u, ∀ g ∈ comps u (vOpt ρ (par M 1 c)), g < σ.o c))
    (hBdCL : ∀ i, Bd i → CL M i = [] ∧ CL N i = [])
    (hBdK : ∀ i m p, Bd i → par M 0 i = some m → par M 0 m = some p → col M m ≠ bump M p)
    (hWv : ∀ i, ¬ W false i)
    (hWo : ∀ i c, c ∈ children M i → Counted M i c → W true c → S true i)
    (hWot : ∀ i, i < bnd → W true i → isOT (σ.o i) = true)
    (hSdec : ∀ i, i < bnd → (S true i ∨ W true i) → (cvals N σ i).Pairwise (fun a b => b ≤ a))
    (hDvCL : ∀ i, i < bnd → ¬ S true i → ¬ W true i → DepS M S false i → CL N i = [])
    (hDvCLM : ∀ i, i < bnd → ¬ S true i → ¬ W true i → DepS M S false i → CL M i = [])
    (hDvN : ∀ c, c < bnd → ¬ W true c → DepS M S false c → CL N c = [])
    (hDvM : ∀ c, c < bnd → ¬ W true c → DepS M S false c → σ.v c ≠ ρ.v c → CL M c = [])
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
      (¬ S true i → ¬ W true i → FrameShapeXU M N ρ σ i) ∧ (¬ W true i → σ.o i ≤ ρ.o i) ∧
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
        have hlt := (hD true c hdc hcb hWc).lt
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
      · exact Or.inl (Or.inl (Or.inr (Or.inr ⟨hDvCL i hi hns hnw hv, hDvCLM i hi hns hnw hv⟩)))
      · obtain ⟨Lc, c, hclM, hclN, hdc, hcb, hLc⟩ := hOc i hi hns hnw hd hv
        have hWc : ¬ W true c := by
          intro hw
          have hcCL : c ∈ CL M i := by rw [hclM]; simp
          have hcnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
          exact hns (hWo i c (cl_mem_children hcCL) hcnt hw)
        have hPc := hD true c hdc hcb hWc
        have hcCL : c ∈ CL M i := by rw [hclM]; simp
        have hcch := cl_mem_children hcCL
        have hcM : c < M.length := (mem_children hcch).2
        by_cases hBdc : Bd c
        · -- the fourth case: the last counted child is a bad column
          obtain ⟨hclMc, hclNc, hshape⟩ := hBdF i c hBdc hcCL
          have hoM : ρ.o c = psi (ρ.v c) z z :=
            o_of_no_counted hC hcM (hG.ot_v c hcM) (no_cnt_of_cl_nil hclMc)
          have hvc : σ.v c ≠ ρ.v c := by
            intro he
            have hvot : isOT (σ.v c) = true := by rw [he]; exact hG.ot_v c hcM
            have hoN : σ.o c = psi (σ.v c) z z :=
              o_of_no_counted hCN (by omega) hvot (no_cnt_of_cl_nil hclNc)
            have := hPc.lt; change σ.o c < ρ.o c at this
            rw [hoN, hoM, he] at this; exact lt_irrefl' _ this
          have hdv : DepS M S false c := by by_contra h'; exact hvc ((hoff c hcb).2 h')
          have hPv := hD false c hdv hcb (hWv c)
          have hoN : σ.o c = psi (σ.v c) z z :=
            o_of_no_counted hCN (by omega) hPv.2 (no_cnt_of_cl_nil hclNc)
          have hIHW : Lhd (vOpt ρ (par M 1 c)) (σ.o c) (ρ.o c) := by
            rcases hPc.1 with h | ⟨_, h⟩
            · exact lhd_mono_eta h
            · exact h
          have hVlV : Lhd (vOpt ρ (par M 1 c)) (σ.v c) (ρ.v c) := by
            rcases hPv.1 with h | ⟨_, h⟩
            · exact lhd_mono_eta h
            · exact h
          have hPi := (hD true i hd hi hnw).strong (not_bd_of_clU (ρ := ρ) (σ := σ) hBdCL hclM)
          change Lhd z (σ.o i) (ρ.o i) ∧ isOT (σ.o i) = true at hPi
          rcases hshape with hp1 | hsmS
          · have hVl : Lhd (ρ.v i) (σ.v c) (ρ.v c) := by
              rcases hPv.1 with h | ⟨_, h⟩
              · exact lhd_mono_eta h
              · change Lhd _ (σ.v c) (ρ.v c) at h; rw [hp1] at h; exact h
            have hOl : Lhd (ρ.v i) (σ.o c) (ρ.o c) := by
              change Lhd (vOpt ρ (par M 1 c)) _ _ at hIHW
              rw [hp1] at hIHW
              exact hIHW
            exact Or.inl (Or.inr ⟨(hoff i hi).2 hv, Lc, c, hclM, hclN,
              fun d hd' => (hoff d (hLc d hd').2).1 (hLc d hd').1, hoN, hoM, hVl, hOl, hPi.1⟩)
          · exact Or.inr ⟨(hoff i hi).2 hv, Lc, c, vOpt ρ (par M 1 c), hclM, hclN,
              fun d hd' => (hoff d (hLc d hd').2).1 (hLc d hd').1, hoN, hoM,
              hVlV, hIHW, hsmS, hPi.1⟩
        obtain ⟨hl, hot⟩ := hPc.strong hBdc
        refine Or.inl (Or.inl (Or.inr (Or.inl ⟨(hoff i hi).2 hv, Lc, c, hclM, hclN,
          fun d hd' => (hoff d (hLc d hd').2).1 (hLc d hd').1, hl, hot, fun hne => ?_, fun hne => ?_⟩)))
        · have hdv : DepS M S false c := by by_contra h'; exact hne ((hoff c hcb).2 h')
          exact o_of_no_counted hCN (by omega) (hD false c hdv hcb (hWv c)).2
            (no_cnt_of_cl_nil (hDvN c hcb hWc hdv))
        · have hdv : DepS M S false c := by by_contra h'; exact hne ((hoff c hcb).2 h')
          exact ⟨o_of_no_counted hC (by omega) (hG.ot_v c (by omega))
            (no_cnt_of_cl_nil (hDvM c hcb hWc hdv hne)), ((hD false c hdv hcb (hWv c)).strong hBdc).1⟩
    · have hv : ¬ DepS M S false i := fun h => hd (DepS.ov h)
      obtain ⟨hcl, hcb⟩ := hCLeq i hi hns hnw hd
      refine Or.inl (Or.inl (Or.inl ⟨(hoff i hi).2 hv, hcl, fun c hc => (hoff c (hcb c hc)).1 (fun hdc => hd ?_)⟩))
      have hcch := cl_mem_children hc
      have hcnt : Counted M i c := by unfold CL at hc; simpa using (List.mem_filter.mp hc).2
      exact DepS.ochild hcch hcnt.1 hcnt.2 hdc
  · by_cases hd : DepS M S true i
    · exact le_of_lt (hD true i hd hi hnw).lt
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
    have hBk : ¬ Bd k := fun hb =>
      hBdK k j i hb (mem_children_iff.mp hk).2 (mem_children_iff.mp hj).2 hjb
    obtain ⟨hl, hot⟩ := (hD true k hdk hkb hWk).strong hBk
    exact ⟨Lb, Kb, j, k, hch, hchN, hjb, hjbN, hchj, hchjN,
      fun d hd => (hoff d (hKnd d hd).2).1 (hKnd d hd).1, hbL,
      fun d hd e he heb => (hoff e heb).1 (hLnd d hd e he), hl, hot⟩
  · exact (hoff k hkb).1 (fun hdk => hnd (DepS.vbump h1 h2 hj hjb hk hdk))




theorem t2_assembleOTXU {M N : Mat} {S W : Bool → Nat → Prop} {Bd : Nat → Prop} {bnd p : Nat} {ρ σ : Valn}
    {rkM rkN : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hCN : Cons N σ) (hRN : Rk N rkN)
    (hF : FrameClosed M ρ) (hFO : FrameOT M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ)
    (hKD : BumpKidsDec M ρ)
    (hlenM : bnd + 1 = M.length) (hbN : bnd ≤ N.length)
    -- structural agreement before `bnd`
    (hchA : ∀ i, i < bnd → children N i = children M i)
    (hpS : S true p ∨ W true p) (hp2 : entry M 2 p = 0 ∨ S false p)
    (hpb : ∀ i, p ∈ children M i → col M p ≠ bump M i)
    (he : ∀ y i, i < bnd → entry N y i = entry M y i)
    (hpar1 : ∀ i, i < bnd → par N 1 i = par M 1 i)
    (hupg : ∀ i, i < bnd → ¬ S false i → upg N i = upg M i)
    (hcnt : ∀ i c, i < bnd → ¬ S true i → c ∈ children M i → c < bnd → (Counted N i c ↔ Counted M i c))
    (hxSW : ∀ i c, i < bnd → c ∈ children M i → bnd ≤ c → S true i ∨ W true i)
    (hupS : ∀ i k, i < bnd → upg M i = some k → bnd ≤ k → S false i)
    (hbjN : ∀ i j, i < bnd → j ∈ children N i → bnd ≤ j → col N j ≠ bump N i)
    (hbjS : ∀ i j, i < bnd → j ∈ children M i → bnd ≤ j → col M j = bump M i → S false i)
    (hbkS : ∀ i j k, i < bnd → j ∈ children M i → j < bnd → col M j = bump M i → k ∈ children M j →
      bnd ≤ k → S false i)
    -- the shape of `D` in `M`
    (hWD : ∀ i, W true i → DepS M S true i)
    (hWv : ∀ i, ¬ W false i)
    (hWo : ∀ i c, c ∈ children M i → Counted M i c → W true c → S true i)
    (hWb : ∀ i j c, entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → j ∈ children M i → col M j = bump M i →
      c ∈ children M j → W true c → S false i)
    (hDvNil : ∀ c, c < bnd → ¬ W true c → ¬ S true c → DepS M S false c → CL M c = [])
    (hDvNilS : ∀ c, c < bnd → ¬ W true c → S true c → DepS M S false c → CL N c = [])
    (hCLnil : ∀ c, c < bnd → ¬ W true c → CL M c = [] → CL N c = [])
    (hOS : ∀ i, i < bnd → ¬ S true i → ¬ W true i → DepS M S true i → ¬ DepS M S false i →
      ∃ L c R, children M i = L ++ c :: R ∧ Counted M i c ∧ DepS M S true c ∧
        (∀ d ∈ R, ¬ Counted M i d) ∧ (∀ d ∈ L, Counted M i d → ¬ DepS M S true d))
    (hVSh : ∀ i, i < bnd → ¬ S false i → DepS M S false i →
      (∀ m, par M 1 i = some m → ¬ DepS M S false m) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ col M j = bump M i ∧
        children M j = Kb ++ [k] ∧ (∀ d ∈ Kb, ¬ DepS M S true d) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M S true e)))
    -- values
    (hAbsX : ∀ i, i < bnd → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → AbsAt M N ρ σ i ∨ Bd i)
    (hBdUp : ∀ i k, upg M i = some k → Bd k → Bd i)
    (hBdF : ∀ i c, Bd c → c ∈ CL M i → CL M c = [] ∧ CL N c = [] ∧
      (par M 1 c = some i ∨ ∀ u, ∀ g ∈ comps u (vOpt ρ (par M 1 c)), g < σ.o c))
    (hBdCL : ∀ i, Bd i → CL M i = [] ∧ CL N i = [])
    (hBdK : ∀ i m p, Bd i → par M 0 i = some m → par M 0 m = some p → col M m ≠ bump M p)
    (hSeed : ∀ b i, S b i → i < bnd → DepS M S b i →
      (∀ i, i < bnd → (¬ DepS M S true i → σ.o i = ρ.o i) ∧ (¬ DepS M S false i → σ.v i = ρ.v i)) →
      (∀ b' i', rkM b' i' < rkM b i → DepS M S b' i' → i' < bnd → ¬ W b' i' → PX M Bd ρ σ b' i') →
      Lhd z (valB σ b i) (valB ρ b i) ∧ isOT (valB σ b i) = true)
    {sd : Nat} (hHA : T2HardA M N bnd sd ρ σ) (hSp : ∀ i, S true i → i = sd)
    (hOTout : ∀ b j, bnd ≤ j → j < N.length → isOT (valB σ b j) = true)
    (hWot : (∀ i, i < bnd → (¬ DepS M S true i → σ.o i = ρ.o i) ∧ (¬ DepS M S false i → σ.v i = ρ.v i)) →
      ∀ i, i < bnd → W true i → isOT (σ.o i) = true)
    (hSdec : (∀ i, i < bnd → (¬ DepS M S true i → σ.o i = ρ.o i) ∧ (¬ DepS M S false i → σ.v i = ρ.v i)) →
      ∀ i, i < bnd → (S true i ∨ W true i) → (cvals N σ i).Pairwise (fun a b => b ≤ a)) :
    ∀ i, i < bnd → isOT (σ.o i) = true ∧ isOT (σ.v i) = true ∧
      (cvals N σ i).Pairwise (fun a b => b ≤ a) ∧
      (¬ S true i → ¬ W true i → FrameShapeXU M N ρ σ i) ∧ (¬ W true i → σ.o i ≤ ρ.o i) ∧
      (¬ S false i → DepS M S false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ children N i = Lb ++ [j] ∧ col M j = bump M i ∧
          col N j = bump N i ∧ children M j = Kb ++ [k] ∧ children N j = Kb ++ [k] ∧
          (∀ d ∈ Kb, σ.o d = ρ.o d) ∧ (∀ d ∈ Lb, bumpTerm N σ i d = bumpTerm M ρ i d) ∧
          (∀ d ∈ Lb, ∀ e ∈ children M d, e < bnd → σ.o e = ρ.o e) ∧
          Lhd z (σ.o k) (ρ.o k) ∧ isOT (σ.o k) = true) ∧
      (¬ DepS M S false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ j ∈ children M i, col M j = bump M i →
        ∀ k ∈ children M j, k < bnd → σ.o k = ρ.o k) := by
  have hch : ∀ i, i < bnd → i ≠ p → children N i = children M i := fun i hi _ => hchA i hi
  have hcol : ∀ i, i < bnd → col N i = col M i := fun i hi => by
    rw [col_eq_entries, col_eq_entries, he 0 i hi, he 1 i hi, he 2 i hi]
  have hbump : ∀ i, i < bnd → bump N i = bump M i := fun i hi => by
    unfold bump; rw [he 0 i hi, he 1 i hi]
  have hoff := t2_off_gen (S := S) hC hCN hRN (by omega) hbN hch
    (by rcases hpS with h | h; exact DepS.seed h; exact hWD p h)
    (by rcases hp2 with h | h; exact Or.inl h; exact Or.inr (DepS.seed h)) hpb he hpar1
    (fun i hi hd => hupg i hi (fun hs => hd (DepS.seed hs)))
    (fun i c hi hd hc hcx => hcnt i c hi (fun hs => hd (DepS.seed hs)) hc hcx)
    (fun i c hi hc hcx => by
      rcases hxSW i c hi hc hcx with h | h
      · exact DepS.seed h
      · exact hWD i h)
    (fun i k hi hk hkx => DepS.seed (hupS i k hi hk hkx)) hbjN
    (fun i j hi hj hjx hjb => DepS.seed (hbjS i j hi hj hjx hjb))
    (fun i j k hi hj hjx hjb hk hkx => DepS.seed (hbkS i j k hi hj hjx hjb hk hkx))
  have hupgK : ∀ i k, i < bnd → upg M i = some k → ∀ j ∈ children N k, col N j = bump N k →
      ∀ k' ∈ children N j, k' < bnd → j ∈ children M k ∧ col M j = bump M k ∧ k' ∈ children M j := by
    intro i k hi hk j hj hjb k' hk' hk'b
    rcases Nat.lt_or_ge k bnd with hkb | hkb
    · have hjM : j ∈ children M k := by rw [← hchA k hkb]; exact hj
      have hjb' : j < bnd := by
        by_contra h'
        exact hbjN k j hkb hj (by omega) hjb
      refine ⟨hjM, by rw [← hcol j hjb', ← hbump k hkb]; exact hjb, ?_⟩
      rw [← hchA j hjb']; exact hk'
    · exfalso
      have := (mem_children hj).1
      have := (mem_children hk').1
      omega
  have hVc : ∀ i, i < bnd → ¬ S false i → DepS M S false i →
      entry N 1 i = entry M 1 i ∧ entry N 2 i = entry M 2 i ∧ par N 1 i = par M 1 i ∧
      (∀ m, par M 1 i = some m → ¬ DepS M S false m) ∧ upg N i = upg M i ∧
      (∀ k, upg M i = some k → DepS M S false k → k < bnd) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ children N i = Lb ++ [j] ∧
        col M j = bump M i ∧ col N j = bump N i ∧ children M j = Kb ++ [k] ∧
        children N j = Kb ++ [k] ∧ k < bnd ∧ entry N 1 k = entry M 1 k ∧
        (∀ d ∈ Kb, ¬ DepS M S true d ∧ d < bnd) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M S true e) ∧
        (∀ d ∈ Lb, bumpTerm N σ i d = bumpTerm M ρ i d)) := by
    intro i hi hns hD
    obtain ⟨hpnd, hbsh⟩ := hVSh i hi hns hD
    refine ⟨he 1 i hi, he 2 i hi, hpar1 i hi, hpnd, hupg i hi hns, fun k hk _ => ?_, fun h2 => ?_⟩
    · by_contra h'
      exact hns (hupS i k hi hk (by omega))
    · obtain ⟨Lb, Kb, j, k, hchi, hjb, hchj, hKnd, hLnd⟩ := hbsh h2
      have hj : j ∈ children M i := by rw [hchi]; simp
      have hjx : j < bnd := by
        by_contra h'; exact hns (hbjS i j hi hj (by omega) hjb)
      have hk : k ∈ children M j := by rw [hchj]; simp
      have hkx : k < bnd := by
        by_contra h'; exact hns (hbkS i j k hi hj hjx hjb hk (by omega))
      have hKk : ∀ d ∈ Kb, d < k := (sib_order (children_sorted M j) (R := []) (by rw [hchj])).1
      have hLj : ∀ d ∈ Lb, d < j := (sib_order (children_sorted M i) (R := []) (by rw [hchi])).1
      have hip : i ≠ p := by
        rintro rfl; rcases hp2 with h | h; exact h2 h; exact hns h
      refine ⟨Lb, Kb, j, k, hchi, by rw [hch i hi hip, hchi], hjb,
        by rw [hcol j hjx, hbump i hi]; exact hjb, hchj,
        by rw [hch j hjx (by rintro rfl; exact hpb i hj hjb), hchj], hkx, he 1 k hkx,
        fun d hd => ⟨hKnd d hd, by have := hKk d hd; omega⟩, hLnd, fun d hd => ?_⟩
      have hdj := hLj d hd
      have hdM : d ∈ children M i := by rw [hchi]; simp [hd]
      apply bumpTerm_eq_of
      · rw [hcol d (by omega), hbump i hi]
      · intro hdb
        rw [hch d (by omega) (by rintro rfl; exact hpb i hdM hdb)]
        apply List.map_congr_left
        intro e he'
        have hex : e < bnd := by
          by_contra h'; exact hns (hbkS i d e hi hdM (by omega) hdb he' (by omega))
        exact (hoff e hex).1 (hLnd d hd e he')
  have hdlR := deps_lhd_otXU (S := S) (W := W) (Bd := Bd) (bnd := bnd) hC hG hCN hRM (by omega) hbN
    hF hFO hVS hTD hKD (hHA.sv S hSp) (hHA.1.1.toS S bnd) hHA.1.2.1 hoff hOTout hWv hWo hWb (hWot hoff)
    (fun b i hs hi hd ih => hSeed b i hs hi hd hoff ih) (hHA.seed S hSp) (hHA.re S hSp) hDvNil
    (fun c hc hw hd => by
      by_cases hs : S true c
      · exact hDvNilS c hc hw hs hd
      · exact hCLnil c hc hw (hDvNil c hc hw hs hd)) hCLnil
    (by
      intro i hi hns hnw hD hv
      obtain ⟨Lp, c, R, hch', hcnt', hdc, hR, hL⟩ := hOS i hi hns hnw hD hv
      have hcM : c ∈ children M i := by rw [hch']; simp
      have hall : ∀ d ∈ children M i, d < bnd := by
        intro d hd
        by_contra h'
        rcases hxSW i d hi hd (by omega) with h | h
        · exact hns h
        · exact hnw h
      have hclM : CL M i = Lp.filter (fun d => decide (Counted M i d)) ++ [c] := by
        unfold CL
        rw [hch', List.filter_append, List.filter_cons, if_pos (by simpa using hcnt')]
        have : R.filter (fun d => decide (Counted M i d)) = [] := by
          rw [List.filter_eq_nil_iff]; intro d hd; simpa using hR d hd
        rw [this]
      have hclN : CL N i = CL M i := by
        unfold CL
        rw [hch i hi (by rintro rfl; rcases hpS with h | h; exact hns h; exact hnw h)]
        apply List.filter_congr
        intro d hd
        simp only [hcnt i d hi hns hd (hall d hd)]
      refine ⟨_, c, hclM, by rw [hclN, hclM], hdc, hall c hcM, fun d hd => ?_⟩
      have hd' := List.mem_filter.mp hd
      have hdM : d ∈ children M i := by rw [hch']; simp [hd'.1]
      exact ⟨hL d hd'.1 (by simpa using hd'.2), hall d hdM⟩)
    hVc
    hupgK hAbsX hBdUp hBdF hBdK
  have hdl : ∀ b i, DepS M S b i → i < bnd → ¬ W b i → PX M Bd ρ σ b i :=
    fun b i hD hi hW => (hdlR b i hD hi hW).1
  apply good_below_ofXU hC hG hCN (by omega) hbN hoff hdl hBdUp hBdF hBdCL hBdK hWv hWo (hWot hoff) (hSdec hoff)
  · intro i hi hns hnw hv
    exact hCLnil i hi hnw (hDvNil i hi hnw hns hv)
  · intro i hi hns hnw hv
    exact hDvNil i hi hnw hns hv
  · intro c hc hw hd
    by_cases hs : S true c
    · exact hDvNilS c hc hw hs hd
    · exact hCLnil c hc hw (hDvNil c hc hw hs hd)
  · intro c hc hw hd hne
    by_cases hs : S true c
    · exact absurd (hHA.sv S hSp c hs) hne
    · exact hDvNil c hc hw hs hd
  · intro i hi hns hnw hD hv
    obtain ⟨Lp, c, R, hch', hcnt', hdc, hR, hL⟩ := hOS i hi hns hnw hD hv
    have hall : ∀ d ∈ children M i, d < bnd := by
      intro d hd
      by_contra h'
      rcases hxSW i d hi hd (by omega) with h | h
      · exact hns h
      · exact hnw h
    have hcM : c ∈ children M i := by rw [hch']; simp
    have hclM : CL M i = Lp.filter (fun d => decide (Counted M i d)) ++ [c] := by
      unfold CL
      rw [hch', List.filter_append, List.filter_cons, if_pos (by simpa using hcnt')]
      have : R.filter (fun d => decide (Counted M i d)) = [] := by
        rw [List.filter_eq_nil_iff]; intro d hd; simpa using hR d hd
      rw [this]
    have hclN : CL N i = CL M i := by
      unfold CL
      rw [hchA i hi]
      apply List.filter_congr
      intro d hd
      simp only [hcnt i d hi hns hd (hall d hd)]
    refine ⟨_, c, hclM, by rw [hclN, hclM], hdc, hall c hcM, fun d hd => ?_⟩
    have hd' := List.mem_filter.mp hd
    have hdM : d ∈ children M i := by rw [hch']; simp [hd'.1]
    exact ⟨hL d hd'.1 (by simpa using hd'.2), hall d hdM⟩
  · intro i hi hns hnw hnd
    have hall : ∀ d ∈ children M i, d < bnd := by
      intro d hd
      by_contra h'
      rcases hxSW i d hi hd (by omega) with h | h
      · exact hns h
      · exact hnw h
    refine ⟨?_, fun c hc => hall c (cl_mem_children hc)⟩
    unfold CL
    rw [hchA i hi]
    apply List.filter_congr
    intro d hd
    simp only [hcnt i d hi hns hd (hall d hd)]
  · exact hWb
  · exact hVc

end Ytosk.WfT2X
