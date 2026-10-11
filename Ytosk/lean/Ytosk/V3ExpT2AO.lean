/-
**3 行・t = 2: `t2_assemble` の、Good3 N を仮定しない版（`t2_assembleOT`）。**

構造の一致・D の形・種（◁ と標準形）・弱い呼び出しの標準形・種と弱い呼び出しの数える子の減少から、
bnd より前の o・v の標準形と数える子の減少を出す（`deps_lhd_otW` と `good_below_of`）。
-/
import Ytosk.V3T2G
import Ytosk.V3ExpT2BX

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- **`t2_assemble` without `Good3 N`**: Good3 before `bnd`. -/
theorem t2_assembleOT {M N : Mat} {S W : Bool → Nat → Prop} {bnd p : Nat} {ρ σ : Valn}
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
    (hAbs : AbsWN M N bnd ρ σ)
    (hSeed : ∀ b i, S b i → i < bnd → DepS M S b i →
      (∀ i, i < bnd → (¬ DepS M S true i → σ.o i = ρ.o i) ∧ (¬ DepS M S false i → σ.v i = ρ.v i)) →
      (∀ b' i', rkM b' i' < rkM b i → DepS M S b' i' → i' < bnd → ¬ W b' i' →
        Lhd z (valB σ b' i') (valB ρ b' i') ∧ isOT (valB σ b' i') = true) →
      Lhd z (valB σ b i) (valB ρ b i) ∧ isOT (valB σ b i) = true)
    (hVSN : T2VSN N bnd ρ σ) (hHard : T2Hard N bnd ρ σ)
    (hOTout : ∀ b j, bnd ≤ j → j < N.length → isOT (valB σ b j) = true)
    (hWot : (∀ i, i < bnd → (¬ DepS M S true i → σ.o i = ρ.o i) ∧ (¬ DepS M S false i → σ.v i = ρ.v i)) →
      ∀ i, i < bnd → W true i → isOT (σ.o i) = true)
    (hSdec : (∀ i, i < bnd → (¬ DepS M S true i → σ.o i = ρ.o i) ∧ (¬ DepS M S false i → σ.v i = ρ.v i)) →
      ∀ i, i < bnd → (S true i ∨ W true i) → (cvals N σ i).Pairwise (fun a b => b ≤ a)) :
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
  have hdl := deps_lhd_otW (S := S) (W := W) (bnd := bnd) hC hG hCN hRM (by omega) hbN
    hF hFO hVS hTD hKD hVSN hHard hoff hOTout hWv hWo hWb (hWot hoff)
    (fun b i hs hi hd ih => hSeed b i hs hi hd hoff ih) hDvNil
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
    hupgK hAbs
  apply good_below_of hC hG hCN (by omega) hbN hoff hdl hWv hWo (hWot hoff) (hSdec hoff)
  · intro i hi hns hnw hv
    exact hCLnil i hi hnw (hDvNil i hi hnw hns hv)
  · intro i hi hns hnw hv
    exact hDvNil i hi hnw hns hv
  · intro c hc hw hd
    by_cases hs : S true c
    · exact hDvNilS c hc hw hs hd
    · exact hCLnil c hc hw (hDvNil c hc hw hs hd)
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

end Ytosk
