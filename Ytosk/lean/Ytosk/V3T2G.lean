/-
**3 行・t = 2: 一般形の組み立て。**

行列 M（最後の列 x = bnd）と N（位置 bnd より前は M と同じ構造）、種 S と弱い呼び出し W について、
構造の一致・D = DepS M S の形（M だけの事実）・種の ◁ を仮定にして、N の根の和が標準形で M より小さい
（`t2_assemble`）。D の外の値が同じこと（`t2_off_gen`）は `cons_agree` で示す。
q = r（x − 1 が x へ上げる場合）と q ≠ r で使う。
-/
import Ytosk.V3T2M

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **Outside `D`, `N` has the values of `M` before `bnd`** (general form). -/
theorem t2_off_gen {M N : Mat} {S : Bool → Nat → Prop} {bnd p : Nat} {ρ σ : Valn}
    {rkN : Bool → Nat → Nat} (hC : Cons M ρ) (hCN : Cons N σ) (hRN : Rk N rkN)
    (hbM : bnd < M.length) (hbN : bnd ≤ N.length)
    (hch : ∀ i, i < bnd → i ≠ p → children N i = children M i)
    (hpD : DepS M S true p) (hpV : entry M 2 p = 0 ∨ DepS M S false p)
    (hpb : ∀ i, p ∈ children M i → col M p ≠ bump M i)
    (he : ∀ y i, i < bnd → entry N y i = entry M y i)
    (hpar1 : ∀ i, i < bnd → par N 1 i = par M 1 i)
    (hupg : ∀ i, i < bnd → ¬ DepS M S false i → upg N i = upg M i)
    (hcnt : ∀ i c, i < bnd → ¬ DepS M S true i → c ∈ children M i → c < bnd →
      (Counted N i c ↔ Counted M i c))
    (hxD : ∀ i c, i < bnd → c ∈ children M i → bnd ≤ c → DepS M S true i)
    (hupD : ∀ i k, i < bnd → upg M i = some k → bnd ≤ k → DepS M S false i)
    (hbjN : ∀ i j, i < bnd → j ∈ children N i → bnd ≤ j → col N j ≠ bump N i)
    (hbjD : ∀ i j, i < bnd → j ∈ children M i → bnd ≤ j → col M j = bump M i → DepS M S false i)
    (hbkD : ∀ i j k, i < bnd → j ∈ children M i → j < bnd → col M j = bump M i → k ∈ children M j →
      bnd ≤ k → DepS M S false i) :
    ∀ i, i < bnd → (¬ DepS M S true i → σ.o i = ρ.o i) ∧ (¬ DepS M S false i → σ.v i = ρ.v i) := by
  set D := DepS M S with hD
  have hcol : ∀ i, i < bnd → col N i = col M i := fun i hi => by
    rw [col_eq_entries, col_eq_entries, he 0 i hi, he 1 i hi, he 2 i hi]
  have hbump : ∀ i, i < bnd → bump N i = bump M i := fun i hi => by
    unfold bump; rw [he 0 i hi, he 1 i hi]
  have key := cons_agree (τ := ρ) (fun b i => bnd ≤ i ∨ D b i) hCN hRN
  have hres := key (by
    intro i hi hE
    simp only [not_or] at hE
    have hix : i < bnd := by omega
    rw [(hC i (by omega)).1]
    unfold oRhs
    rw [hch i hix (by rintro rfl; exact hE.2 hpD)]
    congr 3
    apply List.map_congr_left
    intro c hc
    have hcx : c < bnd := by
      by_contra h'; exact hE.2 (hxD i c hix hc (by omega))
    exact (cnt_eq_of (hcnt i c hix hE.2 hc hcx) rfl).symm) (by
    intro i hi hE
    simp only [not_or] at hE
    have hix : i < bnd := by omega
    rw [(hC i (by omega)).2]
    symm
    apply vRhs_eq_of (he 1 i hix) (he 2 i hix)
    · intro _; rw [hpar1 i hix]
    · intro _ _; rw [hupg i hix hE.2]
    · intro _ h2
      have hip : i ≠ p := by
        rintro rfl
        rcases hpV with h | h
        · exact h2 h
        · exact hE.2 h
      rw [hch i hix hip]
      congr 2
      apply List.map_congr_left
      intro j hj
      apply bumpTerm_eq_of
      · rcases Nat.lt_or_ge j bnd with h | h
        · rw [hcol j h, hbump i hix]
        · exact ⟨fun h' => absurd h' (hbjN i j hix (by rw [hch i hix hip]; exact hj) h),
            fun h' => absurd (hbjD i j hix hj h h') hE.2⟩
      · intro hjb
        have hjx : j < bnd := by
          by_contra h'; exact hE.2 (hbjD i j hix hj (by omega) hjb)
        have hchj := hch j hjx (by rintro rfl; exact hpb i hj hjb)
        rw [hchj]) (by
    intro i hi hE
    simp only [not_or] at hE
    have hix : i < bnd := by omega
    refine ⟨fun h => ?_, fun c hc hcnt' h => ?_⟩
    · rcases h with h | h
      · omega
      · exact hE.2 (DepS.ov h)
    · rw [hch i hix (by rintro rfl; exact hE.2 hpD)] at hc
      have hcx : c < bnd := by
        by_contra h'; exact hE.2 (hxD i c hix hc (by omega))
      rcases h with h | h
      · omega
      · have hcM := (hcnt i c hix hE.2 hc hcx).mp hcnt'
        exact hE.2 (DepS.ochild hc hcM.1 hcM.2 h)) (by
    intro i hi hE he1
    simp only [not_or] at hE
    have hix : i < bnd := by omega
    rw [he 1 i hix] at he1
    refine ⟨fun m hm h => ?_, fun he2 k hk h => ?_, fun he2 j hj hjb k hk h => ?_⟩
    · rw [hpar1 i hix] at hm
      rcases h with h | h
      · have := par_lt M 1 i m hm; omega
      · exact hE.2 (DepS.vpar he1 hm h)
    · rw [he 2 i hix] at he2
      rw [hupg i hix hE.2] at hk
      have hkx : k < bnd := by
        by_contra h'; exact hE.2 (hupD i k hix hk (by omega))
      rcases h with h | h
      · omega
      · exact hE.2 (DepS.vupg he1 he2 hk h)
    · rw [he 2 i hix] at he2
      have hjN := hj
      have hip : i ≠ p := by
        rintro rfl
        rcases hpV with h | h
        · exact he2 h
        · exact hE.2 h
      rw [hch i hix hip] at hj
      have hjx : j < bnd := by
        by_contra h'; exact hbjN i j hix hjN (by omega) hjb
      rw [hcol j hjx, hbump i hix] at hjb
      rw [hch j hjx (by rintro rfl; exact hpb i hj hjb)] at hk
      have hkx : k < bnd := by
        by_contra h'; exact hE.2 (hbkD i j k hix hj hjx hjb hk (by omega))
      rcases h with h | h
      · omega
      · exact hE.2 (DepS.vbump he1 he2 hj hjb hk h))
  intro i hi
  have h := hres i (by omega)
  exact ⟨fun hd => h.1 (by rintro (h' | h'); omega; exact hd h'),
    fun hd => h.2 (by rintro (h' | h'); omega; exact hd h')⟩

/-- **The root value** when the roots are before `bnd` in both (general form). -/
theorem root_gen {M N : Mat} {bnd : Nat} (hlenM : bnd + 1 = M.length) (hbN : bnd ≤ N.length)
    (hcolN : ∀ i, i < bnd → col N i = col M i)
    (hposN : ∀ j, bnd ≤ j → j < N.length → entry N 0 j ≠ 0) (hposM : entry M 0 bnd ≠ 0)
    (hR01 : R01 M) (hR12 : R12 M) (h00 : entry M 0 0 = 0)
    {ρ σ : Valn} (hG : Good3 M ρ) (hGN : Good3 N σ)
    (hle : ∀ i, i < bnd → σ.o i ≤ ρ.o i)
    (hstrict : ∀ R, R < bnd → Anc0 M R bnd → col M R = (0, 0, 0) → σ.o R < ρ.o R) :
    isOT (root N σ) = true ∧ root N σ < root M ρ := by
  classical
  have hcol0 : ∀ {N : Mat} {i : Nat}, entry N 0 i ≠ 0 → col N i ≠ (0, 0, 0) := by
    intro N i h hc
    rw [col_eq_entries] at hc
    simp only [Prod.mk.injEq] at hc
    exact h hc.1
  set f' : Nat → T := fun i => if col M i = (0, 0, 0) then σ.o i else z with hf'
  set f : Nat → T := fun i => if col M i = (0, 0, 0) then ρ.o i else z with hf
  have hot' : ∀ i, i < bnd → isOT (f' i) = true := by
    intro i hi; simp only [hf']; split
    · exact hGN.ot_o i (by omega)
    · rfl
  have hot : ∀ i, i < bnd → isOT (f i) = true := by
    intro i hi; simp only [hf]; split
    · exact hG.ot_o i (by omega)
    · rfl
  have hrootN : root N σ = sumN ((List.range bnd).map f') := by
    unfold root
    rw [show N.length = bnd + (N.length - bnd) by omega, List.range_add, List.map_append]
    have hz : ∀ t ∈ (List.map (fun x => bnd + x) (List.range (N.length - bnd))).map
        (fun i => if col N i = (0, 0, 0) then σ.o i else z), t = z := by
      intro t ht
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
      have hk' := List.mem_range.mp hk
      rw [if_neg (hcol0 (hposN (bnd + k) (by omega) (by omega)))]
    rw [sumN_append_zeros (fun t ht => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      have hir := List.mem_range.mp hi
      split
      · exact hGN.ot_o i (by omega)
      · rfl) _ hz]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [hcolN i (List.mem_range.mp hi)]
  have hrootM : root M ρ = sumN ((List.range bnd).map f) := by
    unfold root
    rw [← hlenM, List.range_succ, List.map_append, List.map_singleton]
    rw [if_neg (hcol0 hposM), sumN_snoc_z (fun t ht => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      have hir := List.mem_range.mp hi
      split
      · exact hG.ot_o i (by omega)
      · rfl)]
  rw [hrootN, hrootM]
  refine ⟨isOT_sumN _ (fun t ht => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht; exact hot' i (List.mem_range.mp hi)), ?_⟩
  obtain ⟨R, hRA, hR0c, hRl⟩ := root_t1 hR01 hR12 h00 bnd
  have he0R : entry M 0 R = 0 := by rw [col_eq_entries] at hR0c; simp only [Prod.mk.injEq] at hR0c; exact hR0c.1
  have hRx : R < bnd := by
    by_contra h
    have : R = bnd := by have := hRA.le; omega
    rw [this] at he0R; exact hposM he0R
  apply sumN_range_lt f' f bnd hRx hot' hot
  · intro i hi; simp only [hf', hf]; split
    · exact hle i hi
    · exact le_refl _
  · simp only [hf', hf]; rw [if_pos hR0c, if_pos hR0c]; exact hstrict R hRx hRA hR0c
  · intro i h1 h2
    have hn' := hcol0 (hRl i h1 (by omega))
    simp only [hf', hf]; exact ⟨if_neg hn', if_neg hn'⟩

/-- **`t = 2` assembly** (general form): from the structural agreement before `bnd`, the shape of
`D = DepS M S` in `M`, the weak calls `W` read only by seeds, and the seeds, the root value of `N` is
standard and below that of `M`. -/
theorem t2_assemble {M N : Mat} {S W : Bool → Nat → Prop} {bnd p : Nat} {ρ σ : Valn}
    {rkM rkN : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hCN : Cons N σ) (hGN : Good3 N σ) (hRN : Rk N rkN)
    (hF : FrameClosed M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    (hR01 : R01 M) (hR12 : R12 M) (h00 : entry M 0 0 = 0)
    (hlenM : bnd + 1 = M.length) (hbN : bnd ≤ N.length)
    -- structural agreement before `bnd` (the children may differ only at `p`)
    (hch : ∀ i, i < bnd → i ≠ p → children N i = children M i)
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
    (hposN : ∀ j, bnd ≤ j → j < N.length → entry N 0 j ≠ 0) (hposM : entry M 0 bnd ≠ 0)
    -- the shape of `D` in `M`
    (hWD : ∀ i, W true i → DepS M S true i)
    (hWv : ∀ i, ¬ W false i)
    (hWo : ∀ i c, c ∈ children M i → Counted M i c → W true c → S true i)
    (hWb : ∀ i j c, entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → j ∈ children M i → col M j = bump M i →
      c ∈ children M j → W true c → S false i)
    (hDvNil : ∀ c, c < bnd → ¬ W true c → DepS M S false c → CL M c = [])
    (hCLnil : ∀ c, c < bnd → ¬ W true c → CL M c = [] → CL N c = [])
    (hOS : ∀ i, i < bnd → ¬ S true i → ¬ W true i → DepS M S true i → ¬ DepS M S false i →
      ∃ L c R, children M i = L ++ c :: R ∧ Counted M i c ∧ DepS M S true c ∧
        (∀ d ∈ R, ¬ Counted M i d) ∧ (∀ d ∈ L, Counted M i d → ¬ DepS M S true d))
    (hVSh : ∀ i, i < bnd → ¬ S false i → DepS M S false i →
      (∀ m, par M 1 i = some m → ¬ DepS M S false m) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ col M j = bump M i ∧
        children M j = Kb ++ [k] ∧ (∀ d ∈ Kb, ¬ DepS M S true d) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M S true e)))
    (hRD : ∀ R, R < bnd → Anc0 M R bnd → col M R = (0, 0, 0) → DepS M S true R ∧ ¬ W true R)
    (hWle : ∀ i, i < bnd → W true i → σ.o i ≤ ρ.o i)
    -- values
    (hAbs : ∀ i, i < bnd → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ q ∈ summands (vOpt ρ (par M 1 i)),
      ¬ q < psi z two z → q < bumpW M ρ i → Lhd z q (bumpW M ρ i))
    (hVNN : ∀ i, i < bnd → ∀ (Lc : List Nat) (cs : Nat), CL M i = Lc ++ [cs] → σ.v cs ≠ ρ.v cs →
      ∀ s y, ρ.o cs = psi s y z →
        lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true →
        VSmallV (σ.v cs))
    (hSeed : ∀ b i, S b i → i < bnd → DepS M S b i →
      (∀ i, i < bnd → (¬ DepS M S true i → σ.o i = ρ.o i) ∧ (¬ DepS M S false i → σ.v i = ρ.v i)) →
      (∀ b' i', rkM b' i' < rkM b i → DepS M S b' i' → i' < bnd → ¬ W b' i' →
        Lhd z (valB σ b' i') (valB ρ b' i')) →
      Lhd z (valB σ b i) (valB ρ b i)) :
    isOT (root N σ) = true ∧ root N σ < root M ρ := by
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
  have hdl := deps_lhd_genW (S := S) (W := W) (bnd := bnd) hC hG hCN hGN hRM (by omega) hbN
    hF hVS hTD hKD hoff hWv hWo hWb (fun b i hs hi hd ih => hSeed b i hs hi hd hoff ih) hDvNil hCLnil
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
    hVNN
    (by
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
          exact (hoff e hex).1 (hLnd d hd e he'))
    hAbs
  apply root_gen hlenM hbN hcol hposN hposM hR01 hR12 h00 hG hGN
  · intro i hi
    by_cases hd : DepS M S true i
    · by_cases hw : W true i
      · exact hWle i hi hw
      · exact le_of_lt (hdl true i hd hi hw).1
    · rw [(hoff i hi).1 hd]
  · intro R hR hRA hR0
    obtain ⟨hDR, hWR⟩ := hRD R hR hRA hR0
    exact (hdl true R hDR hR hWR).1

end Ytosk
