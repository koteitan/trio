/-
**3 行・t = 2・q = r（主の場合）: x より前の Good3（Good3 N を仮定しない）。**

`t2_qr_main`（V3T2M）の構造の部分をそのまま使い、`deps_lhd_gen` を `deps_lhd_ot` に替え、`good_below_of` で
x より前の o・v の標準形と数える子の減少を出す。残りは N 側の 2 つ（`T2VSN`・`T2Hard`）、x 以後の標準形、
種 o(r) の ◁・標準形・数える子の減少。
-/
import Ytosk.V3T2M
import Ytosk.V3ExpT2BX

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn2 : 2 ≤ n)
  (hXu : ∀ i, upg M i ≠ some (r + L)) (hXb : col M (r + L) ≠ bump M r)
  (hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p)
  (he2r : entry M 2 r = 0)
  (hIU : ∀ c, c < r + L → topped M c = true → isUpg (TRIO.gexp M r L d0 d1 n) c = isUpg M c)
include hlen hL hp hd0e hn2 hXu hXb hrb he2r hIU

/-- **`t = 2`, `q = r`, the main case: Good3 of `M[n]` before `x`.** -/
theorem t2_qr_below (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M)
    (hUAB : UAB M) (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    {ρ σ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    {rkN : Bool → Nat → Nat} (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ)
    (hRN : Rk (TRIO.gexp M r L d0 d1 n) rkN)
    (hF : FrameClosed M ρ) (hFO : FrameOT M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ)
    (hKD : BumpKidsDec M ρ)
    (hAbsC : BumpAbsS M (r + L) ρ)
    (hxcN : Counted (TRIO.gexp M r L d0 d1 n) r (r + L))
    (hVSN : T2VSN (TRIO.gexp M r L d0 d1 n) (r + L) ρ σ)
    (hHard : T2Hard (TRIO.gexp M r L d0 d1 n) (r + L) ρ σ)
    (hOTout : ∀ b j, r + L ≤ j → j < (TRIO.gexp M r L d0 d1 n).length → isOT (valB σ b j) = true)
    (hseed : Lhd z (σ.o r) (ρ.o r) ∧ isOT (σ.o r) = true)
    (hsdec : (cvals (TRIO.gexp M r L d0 d1 n) σ r).Pairwise (fun a b => b ≤ a)) :
    ∀ i, i < r + L → isOT (σ.o i) = true ∧ isOT (σ.v i) = true ∧
      (cvals (TRIO.gexp M r L d0 d1 n) σ i).Pairwise (fun a b => b ≤ a) ∧
      (i ≠ r → FrameShape M (TRIO.gexp M r L d0 d1 n) ρ σ i) ∧ σ.o i ≤ ρ.o i ∧
      (DepS M ((fun b i => b = true ∧ i = r)) false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ children (TRIO.gexp M r L d0 d1 n) i = Lb ++ [j] ∧
          col M j = bump M i ∧ col (TRIO.gexp M r L d0 d1 n) j = bump (TRIO.gexp M r L d0 d1 n) i ∧
          children M j = Kb ++ [k] ∧ children (TRIO.gexp M r L d0 d1 n) j = Kb ++ [k] ∧
          (∀ d ∈ Kb, σ.o d = ρ.o d) ∧
          (∀ d ∈ Lb, bumpTerm (TRIO.gexp M r L d0 d1 n) σ i d = bumpTerm M ρ i d) ∧
          (∀ d ∈ Lb, ∀ e ∈ children M d, e < r + L → σ.o e = ρ.o e) ∧
          Lhd z (σ.o k) (ρ.o k) ∧ isOT (σ.o k) = true) ∧
      (¬ DepS M ((fun b i => b = true ∧ i = r)) false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        ∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, k < r + L → σ.o k = ρ.o k) := by
  set N := TRIO.gexp M r L d0 d1 n with hN
  set S : Bool → Nat → Prop := fun b i => b = true ∧ i = r with hS
  have hXbD : ∀ p, par M 0 (r + L) = some p → col M (r + L) ≠ bump M p := by
    intro p h'; rw [hp] at h'; cases h'; exact hXb
  have hx : r + L + 1 = M.length := hlen
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn2
  have hoff := t2_off hlen hL hp hd0e hn2 hXu hXb hrb he2r hIU hC hCN hRN
  have hiff : ∀ b i, i < r + L → (DepS M S b i ↔ DepX M (r + L) b i) :=
    fun b i hi => depS_iff_depX hlen hL hp hXu hXb hrb hi
  have hbumpN : ∀ i, i < r + L → bump N i = bump M i := fun i hi => by
    unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hi, entry_gexp_pre hlen (by omega) 1 hi]
  have hcl := fun i hi => CL_N2 hlen hL hp hd0e hn2 hXu hXb he2r hIU hxcN (i := i) hi
  have hupgN : ∀ i, i < r + L → upg N i = upg M i := by
    intro i hi
    rcases Nat.lt_or_ge (i + 1) (r + L) with h | h
    · exact upg_N2_pre hlen hL hp hd0e hn2 hXu hXb he2r h
    · have : i = r + L - 1 := by omega
      rw [this]; exact upg_N2_xm1 hlen hL hp hd0e (by omega) hn2 he2r (hXu _)
  have hDvNil : ∀ c, c < r + L → DepS M S false c → CL M c = [] := by
      intro c hc hd
      unfold CL; rw [List.filter_eq_nil_iff]
      intro d hdc
      simp only [decide_eq_true_eq]
      exact uncnt_of_depvX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXbD hp hc
        ((hiff false c hc).mp hd) hdc
  have hCLnil : ∀ c, c < r + L → CL M c = [] → CL N c = [] := by
    intro c hc h; rw [hcl c hc]; exact h
  have hOc : ∀ i, i < r + L → ¬ S true i → DepS M S true i → ¬ DepS M S false i →
      ∃ Lc c, CL M i = Lc ++ [c] ∧ CL N i = Lc ++ [c] ∧ DepS M S true c ∧ c < r + L ∧
        ∀ d ∈ Lc, ¬ DepS M S true d ∧ d < r + L := by
      intro i hi hns hD hv
      have hir : i ≠ r := fun h => hns ⟨rfl, h⟩
      rcases hOS_t1X hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXbD hp i hi ((hiff true i hi).mp hD) with
        ⟨hvX, _⟩ | ⟨_, Lp, c0, R, hch, hcb0, hcu0, hR, hLnd⟩
      · exact absurd ((hiff false i hi).mpr hvX) hv
      · cases hD with
        | seed h => exact absurd h hns
        | ov h => exact absurd h hv
        | @ochild _ c hc hcb hcu hdc =>
          have hcnt : Counted M i c := ⟨hcb, hcu⟩
          have hcR : ∀ d ∈ R, ¬ Counted M i d := fun d h hd => by
            rcases hR d h with h' | h'
            · exact hd.1 h'
            · exact hd.2 h'
          have hcl' := (mem_children hc).2
          have hcx : c < r + L := by
            by_contra h'
            have : c = r + L := by omega
            have hpc := (mem_children_iff.mp hc).2
            rw [this, hp] at hpc; cases hpc; exact hir rfl
          have hcc0 : c = c0 := by
            have hc' := hc
            rw [hch] at hc'
            rcases List.mem_append.mp hc' with h | h
            · exact absurd ((hiff true c hcx).mp hdc) (hLnd c h hcnt)
            · rcases List.mem_cons.mp h with h | h
              · exact h
              · exact absurd hcnt (hcR c h)
          rw [← hcc0] at hch
          obtain ⟨hLs, _⟩ := sib_order (children_sorted M i) hch
          have hclM : CL M i = Lp.filter (fun d => decide (Counted M i d)) ++ [c] := by
            unfold CL
            rw [hch, List.filter_append, List.filter_cons, if_pos (by simpa using hcnt)]
            have : R.filter (fun d => decide (Counted M i d)) = [] := by
              rw [List.filter_eq_nil_iff]; intro d hd; simpa using hcR d hd
            rw [this]
          refine ⟨_, c, hclM, by rw [hcl i hi, hclM], hdc, hcx, fun d hd => ?_⟩
          have hd' := List.mem_filter.mp hd
          have hdc' : Counted M i d := by simpa using hd'.2
          have := hLs d hd'.1
          exact ⟨fun h => hLnd d hd'.1 hdc' ((hiff true d (by omega)).mp h), by omega⟩
  have hVc : ∀ i, i < r + L → ¬ S false i → DepS M S false i →
      entry N 1 i = entry M 1 i ∧ entry N 2 i = entry M 2 i ∧ par N 1 i = par M 1 i ∧
      (∀ m, par M 1 i = some m → ¬ DepS M S false m) ∧ upg N i = upg M i ∧
      (∀ k, upg M i = some k → DepS M S false k → k < r + L) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ children N i = Lb ++ [j] ∧
        col M j = bump M i ∧ col N j = bump N i ∧ children M j = Kb ++ [k] ∧
        children N j = Kb ++ [k] ∧ k < r + L ∧ entry N 1 k = entry M 1 k ∧
        (∀ d ∈ Kb, ¬ DepS M S true d ∧ d < r + L) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M S true e) ∧
        (∀ d ∈ Lb, bumpTerm N σ i d = bumpTerm M ρ i d)) := by
      intro i hi _ hD
      have hDX := (hiff false i hi).mp hD
      obtain ⟨he1, hpnd, hcase⟩ := dv_shapeX hx hR0 hZ2 hSD hZ1 hUAT hUAB hXu hXbD hp hi hDX
      refine ⟨entry_gexp_pre hlen (by omega) 1 hi, entry_gexp_pre hlen (by omega) 2 hi,
        par_gexp_pre hlen (by omega) 1 hi,
        fun m hm h => hpnd m hm ((hiff false m (by have := par_lt M 1 i m hm; omega)).mp h),
        hupgN i hi, fun k hk _ => ?_, fun h2 => ?_⟩
      · have hkl := upg_lt (by omega) hk
        have hkx : k ≠ r + L := fun h' => hXu i (h' ▸ hk)
        omega
      · rcases hcase with ⟨h2', _⟩ | ⟨_, Lb, Kb, j, k, hch, hjb, hchj, hdk, hKnd, hLnd⟩
        · exact absurd h2' h2
        · have hj : j ∈ children M i := by rw [hch]; simp
          have hjl := (mem_children hj).2
          have hjx : j < r + L := by
            by_contra h'
            have : j = r + L := by omega
            have h' := (mem_children_iff.mp hj).2; rw [this, hp] at h'; cases h'
            rw [this] at hjb; exact hXb hjb
          have hk : k ∈ children M j := by rw [hchj]; simp
          have hkl := (mem_children hk).2
          have hkx : k < r + L := by
            by_contra h'
            have : k = r + L := by omega
            have hpk := (mem_children_iff.mp hk).2
            rw [this, hp] at hpk; cases hpk
            exact hrb i (mem_children_iff.mp hj).2 hjb
          have hKk : ∀ d ∈ Kb, d < k := (sib_order (children_sorted M j) (R := []) (by rw [hchj])).1
          have hLj : ∀ d ∈ Lb, d < j := (sib_order (children_sorted M i) (R := []) (by rw [hch])).1
          refine ⟨Lb, Kb, j, k, hch, by rw [children_N2 hlen hL hp hd0e (by omega) hn2 hi, hch], hjb,
            by rw [col_gexp_pre hlen (by omega) hjx, hbumpN i hi]; exact hjb, hchj,
            by rw [children_N2 hlen hL hp hd0e (by omega) hn2 hjx, hchj], hkx,
            entry_gexp_pre hlen (by omega) 1 hkx,
            fun d hd => ⟨fun h => hKnd d hd ((hiff true d (by have := hKk d hd; omega)).mp h),
              by have := hKk d hd; omega⟩,
            fun d hd e he h => (hLnd d hd e he).2 ((hiff true e (hLnd d hd e he).1).mp h),
            fun d hd => ?_⟩
          have hdj := hLj d hd
          apply bumpTerm_eq_of
          · rw [col_gexp_pre hlen (by omega) (by omega), hbumpN i hi]
          · intro _
            rw [children_N2 hlen hL hp hd0e (by omega) hn2 (by omega)]
            apply List.map_congr_left
            intro e he
            have hex := (hLnd d hd e he).1
            exact (hoff e hex).1 (fun h => (hLnd d hd e he).2 ((hiff true e hex).mp h))
  have hAbs : ∀ i, i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ q ∈ summands (vOpt ρ (par M 1 i)),
      ¬ q < psi z two z → q < bumpW M ρ i → Lhd z q (bumpW M ρ i) := by
      intro i hi h1 h2
      refine hAbsC i h1 h2 (fun j hj hjb hjx => ?_) (Or.inr (Or.inl fun q' i' hq' hi' => ?_))
      · exfalso
        have hxj : r + L ∈ children M j := by rw [hjx]; simp
        have hpx := (mem_children_iff.mp hxj).2
        rw [hp] at hpx; cases hpx
        exact hrb i (mem_children_iff.mp hj).2 hjb
      · rw [hp] at hq'; cases hq'; exact hrb i' hi'
  have hxnbN : ∀ i, col N (r + L) ≠ bump N i := by
    intro i h'
    have : entry N 2 (r + L) = (col N (r + L)).2.2 := rfl
    rw [h', (entry_xprime hlen hL hp hd0e (by omega) hn2).1, he2r] at this; simp [bump] at this
  have hupgK : ∀ i k, i < r + L → upg M i = some k → ∀ j ∈ children N k, col N j = bump N k →
      ∀ k' ∈ children N j, k' < r + L → j ∈ children M k ∧ col M j = bump M k ∧ k' ∈ children M j := by
    intro i k hi hk j hj hjb k' hk' _
    have hkx : k < r + L := by
      have := upg_le hk
      have hkx : k ≠ r + L := fun h' => hXu i (h' ▸ hk)
      omega
    have hjM : j ∈ children M k := by rw [← children_N2 hlen hL hp hd0e (by omega) hn2 hkx]; exact hj
    have hjx : j < r + L := by
      have := (mem_children hjM).2
      rcases Nat.lt_or_ge j (r + L) with h | h
      · exact h
      · exfalso; rw [show j = r + L by omega] at hjb; exact hxnbN k hjb
    refine ⟨hjM, by rw [← col_gexp_pre (d0 := d0) (d1 := d1) (m := n) hlen (by omega) hjx, ← hbumpN k hkx]; exact hjb, ?_⟩
    rw [← children_N2 hlen hL hp hd0e (by omega) hn2 hjx]; exact hk'
  have hdl := deps_lhd_otW (S := S) (W := fun _ _ => False) (bnd := r + L) hC hG hCN hRM (by omega)
    (by rw [hlN]; omega)
    hF hFO hVS hTD hKD hVSN hHard hoff hOTout (fun _ h => h)
    (fun _ _ _ _ h => h.elim) (fun _ _ _ _ _ _ _ _ h => h.elim) (fun _ _ h => h.elim)
    (by
      rintro b i ⟨hb, hi'⟩ _ _ _
      subst hb
      rw [hi']
      exact hseed)
    (fun c hc _ _ hv => hDvNil c hc hv) (fun c hc _ hv => hCLnil c hc (hDvNil c hc hv))
    (fun c hc _ h => hCLnil c hc h) (fun i hi hns _ hD hv => hOc i hi hns hD hv) hVc hupgK hAbs
  have hgb := good_below_of (W := fun _ _ => False) hC hG hCN (by omega) (by rw [hlN]; omega) hoff
    (fun b i hd hi hw => hdl b i hd hi hw) (fun _ h => h) (fun _ _ _ _ h => h.elim) (fun _ _ h => h.elim)
    (by
      intro i hi hs
      rcases hs with ⟨_, rfl⟩ | h
      · exact hsdec
      · exact h.elim)
    (fun i hi _ _ hv => hCLnil i hi (hDvNil i hi hv))
    (fun i hi _ _ hv => hDvNil i hi hv)
    (fun c hc _ hv => hCLnil c hc (hDvNil c hc hv))
    (fun i hi hns _ hD hv => hOc i hi hns hD hv)
    (by
      intro i hi hns _ hnd
      refine ⟨hcl i hi, fun c hc => ?_⟩
      have hcch := cl_mem_children hc
      have hcl' := (mem_children hcch).2
      by_contra h'
      have hcx : c = r + L := by omega
      have hpc := (mem_children_iff.mp hcch).2
      rw [hcx, hp] at hpc; cases hpc
      exact hns ⟨rfl, rfl⟩)
    (fun _ _ _ _ _ _ _ _ h => h.elim) hVc
  intro i hi
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hgb i hi
  exact ⟨h1, h2, h3, fun hir => h4 (fun h => hir h.2) (fun h => h), h5 (fun h => h),
    h6 (fun h => absurd h.1 (by simp)), h7⟩

end

end Ytosk
