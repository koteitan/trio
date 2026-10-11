/-
**3 行・t = 2・q = r で x − 1 が x へ上げる場合: x より前の Good3（Good3 N を仮定しない）。**

`t2_sv_main`（V3T2V）を `t2_assembleOT` に替えた写し。種 v(x − 1) の標準形は V + 1（P_1 の値は D の外）。
-/
import Ytosk.V3T2V
import Ytosk.V3ExpT2AO

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

section
variable {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn2 : 2 ≤ n)
  (hu : upg M (r + L - 1) = some (r + L))
include hlen hL hp hd0e hn2 hu

/-- **`t = 2`, `q = r`, `x − 1` upgrades to `x`: Good3 of `M[n]` before `x`.** -/
theorem t2_sv_below (hBE : BumpE2 M) (hZ2 : Z2 M) (hUAT : UAT M) (hR12 : R12 M) (hR01 : R01 M)
    (h00 : entry M 0 0 = 0) (he2r : entry M 2 r = 0)
    (hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p) (hrCL : CL M r ≠ [])
    (hIUt : ∀ c, c < r + L → topped M c = true → isUpg (TRIO.gexp M r L d0 d1 n) c = isUpg M c)
    -- the shape of `D` in `M`
    (hP1 : ∀ m, par M 1 (r + L - 1) = some m → ¬ DepS M (SV r (r + L - 1)) false m)
    (hDvNil : ∀ c, c < r + L → DepS M (SV r (r + L - 1)) false c → CL M c = [])
    (hOS : ∀ i, i < r + L → ¬ SV r (r + L - 1) true i →
      DepS M (SV r (r + L - 1)) true i → ¬ DepS M (SV r (r + L - 1)) false i →
      ∃ Lp c R, children M i = Lp ++ c :: R ∧ Counted M i c ∧ DepS M (SV r (r + L - 1)) true c ∧
        (∀ d ∈ R, ¬ Counted M i d) ∧ (∀ d ∈ Lp, Counted M i d → ¬ DepS M (SV r (r + L - 1)) true d))
    (hVSh : ∀ i, i < r + L → ¬ SV r (r + L - 1) false i → DepS M (SV r (r + L - 1)) false i →
      (∀ m, par M 1 i = some m → ¬ DepS M (SV r (r + L - 1)) false m) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ col M j = bump M i ∧
        children M j = Kb ++ [k] ∧ (∀ d ∈ Kb, ¬ DepS M (SV r (r + L - 1)) true d) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M (SV r (r + L - 1)) true e)))
    -- values
    {ρ σ : Valn} {rkM rkN : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ) (hRN : Rk (TRIO.gexp M r L d0 d1 n) rkN)
    (hF : FrameClosed M ρ) (hFO : FrameOT M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ)
    (hKD : BumpKidsDec M ρ)
    (hAbs : ∀ i, i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ q ∈ summands (vOpt ρ (par M 1 i)),
      ¬ q < psi z two z → q < bumpW M ρ i → Lhd z q (bumpW M ρ i))
    (hVSN : T2VSN (TRIO.gexp M r L d0 d1 n) (r + L) ρ σ)
    (hHard : T2Hard (TRIO.gexp M r L d0 d1 n) (r + L) ρ σ)
    (hOTout : ∀ b j, r + L ≤ j → j < (TRIO.gexp M r L d0 d1 n).length → isOT (valB σ b j) = true)
    (hseed : Lhd z (σ.o r) (ρ.o r) ∧ isOT (σ.o r) = true)
    (hsdec : (cvals (TRIO.gexp M r L d0 d1 n) σ r).Pairwise (fun a b => b ≤ a)) :
    ∀ i, i < r + L → isOT (σ.o i) = true ∧ isOT (σ.v i) = true ∧
      (cvals (TRIO.gexp M r L d0 d1 n) σ i).Pairwise (fun a b => b ≤ a) := by
  have hlN : (TRIO.gexp M r L d0 d1 n).length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn2
  have hA : Anc0 M r (r + L) := anc0_of_par M 0 r (r + L) hp
  have hxr := col_x_ne_bump_r hp hu
  have hcolN : ∀ i, i < r + L → col (TRIO.gexp M r L d0 d1 n) i = col M i := fun i hi => col_gexp_pre hlen (by omega) hi
  have hbumpN : ∀ i, i < r + L → bump (TRIO.gexp M r L d0 d1 n) i = bump M i := fun i hi => by
    unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hi, entry_gexp_pre hlen (by omega) 1 hi]
  have hchN : ∀ i, i < r + L → children (TRIO.gexp M r L d0 d1 n) i = children M i :=
    fun i hi => children_N2 hlen hL hp hd0e (by omega) hn2 hi
  have hxN2 : entry (TRIO.gexp M r L d0 d1 n) 2 (r + L) = 0 := by
    rw [(entry_xprime hlen hL hp hd0e (by omega) hn2).1, he2r]
  have hcnt : ∀ i c, i < r + L → c < r + L → (Counted (TRIO.gexp M r L d0 d1 n) i c ↔ Counted M i c) := by
    intro i c hi hc
    unfold Counted
    rw [hcolN c hc, hbumpN i hi, topped_NV hlen hL hp hd0e hn2 hxr he2r hc]
    by_cases ht : topped M c = true
    · rw [hIUt c hc ht]
    · simp [ht]
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hp] at h'; exact (Option.some.inj h').symm
  have hCLnil : ∀ c, c < r + L → ¬ (fun _ _ => False : Bool → Nat → Prop) true c → CL M c = [] →
      CL (TRIO.gexp M r L d0 d1 n) c = [] := by
    intro c hc _ hcl
    by_cases hcr : c = r
    · exact (hrCL (by rw [← hcr]; exact hcl)).elim
    · unfold CL at hcl ⊢
      rw [hchN c hc, ← hcl]
      apply List.filter_congr
      intro d hd
      have hdx : d < r + L := by
        have := (mem_children hd).2
        by_contra h'
        exact hcr (hxc c d hd (by omega)).2
      simp only [hcnt c d hc hdx]
  have hSeed : ∀ b i, SV r (r + L - 1) b i → i < r + L → DepS M (SV r (r + L - 1)) b i →
      (∀ i, i < r + L → (¬ DepS M (SV r (r + L - 1)) true i → σ.o i = ρ.o i) ∧
        (¬ DepS M (SV r (r + L - 1)) false i → σ.v i = ρ.v i)) →
      (∀ b' i', rkM b' i' < rkM b i → DepS M (SV r (r + L - 1)) b' i' → i' < r + L →
        ¬ (fun _ _ => False : Bool → Nat → Prop) b' i' →
        Lhd z (valB σ b' i') (valB ρ b' i') ∧ isOT (valB σ b' i') = true) →
      Lhd z (valB σ b i) (valB ρ b i) ∧ isOT (valB σ b i) = true := by
    rintro b i (⟨hb, hi'⟩ | ⟨hb, hi'⟩) _ _ hoff _
    · subst hb; rw [hi']
      exact hseed
    · subst hb; rw [hi']
      have hV : vOpt σ (par (TRIO.gexp M r L d0 d1 n) 1 (r + L - 1)) = vOpt ρ (par M 1 (r + L - 1)) := by
        rw [par_gexp_pre hlen (by omega) 1 (by omega)]
        cases hm : par M 1 (r + L - 1) with
        | none => rfl
        | some m =>
          show σ.v m = ρ.v m
          exact (hoff m (by have := par_lt M 1 _ m hm; omega)).2 (hP1 m hm)
      refine ⟨v_xm1_lhd hlen hL hn2 hu hZ2 he2r hC hG hCN hV (upgN_xm1_none hlen hL hp hd0e hn2 hu he2r), ?_⟩
      show isOT (σ.v (r + L - 1)) = true
      obtain ⟨he1, he2⟩ := upg_e12 hu
      have he2z : entry M 2 (r + L - 1) = 0 := by have := hZ2 (r + L - 1); omega
      have hVot : isOT (vOpt ρ (par M 1 (r + L - 1))) = true := by
        cases hm : par M 1 (r + L - 1) with
        | none => rfl
        | some m => exact hG.ot_v m (by have := par_lt M 1 _ m hm; omega)
      rw [(hCN (r + L - 1) (by rw [hlN]; omega)).2]
      unfold vRhs
      rw [entry_gexp_pre hlen (by omega) 1 (by omega), entry_gexp_pre hlen (by omega) 2 (by omega),
        if_neg he1, if_pos he2z, upgN_xm1_none hlen hL hp hd0e hn2 hu he2r, hV]
      show isOT (sf (add (vOpt ρ (par M 1 (r + L - 1))) one)) = true
      rw [sf_ot (isOT_add hVot rfl)]
      exact isOT_add hVot rfl
  exact t2_assembleOT (S := SV r (r + L - 1)) (W := fun _ _ => False) (bnd := r + L) hC hG hRM hCN hRN
    hF hFO hVS hTD hKD hlen (by rw [hlN]; omega) hchN
    (Or.inl (Or.inl ⟨rfl, rfl⟩)) (Or.inl he2r) (fun i hr hb => hrb i (mem_children_iff.mp hr).2 hb)
    (fun y i hi => entry_gexp_pre hlen (by omega) y hi) (fun i hi => par_gexp_pre hlen (by omega) 1 hi)
    (fun i hi hs => by
      rcases Nat.lt_or_ge (i + 1) (r + L) with h | h
      · rw [← upg_take _ h, gexp_take_x hlen (by omega), upg_take M h]
      · exact absurd (Or.inr ⟨rfl, by omega⟩) hs)
    (fun i c hi _ _ hcx => hcnt i c hi hcx)
    (fun i c hi hc hcx => by obtain ⟨_, rfl⟩ := hxc i c hc hcx; exact Or.inl (Or.inl ⟨rfl, rfl⟩))
    (fun i k hi hk hkx => by
      obtain ⟨_, _, _, _, hcase⟩ := upg_spec hk
      exact Or.inr ⟨rfl, by rcases hcase with h | ⟨_, h⟩ <;> omega⟩)
    (fun i j hi hj hjx hb => by
      have hjl := (mem_children hj).2
      rw [hlN] at hjl
      rcases par0_tail2 hlen hL hp hd0e (by omega) hjx hjl with ⟨hjx', _⟩ | ⟨p', hp', hp'1, _⟩
      · rw [hjx'] at hb
        have := e2_of_col (show col (TRIO.gexp M r L d0 d1 n) (r + L) = (entry (TRIO.gexp M r L d0 d1 n) 0 i + 1, entry (TRIO.gexp M r L d0 d1 n) 1 i, 1) from hb)
        omega
      · rw [(mem_children_iff.mp hj).2] at hp'; cases hp'; omega)
    (fun i j hi hj hjx hjb => by
      obtain ⟨hjx', hir⟩ := hxc i j hj hjx
      rw [hjx', hir] at hjb; exact absurd hjb hxr)
    (fun i j k hi hj hjx hjb hk hkx => by
      obtain ⟨_, hjr⟩ := hxc j k hk hkx
      rw [hjr] at hj hjb
      exact absurd hjb (hrb i (mem_children_iff.mp hj).2))
    (fun i h => h.elim) (fun i h => h) (fun i c _ _ h => h.elim) (fun i j c _ _ _ _ _ h => h.elim)
    (fun c hc _ _ hd => hDvNil c hc hd) (fun c hc hw _ hd => hCLnil c hc hw (hDvNil c hc hd))
    hCLnil (fun i hi hns _ hD hv => hOS i hi hns hD hv) hVSh hAbs hSeed hVSN hHard hOTout
    (fun _ i _ h => h.elim)
    (fun _ i _ hs => by
      rcases hs with (⟨_, rfl⟩ | ⟨h, _⟩) | h
      · exact hsdec
      · cases h
      · exact h.elim)


end

end Ytosk
