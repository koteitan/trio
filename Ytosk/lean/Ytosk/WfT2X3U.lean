/-
**WfT2X3: the three `t = 2` engines with `AbsWNxU` (2026-11-01, t = 2 Bad2 route).**

`t2_sv_belowX`, `t2_qr_belowX`, `t2_qn_belowX`: copies of `t2_sv_below` (V3ExpT2SB), `t2_qr_below` (V3ExpT2QB),
`t2_qn_below` (V3ExpT2NB) with
- `AbsWN M M[n]` replaced by `AbsWNxU M M[n]` (absorption, or the bad shape `BadAbsShape`) and `NotBumpKidXU`
  (at a column where the absorption fails, the parent `m = P₀ i` is not a bump child; measured: 926 failing
  columns on graft36/36b/36c and graftM36/graftM36x, 0 exceptions; vacuous where `AbsWN` holds),
- `FrameShape` replaced by `FrameShapeXU` in the conclusion.
The bad columns are `BdXU M N ρ σ bnd i := i < bnd ∧ e₁ i ≠ 0 ∧ e₂ i ≠ 0 ∧ ¬ AbsAt i ∧ BadAbsShape i`.
-/
import Ytosk.WfT2X2U
import Ytosk.V3AbsUpgShape
import Ytosk.V3ExpT2SB
import Ytosk.V3ExpT2QB
import Ytosk.V3ExpT2NB

namespace Ytosk.WfT2X

open T Classical Ytosk.WfAbsW

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


section
variable {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn2 : 2 ≤ n)
  (hu : upg M (r + L - 1) = some (r + L))
include hlen hL hp hd0e hn2 hu

/-- **`t = 2`, `q = r`, `x − 1` upgrades to `x`: Good3 of `M[n]` before `x`.** -/
theorem t2_sv_belowXU (hBE : BumpE2 M) (hZ2 : Z2 M) (hUAT : UAT M) (hR12 : R12 M) (hR01 : R01 M)
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
    (hAbs : AbsWNxU M (TRIO.gexp M r L d0 d1 n) (r + L) ρ σ)
    (hNB : NotBumpKidXU M (TRIO.gexp M r L d0 d1 n) (r + L) ρ σ)
    (hHA : T2HardA M (TRIO.gexp M r L d0 d1 n) (r + L) r ρ σ)
    (hOTout : ∀ b j, r + L ≤ j → j < (TRIO.gexp M r L d0 d1 n).length → isOT (valB σ b j) = true)
    (hseed : Lhd z (σ.o r) (ρ.o r) ∧ isOT (σ.o r) = true)
    (hsdec : (cvals (TRIO.gexp M r L d0 d1 n) σ r).Pairwise (fun a b => b ≤ a)) :
    ∀ i, i < r + L → isOT (σ.o i) = true ∧ isOT (σ.v i) = true ∧
      (cvals (TRIO.gexp M r L d0 d1 n) σ i).Pairwise (fun a b => b ≤ a) ∧
      (¬ SV r (r + L - 1) true i → ¬ (fun _ _ => False : Bool → Nat → Prop) true i →
        FrameShapeXU M (TRIO.gexp M r L d0 d1 n) ρ σ i) ∧
      (¬ (fun _ _ => False : Bool → Nat → Prop) true i → σ.o i ≤ ρ.o i) ∧
      (¬ SV r (r + L - 1) false i → DepS M (SV r (r + L - 1)) false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ children (TRIO.gexp M r L d0 d1 n) i = Lb ++ [j] ∧
          col M j = bump M i ∧ col (TRIO.gexp M r L d0 d1 n) j = bump (TRIO.gexp M r L d0 d1 n) i ∧
          children M j = Kb ++ [k] ∧ children (TRIO.gexp M r L d0 d1 n) j = Kb ++ [k] ∧
          (∀ d ∈ Kb, σ.o d = ρ.o d) ∧
          (∀ d ∈ Lb, bumpTerm (TRIO.gexp M r L d0 d1 n) σ i d = bumpTerm M ρ i d) ∧
          (∀ d ∈ Lb, ∀ e ∈ children M d, e < r + L → σ.o e = ρ.o e) ∧
          Lhd z (σ.o k) (ρ.o k) ∧ isOT (σ.o k) = true) ∧
      (¬ DepS M (SV r (r + L - 1)) false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        ∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, k < r + L → σ.o k = ρ.o k) := by
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
        PX M (BdXU M (TRIO.gexp M r L d0 d1 n) ρ σ (r + L)) ρ σ b' i') →
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
  exact t2_assembleOTXU (Bd := BdXU M (TRIO.gexp M r L d0 d1 n) ρ σ (r + L)) (S := SV r (r + L - 1)) (W := fun _ _ => False) (bnd := r + L) hC hG hRM hCN hRN
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
    hCLnil (fun i hi hns _ hD hv => hOS i hi hns hD hv) hVSh (bdxu_absX hAbs) bdxu_up bdxu_F bdxu_cl hNB hSeed hHA
    (fun i h => by rcases h with h | h; exact h.2; exact absurd h.1 (by decide)) hOTout
    (fun _ i _ h => h.elim)
    (fun _ i _ hs => by
      rcases hs with (⟨_, rfl⟩ | ⟨h, _⟩) | h
      · exact hsdec
      · cases h
      · exact h.elim)


end

section
variable {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn2 : 2 ≤ n)
  (hXu : ∀ i, upg M i ≠ some (r + L)) (hXb : col M (r + L) ≠ bump M r)
  (hrb : ∀ p, par M 0 r = some p → col M r ≠ bump M p)
  (he2r : entry M 2 r = 0)
  (hIU : ∀ c, c < r + L → topped M c = true → isUpg (TRIO.gexp M r L d0 d1 n) c = isUpg M c)
include hlen hL hp hd0e hn2 hXu hXb hrb he2r hIU

/-- **`t = 2`, `q = r`, the main case: Good3 of `M[n]` before `x`.** -/
theorem t2_qr_belowXU (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M)
    (hUAB : UAB M) (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    {ρ σ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    {rkN : Bool → Nat → Nat} (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ)
    (hRN : Rk (TRIO.gexp M r L d0 d1 n) rkN)
    (hF : FrameClosed M ρ) (hFO : FrameOT M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ)
    (hKD : BumpKidsDec M ρ)
    (hAbs : AbsWNxU M (TRIO.gexp M r L d0 d1 n) (r + L) ρ σ)
    (hNB : NotBumpKidXU M (TRIO.gexp M r L d0 d1 n) (r + L) ρ σ)
    (hxcN : Counted (TRIO.gexp M r L d0 d1 n) r (r + L))
    (hHA : T2HardA M (TRIO.gexp M r L d0 d1 n) (r + L) r ρ σ)
    (hOTout : ∀ b j, r + L ≤ j → j < (TRIO.gexp M r L d0 d1 n).length → isOT (valB σ b j) = true)
    (hseed : Lhd z (σ.o r) (ρ.o r) ∧ isOT (σ.o r) = true)
    (hsdec : (cvals (TRIO.gexp M r L d0 d1 n) σ r).Pairwise (fun a b => b ≤ a)) :
    ∀ i, i < r + L → isOT (σ.o i) = true ∧ isOT (σ.v i) = true ∧
      (cvals (TRIO.gexp M r L d0 d1 n) σ i).Pairwise (fun a b => b ≤ a) ∧
      (i ≠ r → FrameShapeXU M (TRIO.gexp M r L d0 d1 n) ρ σ i) ∧ σ.o i ≤ ρ.o i ∧
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
  have hdlR := deps_lhd_otXU (Bd := BdXU M (TRIO.gexp M r L d0 d1 n) ρ σ (r + L)) (S := S) (W := fun _ _ => False) (bnd := r + L) hC hG hCN hRM (by omega)
    (by rw [hlN]; omega)
    hF hFO hVS hTD hKD (hHA.sv S (fun i h => h.2)) (hHA.1.1.toS S (r + L)) hHA.1.2.1 hoff hOTout (fun _ h => h)
    (fun _ _ _ _ h => h.elim) (fun _ _ _ _ _ _ _ _ h => h.elim) (fun _ _ h => h.elim)
    (by
      rintro b i ⟨hb, hi'⟩ _ _ _
      subst hb
      rw [hi']
      exact hseed)
    (hHA.seed S (fun i h => h.2)) (hHA.re S (fun i h => h.2))
    (fun c hc _ _ hv => hDvNil c hc hv) (fun c hc _ hv => hCLnil c hc (hDvNil c hc hv))
    (fun c hc _ h => hCLnil c hc h) (fun i hi hns _ hD hv => hOc i hi hns hD hv) hVc hupgK (bdxu_absX hAbs) bdxu_up bdxu_F hNB
  have hdl : ∀ b i, DepS M S b i → i < r + L → ¬ False → PX M (BdXU M (TRIO.gexp M r L d0 d1 n) ρ σ (r + L)) ρ σ b i :=
    fun b i hD hi hW => (hdlR b i hD hi hW).1
  have hgb := good_below_ofXU (W := fun _ _ => False) hC hG hCN (by omega) (by rw [hlN]; omega) hoff
    (fun b i hd hi hw => hdl b i hd hi hw) bdxu_up bdxu_F bdxu_cl hNB (fun _ h => h) (fun _ _ _ _ h => h.elim) (fun _ _ h => h.elim)
    (by
      intro i hi hs
      rcases hs with ⟨_, rfl⟩ | h
      · exact hsdec
      · exact h.elim)
    (fun i hi _ _ hv => hCLnil i hi (hDvNil i hi hv))
    (fun i hi _ _ hv => hDvNil i hi hv)
    (fun c hc _ hv => hCLnil c hc (hDvNil c hc hv))
    (fun c hc _ hv _ => hDvNil c hc hv)
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

section
variable {M : Mat} {r L d0 d1 n qp : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hp : par M 0 (r + L) = some (r + qp)) (hqp : qp < L)
  (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn2 : 2 ≤ n)
  (hxb : col M (r + L) = bump M (r + qp)) (hBE : BumpE2 M)
include hlen hL hA hp hqp hd0e hn2 hxb hBE

omit hBE in
/-- **`t = 2`, `q ≠ r`: Good3 of `M[n]` before `x`.** -/
theorem t2_qn_belowXU (hBE : BumpE2 M) (hZ2 : Z2 M) (hUAT : UAT M) (hR12 : R12 M) (hR01 : R01 M)
    (h00 : entry M 0 0 = 0) (he2r : entry M 2 r = 0) {pq : Nat} (hpq : par M 0 (r + qp) = some pq)
    (hqb : col M (r + qp) ≠ bump M pq) (he2pq : entry M 2 pq = 0) (hCLq : CL M (r + qp) = [])
    (hpqCL : CL M pq ≠ [])
    (hIUt : ∀ c, c < r + L → c ≠ r + qp → topped M c = true → isUpg (TRIO.gexp M r L d0 d1 n) c = isUpg M c)
    -- the shape of `D` in `M`
    (hP1q : ∀ m, par M 1 (r + qp) = some m → ¬ DepS M (SQ (r + qp) pq) false m)
    (hqL : ∀ d ∈ children M (r + qp), col M d = bump M (r + qp) → ∀ e ∈ children M d,
      ¬ DepS M (SQ (r + qp) pq) true e)
    (hDvNil : ∀ c, c < r + L → DepS M (SQ (r + qp) pq) false c → CL M c = [])
    (hOS : ∀ i, i < r + L → ¬ SQ (r + qp) pq true i → ¬ WQ (r + qp) true i →
      DepS M (SQ (r + qp) pq) true i → ¬ DepS M (SQ (r + qp) pq) false i →
      ∃ L c R, children M i = L ++ c :: R ∧ Counted M i c ∧ DepS M (SQ (r + qp) pq) true c ∧
        (∀ d ∈ R, ¬ Counted M i d) ∧ (∀ d ∈ L, Counted M i d → ¬ DepS M (SQ (r + qp) pq) true d))
    (hVSh : ∀ i, i < r + L → ¬ SQ (r + qp) pq false i → DepS M (SQ (r + qp) pq) false i →
      (∀ m, par M 1 i = some m → ¬ DepS M (SQ (r + qp) pq) false m) ∧
      (entry M 2 i ≠ 0 → ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ col M j = bump M i ∧
        children M j = Kb ++ [k] ∧ (∀ d ∈ Kb, ¬ DepS M (SQ (r + qp) pq) true d) ∧
        (∀ d ∈ Lb, ∀ e ∈ children M d, ¬ DepS M (SQ (r + qp) pq) true e)))
    -- values
    {ρ σ : Valn} {rkM rkN : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ) (hRN : Rk (TRIO.gexp M r L d0 d1 n) rkN)
    (hF : FrameClosed M ρ) (hFO : FrameOT M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ)
    (hKD : BumpKidsDec M ρ)
    (hAbs : AbsWNxU M (TRIO.gexp M r L d0 d1 n) (r + L) ρ σ)
    (hNB : NotBumpKidXU M (TRIO.gexp M r L d0 d1 n) (r + L) ρ σ)
    (hHA : T2HardA M (TRIO.gexp M r L d0 d1 n) (r + L) pq ρ σ)
    (hOTout : ∀ b j, r + L ≤ j → j < (TRIO.gexp M r L d0 d1 n).length → isOT (valB σ b j) = true)
    (hvqot : isOT (σ.v (r + qp)) = true)
    (hseed : Lhd z (σ.o pq) (ρ.o pq) ∧ isOT (σ.o pq) = true)
    (hsdec : (cvals (TRIO.gexp M r L d0 d1 n) σ pq).Pairwise (fun a b => b ≤ a))
    (hqot : isOT (σ.o (r + qp)) = true)
    (hqdec : (cvals (TRIO.gexp M r L d0 d1 n) σ (r + qp)).Pairwise (fun a b => b ≤ a)) :
    ∀ i, i < r + L → isOT (σ.o i) = true ∧ isOT (σ.v i) = true ∧
      (cvals (TRIO.gexp M r L d0 d1 n) σ i).Pairwise (fun a b => b ≤ a) ∧
      (¬ SQ (r + qp) pq true i → ¬ WQ (r + qp) true i →
        FrameShapeXU M (TRIO.gexp M r L d0 d1 n) ρ σ i) ∧
      (¬ WQ (r + qp) true i → σ.o i ≤ ρ.o i) ∧
      (¬ SQ (r + qp) pq false i → DepS M (SQ (r + qp) pq) false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        ∃ Lb Kb j k, children M i = Lb ++ [j] ∧ children (TRIO.gexp M r L d0 d1 n) i = Lb ++ [j] ∧
          col M j = bump M i ∧ col (TRIO.gexp M r L d0 d1 n) j = bump (TRIO.gexp M r L d0 d1 n) i ∧
          children M j = Kb ++ [k] ∧ children (TRIO.gexp M r L d0 d1 n) j = Kb ++ [k] ∧
          (∀ d ∈ Kb, σ.o d = ρ.o d) ∧
          (∀ d ∈ Lb, bumpTerm (TRIO.gexp M r L d0 d1 n) σ i d = bumpTerm M ρ i d) ∧
          (∀ d ∈ Lb, ∀ e ∈ children M d, e < r + L → σ.o e = ρ.o e) ∧
          Lhd z (σ.o k) (ρ.o k) ∧ isOT (σ.o k) = true) ∧
      (¬ DepS M (SQ (r + qp) pq) false i → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 →
        ∀ j ∈ children M i, col M j = bump M i → ∀ k ∈ children M j, k < r + L → σ.o k = ρ.o k) := by
  have hlN : (TRIO.gexp M r L d0 d1 n).length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn2
  have hqx : r + qp < r + L := by omega
  have hqM : r + qp < M.length := by omega
  have hxq : r + L ∈ children M (r + qp) := mem_children_iff.mpr ⟨by omega, hp⟩
  have hpqq : pq < r + qp := par_lt M 0 _ _ hpq
  have he2q := e2_q hlen hp hxb hBE
  have he1q : entry M 1 (r + qp) ≠ 0 := by
    have h1 : entry M 1 (r + L) = entry M 1 (r + qp) :=
      e1_of_col (show col M (r + L) = (entry M 0 (r + qp) + 1, entry M 1 (r + qp), 1) from hxb)
    intro h0; rw [← h1] at h0; have := hR12 _ h0; have := e2_x hxb; omega
  have hxN2 : entry (TRIO.gexp M r L d0 d1 n) 2 (r + L) = 0 := by
    rw [(entry_xprimeQ hlen hL hA hp hqp hd0e (by omega) hn2).1, he2r]
  have hcolN : ∀ i, i < r + L → col (TRIO.gexp M r L d0 d1 n) i = col M i := fun i hi => col_gexp_pre hlen (by omega) hi
  have hbumpN : ∀ i, i < r + L → bump (TRIO.gexp M r L d0 d1 n) i = bump M i := fun i hi => by
    unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hi, entry_gexp_pre hlen (by omega) 1 hi]
  have hchN : ∀ i, i < r + L → children (TRIO.gexp M r L d0 d1 n) i = children M i :=
    fun i hi => children_N2Q hlen hL hA hp hqp hd0e (by omega) hn2 hi
  have hnu : upg M (r + L - 1) ≠ some (r + L) := fun h =>
    upg_not_x hlen hA hp hxb hBE h (le_refl _) (by omega)
  have hupgN : ∀ i, i < r + L → upg (TRIO.gexp M r L d0 d1 n) i = upg M i := fun i hi =>
    upg_NQ hlen hL hA hp hqp hd0e hn2 he2r hnu hi
  have hxc : ∀ i c, c ∈ children M i → r + L ≤ c → c = r + L ∧ i = r + qp := by
    intro i c hc hcx
    have := (mem_children hc).2
    have hcx' : c = r + L := by omega
    refine ⟨hcx', ?_⟩
    have h' := (mem_children_iff.mp hc).2; rw [hcx', hp] at h'; exact (Option.some.inj h').symm
  have hcntS : ∀ i c, i < r + L → i ≠ pq → c ∈ children M i → c < r + L →
      (Counted (TRIO.gexp M r L d0 d1 n) i c ↔ Counted M i c) := by
    intro i c hi hipq hc hcx
    apply counted_NQ hlen hL hA hp hqp hd0e hn2 hxb hIUt hi hcx
    intro h; apply hipq
    have h' := (mem_children_iff.mp hc).2; rw [h, hpq] at h'; exact (Option.some.inj h').symm
  have hbjN : ∀ i j, i < r + L → j ∈ children (TRIO.gexp M r L d0 d1 n) i → r + L ≤ j → col (TRIO.gexp M r L d0 d1 n) j ≠ bump (TRIO.gexp M r L d0 d1 n) i := by
    intro i j hi hj hjx hb
    have hjl := (mem_children hj).2
    rw [hlN] at hjl
    rcases par0_tail2Q hlen hL hA hp hqp hd0e (by omega) hjx hjl with ⟨hjx', _⟩ | ⟨p', hp', hp'1, _⟩
    · rw [hjx'] at hb
      have := e2_of_col (show col (TRIO.gexp M r L d0 d1 n) (r + L) = (entry (TRIO.gexp M r L d0 d1 n) 0 i + 1, entry (TRIO.gexp M r L d0 d1 n) 1 i, 1) from hb)
      omega
    · rw [(mem_children_iff.mp hj).2] at hp'; cases hp'; omega
  have hoff := t2_off_gen (S := SQ (r + qp) pq) (bnd := r + L) hC hCN hRN (by omega) (by rw [hlN]; omega)
    (fun i hi _ => hchN i hi) (DepS.ov (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (Or.inr (DepS.seed (Or.inl ⟨rfl, rfl⟩))) (fun i hq hb => by have h' := (mem_children_iff.mp hq).2; rw [hpq] at h'; cases h'; exact hqb hb)
    (fun y i hi => entry_gexp_pre hlen (by omega) y hi) (fun i hi => par_gexp_pre hlen (by omega) 1 hi)
    (fun i hi _ => hupgN i hi)
    (fun i c hi hd hc hcx => hcntS i c hi (fun h => hd (DepS.seed (Or.inr ⟨rfl, h⟩))) hc hcx)
    (fun i c hi hc hcx => by
      obtain ⟨_, rfl⟩ := hxc i c hc hcx
      exact DepS.ov (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (fun i k hi hk hkx => (upg_not_x hlen hA hp hxb hBE hk hkx hi).elim)
    hbjN
    (fun i j hi hj hjx _ => by
      obtain ⟨_, rfl⟩ := hxc i j hj hjx
      exact DepS.seed (Or.inl ⟨rfl, rfl⟩))
    (fun i j k hi hj hjx hjb hk hkx => by
      obtain ⟨_, rfl⟩ := hxc j k hk hkx
      have h' := (mem_children_iff.mp hj).2; rw [hpq] at h'; cases h'
      exact absurd hjb hqb)
  -- the seed `v(q)`
  have hcqM : children M (r + qp) =
      (children M (r + qp)).filter (fun d => decide (d < r + L)) ++ [r + L] :=
    split_last_max _ _ (children_sorted M _) hxq (fun d hd => by have := (mem_children hd).2; omega)
  have hvq : Lhd z (σ.v (r + qp)) (ρ.v (r + qp)) := by
    apply v_bump_lost (L := (children M (r + qp)).filter (fun d => decide (d < r + L))) (j := r + L)
      hC hG hCN hqM (by rw [hlN]; omega) he1q (by omega)
      (entry_gexp_pre hlen (by omega) 1 hqx) (entry_gexp_pre hlen (by omega) 2 hqx)
    · rw [par_gexp_pre hlen (by omega) 1 hqx]
      cases hm : par M 1 (r + qp) with
      | none => rfl
      | some m =>
        show σ.v m = ρ.v m
        exact (hoff m (by have := par_lt M 1 _ m hm; omega)).2 (hP1q m hm)
    · exact hcqM
    · rw [hchN _ hqx]; exact hcqM
    · intro d hd
      have hdx : d < r + L := by have := (List.mem_filter.mp hd).2; simpa using this
      have hdM : d ∈ children M (r + qp) := (List.mem_filter.mp hd).1
      apply bumpTerm_eq_of
      · rw [hcolN d hdx, hbumpN _ hqx]
      · intro hb
        rw [hchN d hdx]
        apply List.map_congr_left
        intro e he
        have hex : e < r + L := by
          have hel := (mem_children he).2
          by_contra h'
          have hex' : e = r + L := by omega
          have h'' := (mem_children_iff.mp he).2
          rw [hex', hp] at h''
          have hdq : d = r + qp := (Option.some.inj h'').symm
          have := (mem_children hdM).1
          omega
        exact (hoff e hex).1 (hqL d hdM hb e he)
    · unfold bumpTerm; rw [if_pos hxb, children_last_nil hlen]; exact omega_z
    · unfold bumpTerm
      rw [if_neg]
      intro hb
      have := e2_of_col (show col (TRIO.gexp M r L d0 d1 n) (r + L) = (entry (TRIO.gexp M r L d0 d1 n) 0 (r + qp) + 1, entry (TRIO.gexp M r L d0 d1 n) 1 (r + qp), 1) from hb)
      omega
  have hCLnil : ∀ c, c < r + L → ¬ WQ (r + qp) true c → CL M c = [] → CL (TRIO.gexp M r L d0 d1 n) c = [] := by
    intro c hc hw hcl
    by_cases hcpq : c = pq
    · exact (hpqCL (by rw [← hcpq]; exact hcl)).elim
    · have hcq : c ≠ r + qp := fun h => hw ⟨rfl, h⟩
      unfold CL at hcl ⊢
      rw [hchN c hc, ← hcl]
      apply List.filter_congr
      intro d hd
      have hdx : d < r + L := by
        have := (mem_children hd).2
        by_contra h'
        exact hcq (hxc c d hd (by omega)).2
      simp only [hcntS c d hc hcpq hd hdx]
  have hSeed : ∀ b i, SQ (r + qp) pq b i → i < r + L → DepS M (SQ (r + qp) pq) b i →
      (∀ i, i < r + L → (¬ DepS M (SQ (r + qp) pq) true i → σ.o i = ρ.o i) ∧
        (¬ DepS M (SQ (r + qp) pq) false i → σ.v i = ρ.v i)) →
      (∀ b' i', rkM b' i' < rkM b i → DepS M (SQ (r + qp) pq) b' i' → i' < r + L →
        ¬ WQ (r + qp) b' i' → PX M (BdXU M (TRIO.gexp M r L d0 d1 n) ρ σ (r + L)) ρ σ b' i') →
      Lhd z (valB σ b i) (valB ρ b i) ∧ isOT (valB σ b i) = true := by
    rintro b i (⟨hb, hi'⟩ | ⟨hb, hi'⟩) _ _ _ _
    · subst hb; rw [hi']; exact ⟨hvq, hvqot⟩
    · subst hb; rw [hi']
      exact hseed
  exact t2_assembleOTXU (Bd := BdXU M (TRIO.gexp M r L d0 d1 n) ρ σ (r + L)) (S := SQ (r + qp) pq) (W := WQ (r + qp)) (bnd := r + L) hC hG hRM hCN hRN
    hF hFO hVS hTD hKD hlen (by rw [hlN]; omega) hchN
    (Or.inr ⟨rfl, rfl⟩) (Or.inr (Or.inl ⟨rfl, rfl⟩)) (fun i hq hb => by have h' := (mem_children_iff.mp hq).2; rw [hpq] at h'; cases h'; exact hqb hb)
    (fun y i hi => entry_gexp_pre hlen (by omega) y hi) (fun i hi => par_gexp_pre hlen (by omega) 1 hi)
    (fun i hi _ => hupgN i hi)
    (fun i c hi hd hc hcx => hcntS i c hi (fun h => hd (Or.inr ⟨rfl, h⟩)) hc hcx)
    (fun i c hi hc hcx => by obtain ⟨_, rfl⟩ := hxc i c hc hcx; exact Or.inr ⟨rfl, rfl⟩)
    (fun i k hi hk hkx => (upg_not_x hlen hA hp hxb hBE hk hkx hi).elim)
    hbjN
    (fun i j hi hj hjx _ => by obtain ⟨_, rfl⟩ := hxc i j hj hjx; exact Or.inl ⟨rfl, rfl⟩)
    (fun i j k hi hj hjx hjb hk hkx => by
      obtain ⟨_, rfl⟩ := hxc j k hk hkx
      have h' := (mem_children_iff.mp hj).2; rw [hpq] at h'; cases h'
      exact absurd hjb hqb)
    (fun i h => by obtain ⟨-, hi⟩ := h; rw [hi]; exact DepS.ov (DepS.seed (Or.inl ⟨rfl, rfl⟩)))
    (fun i h => by cases h.1)
    (fun i c hc _ h => by
      obtain ⟨-, hc'⟩ := h
      have h' := (mem_children_iff.mp hc).2; rw [hc', hpq] at h'; cases h'
      exact Or.inr ⟨rfl, rfl⟩)
    (fun i j c _ _ hj hjb hc h => by
      obtain ⟨-, hc'⟩ := h
      have h' := (mem_children_iff.mp hc).2; rw [hc', hpq] at h'; cases h'
      have := e2_of_col (show col M _ = (entry M 0 i + 1, entry M 1 i, 1) from hjb)
      omega)
    (fun c hc _ _ hd => hDvNil c hc hd) (fun c hc hw _ hd => hCLnil c hc hw (hDvNil c hc hd))
    hCLnil hOS hVSh (bdxu_absX hAbs) bdxu_up bdxu_F bdxu_cl hNB hSeed hHA
    (fun i h => by rcases h with h | h; exact absurd h.1 (by decide); exact h.2) hOTout
    (fun _ i _ h => by obtain ⟨-, hi⟩ := h; rw [hi]; exact hqot)
    (fun _ i _ hs => by
      rcases hs with (⟨h, _⟩ | ⟨_, hi⟩) | ⟨_, hi⟩
      · cases h
      · rw [hi]; exact hsdec
      · rw [hi]; exact hqdec)


end

end Ytosk.WfT2X
