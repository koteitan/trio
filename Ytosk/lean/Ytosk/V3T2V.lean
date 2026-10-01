/-
**3 行・t = 2・q = r で x − 1 が x へ上げる場合: 組み立て。**

M では upg(x − 1) = x で v_M(x − 1) = V + last(v(x)) = V + ω（x は子のない行 2 が 1 の列）。
N では位置 x の列 x′ の行 2 が 0 なので、x − 1 はどこへも上げず（`upgN_xm1_none`）v_N(x − 1) = V + 1。
1 ◁ ω から v_N(x − 1) ◁ v_M(x − 1)（`v_upg_lost`）。種は o(r) と v(x − 1)、弱い呼び出しはない。
x は r の bump 子でないこと（`col_x_ne_bump_r`）は upg の形から出る。
-/
import Ytosk.V3T2QM

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- A climb whose test always fails finds nothing. -/
theorem climb_all_false {step : Nat → Option Nat} {ok : Nat → Bool} (h : ∀ q, ok q = false) :
    ∀ f s, climb step ok f s = none
  | 0, _ => rfl
  | _ + 1, none => rfl
  | f + 1, some q => by simp only [climb, h q]; exact climb_all_false h f _

/-- `V + ω^S ◁ V + ω^(S+1)`. -/
theorem add_omega_succ_lhd {V S : T} (hV : isOT V = true) (hS : isOT S = true) :
    Lhd z (add V (omega S)) (add V (omega (succ S))) := by
  have hl := lhd_omega_succ hS
  have hE : LhdE (add V (omega S)) (add V (omega (succ S))) := by
    apply v_strong hV (single_omega hS) (single_omega (isOT_succ hS)) (Or.inr hl)
    intro r hr hn hlt
    obtain ⟨s, b', h1', h2'⟩ := omega_succ_form hS
    rw [h1'] at hn
    rw [show succ S = app S one from rfl, h2'] at hlt ⊢
    have := single_between (mem_summands hr) hn hlt
    rw [this, ← h1', ← h2']; exact hl
  apply lhd_of_lhdE_lt hE
  exact add_lt_add_left V (omega_lt_omega hS (isOT_succ hS) (lt_succ_self S))

/-- The seeds for the upgrade case: `o(r)` and `v(x − 1)`. -/
def SV (a b : Nat) : Bool → Nat → Prop := fun bb i => (bb = true ∧ i = a) ∨ (bb = false ∧ i = b)

section
variable {M : Mat} {r L d0 d1 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hp : par M 0 (r + L) = some r) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn2 : 2 ≤ n)
  (hu : upg M (r + L - 1) = some (r + L))
include hlen hL hp hd0e hn2 hu

omit hlen hL hd0e hn2 in
/-- **`x` is not a bump child of `r`.** -/
theorem col_x_ne_bump_r : col M (r + L) ≠ bump M r := by
  intro hb
  obtain ⟨m, _, hmx, hcol, _⟩ := upg_spec hu
  have he1x := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from hb)
  have he0x := e0_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from hb)
  have he0m := e0_of_col hcol
  by_cases hmr : m = r
  · rw [hmr] at hmx; have := par1_entry_lt hmx; omega
  · have hAm : Anc0 M m (r + L) := anc0_of_par M 1 m (r + L) hmx
    have hmxl := par_lt M 1 _ m hmx
    have hAmr : Anc0 M m r := anc0_par hAm (by omega) hp
    have := anc0_e0_lt hAmr hmr
    omega

/-- **`x − 1` upgrades to nothing in `N`.** -/
theorem upgN_xm1_none (he2r : entry M 2 r = 0) :
    upg (TRIO.gexp M r L d0 d1 n) (r + L - 1) = none := by
  obtain ⟨m, hm1, _, hcol, _⟩ := upg_spec hu
  have hix : r + L - 1 + 1 = r + L := by omega
  obtain ⟨he1, he2⟩ := upg_e12 hu
  have hmi := par_lt M 1 _ m hm1
  have hlN : (TRIO.gexp M r L d0 d1 n).length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn2
  have hx2 : entry (TRIO.gexp M r L d0 d1 n) 2 (r + L) = 0 := by
    have h := TRIO.gexp_getD_mir (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := d1) (n := n)
      (k := 1) (q := 0) hlen (by omega) hL
    rw [show r + (1 * L + 0) = r + L by omega, Nat.add_zero] at h
    unfold entry; rw [h]; exact he2r
  have hx0 : entry (TRIO.gexp M r L d0 d1 n) 0 (r + L) = entry M 0 r + 1 * d0 := by
    have h := TRIO.gexp_getD_mir (M := M) (j0 := r) (Lb := L) (d0 := d0) (d1 := d1) (n := n)
      (k := 1) (q := 0) hlen (by omega) hL
    rw [show r + (1 * L + 0) = r + L by omega, Nat.add_zero] at h
    unfold entry; rw [h]; rfl
  have he0x := e0_of_col hcol
  have he0m : entry (TRIO.gexp M r L d0 d1 n) 0 m = entry M 0 m :=
    entry_gexp_pre hlen (by omega) 0 (by omega)
  have he2m : entry (TRIO.gexp M r L d0 d1 n) 2 m = entry M 2 m :=
    entry_gexp_pre hlen (by omega) 2 (by omega)
  unfold upg
  rw [entry_gexp_pre hlen (by omega) 1 (by omega), entry_gexp_pre hlen (by omega) 2 (by omega),
    par_gexp_pre hlen (by omega) 1 (by omega), hm1]
  rw [if_neg (by
    rintro (h | h | h)
    · exact he1 h
    · exact he2 h
    · rw [hlN] at h; omega)]
  simp only
  rw [if_neg (by
    rintro ⟨_, hc⟩
    have := e2_of_col hc
    rw [hix, hx2, he2m] at this; omega)]
  apply climb_all_false
  intro q
  simp only [decide_eq_false_iff_not]
  rintro ⟨_, hc, hlt⟩
  have := e0_of_col hc
  rw [hix, hx0] at hlt
  rw [he0m] at this
  omega

omit hd0e hp in
/-- **The seed `v(x − 1)`**: `v_N(x − 1) = V + 1 ◁ V + ω = v_M(x − 1)`. -/
theorem v_xm1_lhd (hZ2 : Z2 M) (he2r : entry M 2 r = 0) {ρ σ : Valn} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ)
    (hV : vOpt σ (par (TRIO.gexp M r L d0 d1 n) 1 (r + L - 1)) = vOpt ρ (par M 1 (r + L - 1)))
    (hun : upg (TRIO.gexp M r L d0 d1 n) (r + L - 1) = none) :
    Lhd z (σ.v (r + L - 1)) (ρ.v (r + L - 1)) := by
  obtain ⟨m, hm1, hmx, hcol, _⟩ := upg_spec hu
  obtain ⟨he1, he2⟩ := upg_e12 hu
  have he2z : entry M 2 (r + L - 1) = 0 := by have := hZ2 (r + L - 1); omega
  have hlN : (TRIO.gexp M r L d0 d1 n).length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn2
  have hiM : r + L - 1 < M.length := by omega
  have hxM : r + L < M.length := by omega
  set V := vOpt ρ (par M 1 (r + L - 1)) with hVdef
  have hVot : isOT V = true := by
    rw [hVdef, hm1]; exact hG.ot_v m (by have := par_lt M 1 _ m hm1; omega)
  -- `v(x) = V' + ω`
  have he1x : entry M 1 (r + L) ≠ 0 := by rw [e1_of_col hcol]; exact he1
  have he2x : entry M 2 (r + L) ≠ 0 := by rw [e2_of_col hcol]; omega
  have hV'ot : isOT (vOpt ρ (par M 1 (r + L))) = true := by
    rw [hmx]; exact hG.ot_v m (by have := par_lt M 1 _ m hmx; omega)
  have hvx : ρ.v (r + L) = add (vOpt ρ (par M 1 (r + L))) (omega one) := by
    rw [(hC _ hxM).2]; unfold vRhs
    rw [if_neg he1x, if_neg he2x, children_last_nil hlen]
    show sf (add _ (omega (sumN [one]))) = _
    rw [show sumN [one] = one from rfl, sf_ot (isOT_add hV'ot (isOT_omega isOT_one))]
  have hlast : last (ρ.v (r + L)) = omega one := by
    obtain ⟨s, y, h⟩ := (single_omega isOT_one).2
    rw [hvx, h, last_add_single]
  have ev : ρ.v (r + L - 1) = add V (omega (succ z)) := by
    rw [(hC _ hiM).2]; unfold vRhs
    rw [if_neg he1, if_pos he2z, hu]
    show sf (add V (last (ρ.v (r + L)))) = _
    rw [hlast, sf_ot (isOT_add hVot (isOT_omega isOT_one))]; rfl
  have ev' : σ.v (r + L - 1) = add V (omega z) := by
    rw [(hCN _ (by rw [hlN]; omega)).2]; unfold vRhs
    rw [entry_gexp_pre hlen (by omega) 1 (by omega), entry_gexp_pre hlen (by omega) 2 (by omega),
      if_neg he1, if_pos he2z, hun, hV]
    show sf (add V one) = _
    rw [omega_z, sf_ot (isOT_add hVot isOT_one)]
  rw [ev, ev']
  exact add_omega_succ_lhd hVot rfl

omit hu in
/-- **`topped` before `x`** is the same (`x` is not a bump child of `r` in either). -/
theorem topped_NV (hxr : col M (r + L) ≠ bump M r) (he2r : entry M 2 r = 0) {c : Nat}
    (hc : c < r + L) : topped (TRIO.gexp M r L d0 d1 n) c = topped M c := by
  unfold topped
  rw [children_N2 hlen hL hp hd0e (by omega) hn2 hc]
  cases hl : (children M c).getLast? with
  | none => rfl
  | some d =>
    have hd := List.mem_of_getLast? hl
    have hdl := (mem_children hd).2
    simp only
    rcases Nat.lt_or_ge d (r + L) with h | h
    · rw [col_gexp_pre hlen (by omega) h, show bump (TRIO.gexp M r L d0 d1 n) c = bump M c by
        unfold bump; rw [entry_gexp_pre hlen (by omega) 0 hc, entry_gexp_pre hlen (by omega) 1 hc]]
    · have hdx : d = r + L := by omega
      subst hdx
      have hcr : c = r := by
        have h' := (mem_children_iff.mp hd).2; rw [hp] at h'; exact (Option.some.inj h').symm
      have h1 : ¬ col (TRIO.gexp M r L d0 d1 n) (r + L) = bump (TRIO.gexp M r L d0 d1 n) c := by
        intro h'
        have := e2_of_col (show col (TRIO.gexp M r L d0 d1 n) (r + L) = (entry (TRIO.gexp M r L d0 d1 n) 0 c + 1, entry (TRIO.gexp M r L d0 d1 n) 1 c, 1) from h')
        rw [(entry_xprime hlen hL hp hd0e (by omega) hn2).1, he2r] at this; omega
      have h2 : ¬ col M (r + L) = bump M c := by rw [hcr]; exact hxr
      simp only [decide_eq_false h1, decide_eq_false h2]

/-- **`t = 2`, `q = r`, `x − 1` upgrades to `x`, all `n ≥ 2`.** -/
theorem t2_sv_main (hBE : BumpE2 M) (hZ2 : Z2 M) (hUAT : UAT M) (hR12 : R12 M) (hR01 : R01 M)
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
    (hCN : Cons (TRIO.gexp M r L d0 d1 n) σ) (hGN : Good3 (TRIO.gexp M r L d0 d1 n) σ) (hRN : Rk (TRIO.gexp M r L d0 d1 n) rkN)
    (hF : FrameClosed M ρ) (hVS : VSmallF M ρ) (hTD : BumpTermDec M ρ) (hKD : BumpKidsDec M ρ)
    (hAbs : ∀ i, i < r + L → entry M 1 i ≠ 0 → entry M 2 i ≠ 0 → ∀ q ∈ summands (vOpt ρ (par M 1 i)),
      ¬ q < psi z two z → q < bumpW M ρ i → Lhd z q (bumpW M ρ i))
    (hVNN : ∀ i, i < r + L → ∀ (Lc : List Nat) (cs : Nat), CL M i = Lc ++ [cs] → σ.v cs ≠ ρ.v cs →
      ∀ s y, ρ.o cs = psi s y z →
        lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true →
        VSmallV (σ.v cs))
    (hseed : ∃ X K, σ.o r = psi (ρ.v r) X z ∧ Closed (ρ.v r) X ∧
      psi (ρ.v r) X z ≤ fs (ρ.o r) (natT K)) :
    isOT (root (TRIO.gexp M r L d0 d1 n) σ) = true ∧ root (TRIO.gexp M r L d0 d1 n) σ < root M ρ := by
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
  have hRD : ∀ R, R < r + L → Anc0 M R (r + L) → col M R = (0, 0, 0) →
      DepS M (SV r (r + L - 1)) true R ∧ ¬ (fun _ _ => False : Bool → Nat → Prop) true R := by
    intro R hR hRA _
    have hRr : Anc0 M R r := anc0_par hRA (by omega) hp
    refine ⟨?_, id⟩
    apply path_upS hUAT hZ2 hR12 hBE (r - R) R r (le_refl _) (by omega) hRr (ne_of_e2z he2r)
      (DepS.seed (Or.inl ⟨rfl, rfl⟩))
    intro t _ htr
    have := htr.le
    exact ⟨r + L, by omega, hA, not_anc_out (by omega) (by omega)⟩
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
        ¬ (fun _ _ => False : Bool → Nat → Prop) b' i' → Lhd z (valB σ b' i') (valB ρ b' i')) →
      Lhd z (valB σ b i) (valB ρ b i) := by
    rintro b i (⟨hb, hi'⟩ | ⟨hb, hi'⟩) _ _ hoff _
    · subst hb; rw [hi']
      show Lhd z (σ.o r) (ρ.o r)
      obtain ⟨X, K, hXo, hcl', hle⟩ := hseed
      have hrM : r < M.length := by omega
      have hor := o_cl_eq hC hG hrM
      have harg := arg_lt_of_cl hC hG hrM hrCL
      rw [hXo]
      rw [hor] at hle ⊢
      exact seed_closed (by rw [← hor]; exact hG.ot_o r hrM) (ne_of_gt harg) hcl' hle
    · subst hb; rw [hi']
      show Lhd z (σ.v (r + L - 1)) (ρ.v (r + L - 1))
      apply v_xm1_lhd hlen hL hn2 hu hZ2 he2r hC hG hCN _ (upgN_xm1_none hlen hL hp hd0e hn2 hu he2r)
      rw [par_gexp_pre hlen (by omega) 1 (by omega)]
      cases hm : par M 1 (r + L - 1) with
      | none => rfl
      | some m =>
        show σ.v m = ρ.v m
        exact (hoff m (by have := par_lt M 1 _ m hm; omega)).2 (hP1 m hm)
  exact t2_assemble (S := SV r (r + L - 1)) (W := fun _ _ => False) (bnd := r + L) hC hG hRM hCN hGN hRN
    hF hVS hTD hKD hR01 hR12 h00 hlen (by rw [hlN]; omega) (fun i hi _ => hchN i hi)
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
    (fun j hj0 hj => by
      have := e0_NQ_pos (d1 := d1) (qp := 0) hlen hL hA hp hL hd0e hn2 hj0 (by rw [hlN] at hj; exact hj)
      omega)
    (by have := anc0_e0_lt hA (by omega); omega)
    (fun i h => h.elim) (fun i h => h) (fun i c _ _ h => h.elim) (fun i j c _ _ _ _ _ h => h.elim)
    (fun c hc _ hd => hDvNil c hc hd)
    hCLnil (fun i hi hns _ hD hv => hOS i hi hns hD hv) hVSh hRD (fun i _ h => h.elim) hAbs hVNN hSeed

end

end Ytosk
