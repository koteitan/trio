/-
The retained t=2 frame fields from the repaired below-boundary engine.
PV2 is sufficient throughout; the false Res3W interface is not assumed.
PH3cG and FC3 take their actual seed-frame inputs, not old StepCtxT2.
-/
import Ytosk.V3T2RootV3U
import Ytosk.V3T2FieldsV3
import Ytosk.WfT2R3

namespace Ytosk.WfT2X
open T Classical WfAbsW

/-- `clField_of_shapeX` for the foreign-allowance fifth frame shape. -/
theorem clField_of_shapeXU {Q : T → List T → T → Prop}
    (hQlow : ∀ a Lv cv cv', Q a Lv cv → Lhd z cv' cv → isOT cv' = true → Q a Lv cv')
    (hQlowV : ∀ a Lv s s', Q a Lv (psi s z z) → Lhd a (psi s' z z) (psi s z z) →
      isOT (psi s' z z) = true → Q a Lv (psi s' z z))
    (hQlowVG : ∀ (V : T) a Lv s s', Q a Lv (psi s z z) → Lhd V (psi s' z z) (psi s z z) →
      (∀ u, ∀ g ∈ comps u V, g < psi s' z z) → isOT (psi s' z z) = true → Q a Lv (psi s' z z))
    {M N : Mat} {ρ σ : Valn} {i : Nat} (hS : FrameShapeXU M N ρ σ i)
    (hOT : ∀ d ∈ CL N i, isOT (σ.o d) = true)
    (hQ : ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R →
      Q (ρ.v i) (Lc.map ρ.o) (ρ.o c)) :
    ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL N i = Lc ++ c :: R →
      Q (σ.v i) (Lc.map σ.o) (σ.o c) := by
  rcases hS with hS | ⟨hv, Lc0, c0, V, hclM, hclN, hsame, hoN, hoM,
      hVl, hOl, hsm, _⟩
  · exact clField_of_shapeX hQlow hQlowV hS hOT hQ
  intro Lc c R hCL
  have hcN : c ∈ CL N i := by rw [hCL]; simp
  rcases shape4_split hclM hclN hsame hCL with ⟨rfl, rfl, rfl⟩ | ⟨hCLM, hLm, hoc⟩
  · have hq := hQ Lc c [] hclM
    rw [hoM] at hq
    have hot := hOT c hcN
    rw [hoN] at hot ⊢
    rw [hv, List.map_congr_left hsame]
    rw [hoN, hoM] at hOl
    have hsm' : ∀ u, ∀ g ∈ comps u V, g < psi (σ.v c) z z := by
      simpa only [hoN] using hsm
    exact hQlowVG V _ _ _ _ hq hOl hsm' hot
  · rw [hv, hLm, hoc]
    exact hQ Lc c R hCLM

end Ytosk.WfT2X

namespace Ytosk.V3Main
open T Classical WfExQ1 WfT2X WfAbsW G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The foreign-allowance lowering needed by the new fifth frame shape. -/
theorem qFC_lowVG : ∀ (V : T) a Lv s s', QFC a Lv (psi s z z) → Lhd V (psi s' z z) (psi s z z) →
    (∀ u, ∀ g ∈ comps u V, g < psi s' z z) → isOT (psi s' z z) = true → QFC a Lv (psi s' z z) := by
  intro V a Lv s s' _ _ _ _ s0 y0 h ht
  simp only [psi.injEq] at h
  rw [← h.2.1] at ht
  exact absurd ht.1 (T.not_lt_z _)

theorem qFO_lowVG : ∀ (V : T) a Lv s s', QFO a Lv (psi s z z) → Lhd V (psi s' z z) (psi s z z) →
    (∀ u, ∀ g ∈ comps u V, g < psi s' z z) → isOT (psi s' z z) = true → QFO a Lv (psi s' z z) :=
  fun _ _ _ _ _ h _ _ _ => h

theorem qT2F_lowVG : ∀ (V : T) a Lv s s', QT2F a Lv (psi s z z) → Lhd V (psi s' z z) (psi s z z) →
    (∀ u, ∀ g ∈ comps u V, g < psi s' z z) → isOT (psi s' z z) = true → QT2F a Lv (psi s' z z) := by
  intro V a Lv s s' h _ _ _
  refine ⟨h.1, ?_⟩
  intro s0 y0 c0 hc ht
  simp only [psi.injEq] at hc
  rw [← hc.2.1] at ht
  exact absurd ht.1 (T.not_lt_z _)

theorem qT2P_lowVG : ∀ (V : T) a Lv s s', QT2P a Lv (psi s z z) → Lhd V (psi s' z z) (psi s z z) →
    (∀ u, ∀ g ∈ comps u V, g < psi s' z z) → isOT (psi s' z z) = true → QT2P a Lv (psi s' z z) := by
  intro V a Lv s s' h _ _ _
  refine ⟨h.1, ?_⟩
  intro s0 y0 c0 hc ht
  simp only [psi.injEq] at hc
  rw [← hc.2.1] at ht
  exact absurd ht.1 (T.not_lt_z _)

theorem clField_expand_t2V3U {Q : T → List T → T → Prop}
    (hQσ : ∀ (V V' a : T) (Lv : List T) (cv : T), isOT V = true → isOT V' = true → V < V' →
      isOT a = true → V ≤ a → (∀ t ∈ Lv ++ [cv], Single t) →
      (Lv ++ [cv]).Pairwise (fun a b => b ≤ a) → (V < a ∨ ∀ t ∈ Lv ++ [cv], V < lev t) →
      Q a Lv cv → Q (shf V V' a) (Lv.map (sh V V')) (sh V V' cv))
    (hQlow : ∀ a Lv cv cv', Q a Lv cv → Lhd z cv' cv → isOT cv' = true → Q a Lv cv')
    (hQlowV : ∀ a Lv s s', Q a Lv (psi s z z) → Lhd a (psi s' z z) (psi s z z) → isOT (psi s' z z) = true →
      Q a Lv (psi s' z z))
    (hQlowVG : ∀ (V : T) a Lv s s', Q a Lv (psi s z z) → Lhd V (psi s' z z) (psi s z z) →
      (∀ u, ∀ g ∈ comps u V, g < psi s' z z) → isOT (psi s' z z) = true → Q a Lv (psi s' z z))
    {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowAtV3U M ρ) (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (D : DropV3 M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) (hQM : CLField Q M ρ)
    (hQT : ∀ τ, Cons (M.take (M.length - 1)) τ → CLField Q (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames Q M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → CLField Q (expand M n) σ := by
  have hGall := good3_expand_t2V3 hM hS I D hz h2 (t2BelowXE_V3U hB hM hS I D hz h2)
    (t2CopyResV3 hM hS I hz h2)
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  rw [h2] at hr
  have hrx : r < M.length - 1 := par_lt M 2 _ r hr
  have hlen2 : 2 ≤ M.length := by omega
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hlen : r + L + 1 = M.length := by omega
  have hL0 : 0 < L := by omega
  rw [hL] at hr hQT
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd0 : 0 < d0 := by omega
  have hd1 : 0 < d1 := by omega
  have hexp : ∀ n, expand M n = TRIO.gexp M r L d0 d1 n := by
    intro n
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hG : ∀ m, 1 ≤ m → ∀ σ, Cons (TRIO.gexp M r L d0 d1 m) σ → Good3 (TRIO.gexp M r L d0 d1 m) σ :=
    fun m hm σ hσ => by rw [← hexp m] at hσ ⊢; exact hGall m hm σ hσ
  have hRk : ∀ m, 1 ≤ m → ∃ rk, Rk (TRIO.gexp M r L d0 d1 m) rk := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  have hBE : ∀ m, 1 ≤ m → BumpE2 (TRIO.gexp M r L d0 d1 m) := fun m _ => by
    rw [← hexp m]; exact (sInvX_expand hX m).loc.2.2.1
  have hCR := t2CopyResV3 hM hS I hz h2 r L hlen hr
  have hBS := t2BelowXS_V3U hB hM hS I D hz h2 hlen hr
  have hSD := hX.loc.1
  have key : ∀ n, 1 ≤ n → ∀ σ, Cons (TRIO.gexp M r L d0 d1 n) σ → CLField Q (TRIO.gexp M r L d0 d1 n) σ := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        intro σ hσ
        rw [gexp_one_gen hlen] at hσ ⊢
        exact hQT σ hσ
      · intro σ hCN
        have hn2 : 2 ≤ m + 1 := by omega
        obtain ⟨rkP, hRP⟩ := hRk m hm0
        have hCP : Cons (TRIO.gexp M r L d0 d1 m) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
        have hGP := hG m hm0 _ hCP
        have hQP := ih hm0 _ hCP
        have hm : m + 1 - 1 = m := by omega
        obtain ⟨hKV, hB', hV', hVV⟩ := hCR (m + 1) hn2 σ _ hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP)
        have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r (by rw [hm]; exact hBE m hm0)
        have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r hX.r0p hSD
        have hF := copy_facts_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r (by rw [hm]; exact hBE m hm0)
          hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP) (by rw [hm]; exact hRP) hK hKV hRK hB' hV' hVV
        rw [hm] at hF
        have hlN : (TRIO.gexp M r L d0 d1 (m + 1)).length = r + (m + 1) * L := TRIO.gexp_length hlen
        have hlP : (TRIO.gexp M r L d0 d1 m).length = r + m * L := TRIO.gexp_length hlen
        have hmL : (m + 1) * L = m * L + L := Nat.succ_mul m L
        have hrP : r < (TRIO.gexp M r L d0 d1 m).length := by
          have : L ≤ m * L := Nat.le_mul_of_pos_left L hm0
          omega
        have hcopy := clField_copy hQσ hF hCP hGP hrP hV' hVV hQP
        have hGN := hG (m + 1) (by omega) σ hCN
        intro i hi Lc c R hCL
        rcases Nat.lt_or_ge i (r + L) with hix | hix
        · by_cases hsc : T2SeedCol M r L i
          · exact hSeed r L hlen hr (m + 1) hn2 (fun k hk1 _ τ hτ => hG k hk1 τ hτ) σ hCN hGN i hsc Lc c R hCL
          · have hsh := (hBS (m + 1) hn2 (fun k hk1 _ τ hτ => hG k hk1 τ hτ) σ hCN (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩) i hix).2.2.2.1 hsc
            exact WfT2X.clField_of_shapeXU hQlow hQlowV hQlowVG hsh
              (fun d hd => hGN.ot_o d (mem_children (cl_mem_children hd)).2) (fun Lc c R h => hQM i (by omega) Lc c R h) Lc c R hCL
        · obtain ⟨a, rfl⟩ : ∃ a, i = r + a + L := ⟨i - L - r, by omega⟩
          exact hcopy (r + a) (by omega) (by omega) Lc c R hCL
  intro n hn σ hσ
  rw [hexp n] at hσ ⊢
  exact key n hn σ hσ


theorem frameOT_expand_t2V3U {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowAtV3U M ρ)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (D : DropV3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ → FrameOT (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames QFO M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → FrameOT (expand M n) σ :=
  clField_expand_t2V3U qFO_sh (fun _ _ _ _ h _ _ => h) WfT2X.qFO_lowV qFO_lowVG
    hB hM hS I D hz h2 I.fo hT hSeed


theorem bumpFields_expand_t2V3U {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowAtV3U M ρ)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (D : DropV3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ →
      BumpKidsDec (M.take (M.length - 1)) τ ∧ BumpTermDec (M.take (M.length - 1)) τ)
    (hSeed : T2SeedBump M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → BumpKidsDec (expand M n) σ ∧ BumpTermDec (expand M n) σ := by
  have hGall := good3_expand_t2V3 hM hS I D hz h2 (t2BelowXE_V3U hB hM hS I D hz h2)
    (t2CopyResV3 hM hS I hz h2)
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  rw [h2] at hr
  have hrx : r < M.length - 1 := par_lt M 2 _ r hr
  have hlen2 : 2 ≤ M.length := by omega
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hlen : r + L + 1 = M.length := by omega
  have hL0 : 0 < L := by omega
  rw [hL] at hr hT
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hd0 : 0 < d0 := by omega
  have hd1 : 0 < d1 := by omega
  have hexp : ∀ n, expand M n = TRIO.gexp M r L d0 d1 n := by
    intro n
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hG : ∀ m, 1 ≤ m → ∀ σ, Cons (TRIO.gexp M r L d0 d1 m) σ → Good3 (TRIO.gexp M r L d0 d1 m) σ :=
    fun m hm σ hσ => by rw [← hexp m] at hσ ⊢; exact hGall m hm σ hσ
  have hRk : ∀ m, 1 ≤ m → ∃ rk, Rk (TRIO.gexp M r L d0 d1 m) rk := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  have hXG : ∀ m, SInvX (TRIO.gexp M r L d0 d1 m) := fun m => by rw [← hexp m]; exact sInvX_expand hX m
  have hCR := t2CopyResV3 hM hS I hz h2 r L hlen hr
  have hBS := t2BelowXS_V3U hB hM hS I D hz h2 hlen hr
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hqx := par_lt M 0 _ _ hq
  have hxbr : col M (r + L) ≠ bump M r := fun h => by
    have := e1_of_col (show col M (r + L) = (entry M 0 r + 1, entry M 1 r, 1) from h); omega
  -- a bump child of a column before `x`, other than a `v`-seed, is before `x`
  have hjx : ∀ i j, i < r + L → ¬ T2VSeedCol M r L i → j ∈ children M i → col M j = bump M i → j < r + L := by
    intro i j hi hns hj hjb
    have := (mem_children hj).2
    by_contra h'
    have hjx' : j = r + L := by omega
    have hpj := (mem_children_iff.mp hj).2
    rw [hjx', hq] at hpj
    have hiq : q = i := Option.some.inj hpj
    by_cases hqr : q = r
    · rw [hjx', ← hiq, hqr] at hjb; exact hxbr hjb
    · exact hns (Or.inl ⟨q, hq, hqr, hiq.symm⟩)
  have key : ∀ n, 1 ≤ n → ∀ σ, Cons (TRIO.gexp M r L d0 d1 n) σ → ∀ i, BumpAt (TRIO.gexp M r L d0 d1 n) σ i := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        intro σ hσ i
        rw [gexp_one_gen hlen] at hσ ⊢
        obtain ⟨hk, ht⟩ := hT σ hσ
        exact ⟨fun h1 h2 => hk i h1 h2, fun h1 h2 => ht i h1 h2⟩
      · intro σ hCN
        have hn2 : 2 ≤ m + 1 := by omega
        have hm1 : 1 ≤ m + 1 := by omega
        obtain ⟨rkP, hRP⟩ := hRk m hm0
        have hCP : Cons (TRIO.gexp M r L d0 d1 m) (rhsIt _ (rkBound _ rkP)) := cons_of_rk hRP
        have hGP := hG m hm0 _ hCP
        have hBP := ih hm0 _ hCP
        have hm : m + 1 - 1 = m := by omega
        obtain ⟨hKV, hB', hV', hVV⟩ := hCR (m + 1) hn2 σ _ hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP)
        have hBEP : BumpE2 (TRIO.gexp M r L d0 d1 m) := (hXG m).loc.2.2.1
        have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r (by rw [hm]; exact hBEP)
        have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r hX.r0p hX.loc.1
        have hF := bump_copy_facts_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r (by rw [hm]; exact hBEP)
          hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP) (by rw [hm]; exact hRP) hK hKV hRK hB' hV' hVV
        rw [hm] at hF
        have hlN : (TRIO.gexp M r L d0 d1 (m + 1)).length = r + (m + 1) * L := TRIO.gexp_length hlen
        have hlP : (TRIO.gexp M r L d0 d1 m).length = r + m * L := TRIO.gexp_length hlen
        have hmL : (m + 1) * L = m * L + L := Nat.succ_mul m L
        have hrP : r < (TRIO.gexp M r L d0 d1 m).length := by
          have : L ≤ m * L := Nat.le_mul_of_pos_left L hm0
          omega
        have he2rP : entry (TRIO.gexp M r L d0 d1 m) 2 r = 0 := by
          rw [entry_gexp_pre hlen hm0 2 (by omega)]; exact he2r
        have hcopy := bump_copy hF hGP hrP hV' hVV (hXG m).r12 he2rP
          (fun i h1 h2 => (hBP i).1 h1 h2) (fun i h1 h2 => (hBP i).2 h1 h2)
        have hGN := hG (m + 1) hm1 σ hCN
        intro i
        rcases Nat.lt_or_ge i (r + L) with hix | hix
        · by_cases hsc : T2VSeedCol M r L i
          · exact hSeed r L hlen hr (m + 1) hn2 σ hCN hGN i hsc
          · have hinfo := fun h1 h2 =>
              (hBS (m + 1) hn2 (fun k hk1 _ τ hτ => hG k hk1 τ hτ) σ hCN (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩) i hix).2.2.2.2.2 hsc h1 h2
            apply bump_below (x := r + L) I.good hCN I.kd I.td (entry_gexp_pre hlen hm1 1 hix)
              (entry_gexp_pre hlen hm1 2 hix) (children_N2g hlen hL0 hA hq hd0e hn2 hix)
              (fun j _ hjx' => children_N2g hlen hL0 hA hq hd0e hn2 hjx')
              _ (fun j hj hjb => hjx i j hix hsc hj hjb) hinfo
            intro j hj
            rcases Nat.lt_or_ge j (r + L) with hjx' | hjx'
            · rw [col_gexp_pre hlen hm1 hjx']
              unfold bump; rw [entry_gexp_pre hlen hm1 0 hix, entry_gexp_pre hlen hm1 1 hix]
            · have hjeq : j = r + L := by have := (mem_children hj).2; omega
              subst hjeq
              constructor
              · intro h
                have := (bump_eq h).2.2
                have h2' : (col (TRIO.gexp M r L d0 d1 (m + 1)) (r + L)).2.2 =
                    entry (TRIO.gexp M r L d0 d1 (m + 1)) 2 (r + L) := rfl
                rw [h2', (entry_xprime_g (d1 := d1) hlen hL0 hA hq hd0e hn2).1, he2r] at this; omega
              · intro h; exact absurd (hjx i (r + L) hix hsc hj h) (lt_irrefl _)
        · rcases Nat.lt_or_ge i (r + (m + 1) * L) with hiN | hiN
          · obtain ⟨a, rfl⟩ : ∃ a, i = r + a + L := ⟨i - L - r, by omega⟩
            exact hcopy (r + a) (by omega) (by omega)
          · exact bumpAt_out (by omega)
  intro n hn σ hσ
  rw [hexp n] at hσ ⊢
  exact bump_fields_of (key n hn σ hσ)


theorem rootP_expand_t2V3U {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowAtV3U M ρ)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (D : DropV3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2) :
    ∀ n, 2 ≤ n → ∀ σ, Cons (expand M n) σ → RootP (expand M n) σ := by
  have hGall := good3_expand_t2V3 hM hS I D hz h2 (t2BelowXE_V3U hB hM hS I D hz h2)
    (t2CopyResV3 hM hS I hz h2)
  obtain ⟨hX, hJ⟩ := sInvXJ_std hM hS
  obtain ⟨r, hr⟩ := parLast_of hX.e00 hX.r01 hX.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  rw [h2] at hr
  have hrx : r < M.length - 1 := par_lt M 2 _ r hr
  have hlen2 : 2 ≤ M.length := by omega
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  have hlen : r + L + 1 = M.length := by omega
  have hL0 : 0 < L := by omega
  have hz0 := hz
  rw [hL] at hr hz
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  set d0 := entry M 0 (r + L) - entry M 0 r with hd0def
  set d1 := entry M 1 (r + L) - entry M 1 r with hd1def
  have hd0e : entry M 0 (r + L) = entry M 0 r + d0 := by omega
  have hexp : ∀ n, expand M n = TRIO.gexp M r L d0 d1 n := by
    intro n
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hqx := par_lt M 0 _ _ hq
  have hrq : Anc0 M r q := anc0_par hA (by omega) hq
  have hrq' : r ≤ q := hrq.le
  have hqb : ∀ i, par M 0 q = some i → col M q ≠ bump M i := by
    intro i hi
    by_cases hqr : q = r
    · intro h
      rw [hqr] at h
      have := e2_of_col (show col M r = (entry M 0 i + 1, entry M 1 i, 1) from h); omega
    · obtain ⟨pq, hpq⟩ := par0_of_anc hrq (Ne.symm hqr)
      have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
      have hpq' : par M 0 (r + (q - r)) = some pq := by rw [show r + (q - r) = q by omega]; exact hpq
      obtain ⟨_, Tqb, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
      rw [hpq] at hi; cases hi
      rwa [show r + (q - r) = q by omega] at Tqb
  have hBS := t2BelowXS_V3U hB hM hS I D hz0 h2 hlen hr
  intro n hn σ hCN
  rw [hexp n] at hCN ⊢
  set N := TRIO.gexp M r L d0 d1 n with hN
  have hlN : N.length = r + n * L := TRIO.gexp_length hlen
  have hnL2 : 2 * L ≤ n * L := Nat.mul_le_mul_right L hn
  have hm1 : 1 ≤ n := by omega
  have hGN : Good3 N σ := by have := hGall n hm1 σ (by rw [hexp n]; exact hCN); rwa [hexp n] at this
  obtain ⟨rkN, hRN⟩ : ∃ rk, Rk N rk := by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz0 h2 I.rank n hm1
    rw [hexp n] at h'; exact ⟨rk', h'⟩
  have hUN : UAT N := by rw [hN, ← hexp n]; exact (sInvX_expand hX n).toSInv.uat
  -- row 0 is positive from `x` on
  have hpos : ∀ j, r + L ≤ j → j < N.length → entry N 0 j ≠ 0 := by
    intro j hj1 hj2
    have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
    have := e0_NQ_pos (d1 := d1) hlen hL0 hA hq' (by omega) hd0e hn hj1 (by rw [hlN] at hj2; exact hj2)
    exact Nat.pos_iff_ne_zero.mp this
  have hroots : roots N = roots M := by
    apply roots_eq (N := N) (x := r + L) hlen (by omega) (fun c hc => col_gexp_pre hlen hm1 hc) hz
    intro c hc1 hc2 h
    apply hpos c hc1 hc2
    unfold entry; unfold col at h; rw [h]; rfl
  -- the last root above `x`
  obtain ⟨Rt, hRA, hR0e, hRlast⟩ := root_exists hX.e00 (r + L)
  have hR0 : col M Rt = (0, 0, 0) := by
    have h1 : entry M 1 Rt = 0 := hX.r01 Rt hR0e
    exact (col_zero_iff M Rt).mpr ⟨hR0e, h1, hX.r12 Rt h1⟩
  have hRle : ∀ a, Anc0 M a (r + L) → Rt ≤ a := by
    intro a ha
    rcases anc0_total ha hRA with h | h
    · by_cases hae : a = Rt
      · omega
      · have := anc0_e0_lt h hae; omega
    · exact h.le
  have hRtr : Rt ≤ r := hRle r hA
  have hRtq : Rt ≤ q := hRle q (Anc0.step hq (Anc0.refl q))
  -- calls before `Rt` do not depend on the seeds of `N`
  have hnd : ∀ c, c < Rt → ¬ DepS N (SN M r (r + L) q) true c := by
    intro c hc hd
    have hR0N : entry N 0 Rt = 0 := by rw [entry_gexp_pre hlen hm1 0 (by have := hRA.le; omega)]; exact hR0e
    have hRlastN : ∀ j, Rt < j → j ≤ N.length - 1 → entry N 0 j ≠ 0 := by
      intro j h1 h2'
      rcases Nat.lt_or_ge j (r + L) with hj | hj
      · rw [entry_gexp_pre hlen hm1 0 hj]; exact hRlast j h1 (by omega)
      · exact hpos j hj (by omega)
    have hSge : ∀ b i, SN M r (r + L) q b i → Rt ≤ i := by
      rintro b i (⟨_, rfl⟩ | ⟨_, rfl, _⟩ | ⟨_, hqr, hpi⟩ | ⟨_, hix, _⟩)
      · exact hRtq
      · exact hRtq
      · exact hRle i (Anc0.step hq (Anc0.step hpi (Anc0.refl i)))
      · omega
    have := depS_ge (show N.length - 1 + 1 = N.length by omega) hR0N hRlastN hSge hd
    omega
  have hag := agree_N hlen hL0 hA hq hd0e hn he2r h1lt hqb hX.toSInv.uat hUN I.cons hCN hRN
  have hle : σ.o Rt ≤ ρ.o Rt := by
    have hRx : Rt < r + L := by have := hRA.le; have : Rt ≠ r + L := fun h => by rw [h] at hR0; exact hz hR0
                                omega
    refine (hBS n hn (fun k hk1 _ τ hτ => by
        have := hGall k hk1 τ (by rw [hexp k]; exact hτ)
        rwa [hexp k] at this) σ hCN (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩) Rt hRx).2.2.2.2.1 ?_
    intro q' hq' hqr' hRq
    rw [hq] at hq'; cases hq'
    -- `q ≠ r` has row 2 equal to `1`, a root has row 2 equal to `0`
    obtain ⟨pq, hpq⟩ := par0_of_anc hrq (Ne.symm hqr')
    have hq' : par M 0 (r + L) = some (r + (q - r)) := by rw [show r + (q - r) = q by omega]; exact hq
    have hpq' : par M 0 (r + (q - r)) = some pq := by rw [show r + (q - r) = q by omega]; exact hpq
    obtain ⟨Txb, _⟩ := t2_qn_struct hX hJ hlen hr hq' (by omega) hpq'
    rw [show r + (q - r) = q by omega] at Txb
    have he2q := hX.loc.2.2.1 q (r + L) (mem_children_iff.mpr ⟨by omega, hq⟩) Txb
    rw [← hRq, e2_of_col hR0] at he2q; omega
  have hsplit := roots_split (show r + L + 1 = M.length from hlen) hRA hR0
  set pre := (roots M).filter (fun c => decide (c < Rt)) with hpre
  have hpre_lt : ∀ c ∈ pre, c < Rt := by
    intro c hc; rw [hpre, List.mem_filter] at hc; simpa using hc.2
  have hNm : (roots N).map σ.o = pre.map ρ.o ++ [σ.o Rt] := by
    rw [hroots, hsplit, List.map_append, List.map_singleton]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact (hag c (by have := hpre_lt c hc; have := hRA.le; omega)).1 (hnd c (hpre_lt c hc))
  have hMm : (roots M).map ρ.o = pre.map ρ.o ++ [ρ.o Rt] := by
    rw [hsplit, List.map_append, List.map_singleton]
  have hpM : RootP M ρ := I.rootP
  unfold RootP at hpM ⊢
  rw [hMm] at hpM
  rw [hNm]
  rw [List.pairwise_append] at hpM ⊢
  refine ⟨hpM.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
  rw [List.mem_singleton] at hb; subst hb
  exact le_trans hle (hpM.2.2 a ha _ (List.mem_singleton_self _))


theorem fc3_expand_t2V3U {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowAtV3U M ρ)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (D : DropV3 M ρ rk) (hP : FC3 M ρ)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ →
      FrameOT (M.take (M.length - 1)) τ ∧ FC3 (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames QT2F M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → FC3 (expand M n) σ := by
  intro n hn σ hσ
  apply fc3_of_clField
  exact clField_expand_t2V3U (fun V V' a Lv cv hV hV' hVV ha hVa hs hp hlev hQ =>
      qT2F_sh hV hV' hVV ha hVa hs hp hlev hQ)
    qT2F_low qT2F_lowVXR qT2F_lowVG hB hM hS I D hz h2 (clField_qT2F I.cons I.fo hP)
    (fun τ hτ => clField_qT2F hτ (hT τ hτ).1 (hT τ hτ).2) hSeed n hn σ hσ


theorem ph3c_expand_t2V3U {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowAtV3U M ρ)
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (D : DropV3 M ρ rk) (hP : PH3cG M ρ)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ →
      FrameOT (M.take (M.length - 1)) τ ∧ PH3cG (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames QT2P M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → PH3cG (expand M n) σ := by
  intro n hn σ hσ
  apply ph3c_of_clField
  exact clField_expand_t2V3U (fun V V' a Lv cv hV hV' hVV ha hVa hs hp hlev hQ =>
      qT2P_sh hV hV' hVV ha hVa hs hp hlev hQ)
    qT2P_low qT2P_lowVXR qT2P_lowVG hB hM hS I D hz h2 (clField_qT2P I.cons I.fo hP)
    (fun τ hτ => clField_qT2P hτ (hT τ hτ).1 (hT τ hτ).2) hSeed n hn σ hσ


end Ytosk.V3Main
