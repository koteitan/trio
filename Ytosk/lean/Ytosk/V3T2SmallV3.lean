/-
The three remaining t=2 carried fields from their seed and copy consumers.
These are the existing component conditions at actual frames; no old Res3W,
Inv3V2, or additional term guard is assumed.
-/
import Ytosk.V3T2FieldsV3

namespace Ytosk.V3Main
open T Classical WfExQ1 WfT2X WfAbsW G
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- Good3 on the prefix for any consistent valuation, using the repaired drop. -/
theorem good3_take_anyV3 {M : Mat} {ρ τ : Valn} {rk : Bool → Nat → Nat}
    (I : Inv3W M ρ rk) (D : DropV3 M ρ rk) (hl : 1 ≤ M.length)
    (hτ : Cons (M.take (M.length - 1)) τ) : Good3 (M.take (M.length - 1)) τ := by
  obtain ⟨hC, hR, hG, _⟩ := t2_drop_ctxV3 I D (show M.length - 1 + 1 = M.length by omega)
  exact good3_congr hG (agree_of_cons hC hτ hR)

theorem vsmallF_expand_t2V3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowAtV3 M ρ) (hM : Std M)
    (hS : M ≠ SRO) (I : Inv3W M ρ rk) (D : DropV3 M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2)
    (hQT : ∀ τ, Cons (M.take (M.length - 1)) τ → CLField QVSF (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames QVSF M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → CLField QVSF (expand M n) σ := by
  have hGall := good3_expand_t2V3 hM hS I D hz h2 (t2BelowXE_V3 hB hM hS I D hz h2)
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
  have hBS := t2BelowXS_V3 hB hM hS I D hz h2 hlen hr
  have hSD := hX.loc.1
  have key : ∀ n, 1 ≤ n → ∀ σ, Cons (TRIO.gexp M r L d0 d1 n) σ → CLField QVSF (TRIO.gexp M r L d0 d1 n) σ := by
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
        have hcopy := clField_copy qVSF_sh hF hCP hGP hrP hV' hVV hQP
        have hGN := hG (m + 1) (by omega) σ hCN
        intro i hi Lc c R hCL
        rcases Nat.lt_or_ge i (r + L) with hix | hix
        · by_cases hsc : T2SeedCol M r L i
          · exact hSeed r L hlen hr (m + 1) hn2 (fun k hk1 _ τ hτ => hG k hk1 τ hτ) σ hCN hGN i hsc Lc c R hCL
          · have hsh := (hBS (m + 1) hn2 (fun k hk1 _ τ hτ => hG k hk1 τ hτ) σ hCN (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩) i hix).2.2.2.1 hsc
            exact WfT2X.qVSF_of_shapeX I.cons I.good hCN hGN (by omega) hsh I.vs Lc c R hCL
        · obtain ⟨a, rfl⟩ : ∃ a, i = r + a + L := ⟨i - L - r, by omega⟩
          exact hcopy (r + a) (by omega) (by omega) Lc c R hCL
  intro n hn σ hσ
  rw [hexp n] at hσ ⊢
  exact key n hn σ hσ


theorem vsmallF_expand_t2VV3 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowAtV3 M ρ) (hM : Std M)
    (hS : M ≠ SRO) (I : Inv3W M ρ rk) (D : DropV3 M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ → Good3 (M.take (M.length - 1)) τ ∧ VSmallF (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames QVSF M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → Good3 (expand M n) σ → VSmallF (expand M n) σ := by
  intro n hn σ hσ hG
  exact vsmallF_of_clField hσ hG (vsmallF_expand_t2V3 hB hM hS I D hz h2
    (fun τ hτ => clField_of_vsmallF hτ (hT τ hτ).1 (hT τ hτ).2) hSeed n hn σ hσ)


theorem clField_expand_t2SKV3 {Q : T → List T → T → Prop} {K : T → T → T → List T → T → Prop}
    (hQσ : ∀ (V V' a : T) (Lv : List T) (cv : T), isOT V = true → isOT V' = true → V < V' →
      isOT a = true → V ≤ a → (∀ t ∈ Lv ++ [cv], Single t) →
      (Lv ++ [cv]).Pairwise (fun a b => b ≤ a) → (V < a ∨ ∀ t ∈ Lv ++ [cv], V < lev t) →
      K V V' a Lv cv → Q a Lv cv → Q (shf V V' a) (Lv.map (sh V V')) (sh V V' cv))
    (hQlow : ∀ a Lv cv cv', Q a Lv cv → Lhd z cv' cv → isOT cv' = true → (∃ s y, cv = psi s y z) →
      (∀ s y s' y', cv = psi s y z → cv' = psi s' y' z → s' ≠ s → y' = z) → Q a Lv cv')
    (hQlowV : ∀ a Lv s s', Q a Lv (psi s z z) → Lhd a (psi s' z z) (psi s z z) → isOT (psi s' z z) = true →
      Q a Lv (psi s' z z))
    {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowAtV3 M ρ) (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (D : DropV3 M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) (hQM : CLField Q M ρ)
    (hQT : ∀ τ, Cons (M.take (M.length - 1)) τ → CLField Q (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames Q M) (hKM : T2CopyK K M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → CLField Q (expand M n) σ := by
  have hGall := good3_expand_t2V3 hM hS I D hz h2 (t2BelowXE_V3 hB hM hS I D hz h2)
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
  have hBS := t2BelowXS_V3 hB hM hS I D hz h2 hlen hr
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
        have hcopy := clField_copyK hQσ hF hCP hGP hrP hV' hVV hQP (by
          intro i hri hi hg Lc c R hCL
          have := hKM r L hlen hr (m + 1) hn2 σ _ hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP) i hri
            (by rw [hm]; exact hi) (by rw [hm]; exact hg) Lc c R (by rw [hm]; exact hCL)
          exact this)
        have hGN := hG (m + 1) (by omega) σ hCN
        intro i hi Lc c R hCL
        rcases Nat.lt_or_ge i (r + L) with hix | hix
        · by_cases hsc : T2SeedCol M r L i
          · exact hSeed r L hlen hr (m + 1) hn2 (fun k hk1 _ τ hτ => hG k hk1 τ hτ) σ hCN hGN i hsc Lc c R hCL
          · have hsh := (hBS (m + 1) hn2 (fun k hk1 _ τ hτ => hG k hk1 τ hτ) σ hCN (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩) i hix).2.2.2.1 hsc
            exact WfT2X.clField_of_shapeSX hQlow hQlowV I.cons I.good hCN hGN hsh (fun Lc c R h => hQM i (by omega) Lc c R h)
              Lc c R hCL
        · obtain ⟨a, rfl⟩ : ∃ a, i = r + a + L := ⟨i - L - r, by omega⟩
          exact hcopy (r + a) (by omega) (by omega) Lc c R hCL
  intro n hn σ hσ
  rw [hexp n] at hσ ⊢
  exact key n hn σ hσ


theorem frameClosed_expand_t2KV3 {M : Mat} {ρ : Valn}
    {rk : Bool → Nat → Nat} (hB : T2BelowAtV3 M ρ) (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (D : DropV3 M ρ rk)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ → FrameClosed (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames QFC M) (hK : T2CopyK FDshAt M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → FrameClosed (expand M n) σ := by
  have hl : 1 ≤ M.length := by
    rcases Nat.eq_zero_or_pos M.length with h | h
    · exfalso; apply hz; rw [h]
      have : M = [] := List.eq_nil_of_length_eq_zero h
      subst this; rfl
    · exact h
  have hSeed' : T2SeedFrames QFCo M := by
    intro r L hlen hr n hn hGm σ hCN hGN i hsc Lc c R hCL
    have hcN := (mem_children (cl_mem_children (show c ∈ CL _ i by rw [hCL]; simp))).2
    exact ⟨hGN.ot_o c hcN, hSeed r L hlen hr n hn hGm σ hCN hGN i hsc Lc c R hCL⟩
  have key := clField_expand_t2SKV3 (K := FDshAt) (fun V V' a Lv cv hV hV' hVV ha hVa hs hp hlev hK hQ =>
      qFCo_shK V V' a Lv cv hV hV' hVV ha hVa hs hp hlev hK hQ) qFCo_low WfT2X.qFCo_lowV hB hM hS I D hz h2
    (clField_QFCo I.good I.fc) (fun τ hτ => clField_QFCo (good3_take_anyV3 I D hl hτ) (hT τ hτ)) hSeed' hK
  exact fun n hn σ hσ => frameClosed_of_QFCo (key n hn σ hσ)


theorem vsmallRAll_expand_t2V3 {K : T → T → T → List T → T → T → Prop} (hsh : QVRAshK K) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowAtV3 M ρ)
    (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (D : DropV3 M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) (hVM : VSmallRAll M ρ)
    (hVT : ∀ τ, Cons (M.take (M.length - 1)) τ → VSmallRAll (M.take (M.length - 1)) τ)
    (hSeed : T2VRASeed M) (hPre : T2VRAPre M ρ) (hCopy : T2VRACopyEsc M) (hKM : T2VRAK K M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → VSmallRAll (expand M n) σ := by
  have hGall := good3_expand_t2V3 hM hS I D hz h2 (t2BelowXE_V3 hB hM hS I D hz h2)
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
  rw [hL] at hr hVT
  have hA : Anc0 M r (r + L) := anc0_of_par M 2 r (r + L) hr
  have he0lt := anc0_e0_lt hA (by omega)
  obtain ⟨he2r, h1lt⟩ := par2_facts hX.z2 (by omega) hr
  have hgx : TRIO.le1 M r (r + L) := by
    obtain ⟨_, _, _, _, hle, _⟩ := (par2_iff M (show r + L < M.length by omega)).mp hr
    exact hle
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by omega
  have hd0 : 0 < entry M 0 (r + L) - entry M 0 r := by omega
  have hd1 : 0 < entry M 1 (r + L) - entry M 1 r := by omega
  have hexp : ∀ n, expand M n = G2 M r L n := by
    intro n
    have h := expand_eq_gexp M n hlen2 hzT (by rw [h2]; rw [hL]; exact hr)
    rw [h2, hL] at h
    simp only [show (0 < 2) from by omega, show (1 < 2) from by omega, if_true,
      Nat.add_sub_cancel_left] at h
    exact h
  have hG : ∀ m, 1 ≤ m → ∀ σ, Cons (G2 M r L m) σ → Good3 (G2 M r L m) σ :=
    fun m hm σ hσ => by rw [← hexp m] at hσ ⊢; exact hGall m hm σ hσ
  have hRk : ∀ m, 1 ≤ m → ∃ rk, Rk (G2 M r L m) rk := fun m hm => by
    obtain ⟨rk', h'⟩ := rk_expand_t2 hX hJ hz h2 I.rank m hm
    rw [hexp m] at h'; exact ⟨rk', h'⟩
  have hBE : ∀ m, 1 ≤ m → BumpE2 (G2 M r L m) := fun m _ => by
    rw [← hexp m]; exact (sInvX_expand hX m).loc.2.2.1
  have hCR := t2CopyResV3 hM hS I hz h2 r L hlen hr
  have hBS := t2BelowXS_V3 hB hM hS I D hz h2 hlen hr
  have hSD := hX.loc.1
  have key : ∀ n, 1 ≤ n → ∀ σ, Cons (G2 M r L n) σ → VSmallRAll (G2 M r L n) σ := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        intro σ hσ
        unfold G2 at hσ ⊢
        rw [gexp_one_gen hlen] at hσ ⊢
        exact hVT σ hσ
      · intro σ hCN
        have hn2 : 2 ≤ m + 1 := by omega
        obtain ⟨rkP, hRP⟩ := hRk m hm0
        set ρP := rhsIt (G2 M r L m) (rkBound (G2 M r L m) rkP) with hρP
        have hCP : Cons (G2 M r L m) ρP := cons_of_rk hRP
        have hGP := hG m hm0 _ hCP
        have hQP := ih hm0 _ hCP
        have hm : m + 1 - 1 = m := by omega
        obtain ⟨hKV, hB', hV', hVV⟩ := hCR (m + 1) hn2 σ _ hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP)
        have hK := t2GuardKids_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r (by rw [hm]; exact hBE m hm0)
        have hRK := t2RootKids_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r hX.r0p hSD
        have hF := copy_facts_gexp hlen hL0 hA hd0e hn2 hd0 hd1 hgx he2r (by rw [hm]; exact hBE m hm0)
          hCN (by rw [hm]; exact hCP) (by rw [hm]; exact hGP) (by rw [hm]; exact hRP) hK hKV hRK hB' hV' hVV
        rw [hm] at hF
        have hlN : (G2 M r L (m + 1)).length = r + (m + 1) * L := TRIO.gexp_length hlen
        have hlP : (G2 M r L m).length = r + m * L := TRIO.gexp_length hlen
        have hmL : (m + 1) * L = m * L + L := Nat.succ_mul m L
        have hrP : r < (G2 M r L m).length := by
          have : L ≤ m * L := Nat.le_mul_of_pos_left L hm0
          omega
        have hGN := hG (m + 1) (by omega) σ hCN
        apply vsmallRAll_iff.mpr
        intro k Lc c Rr hCL u hu
        rcases Nat.lt_or_ge k (r + L) with hix | hix
        · by_cases hsc : T2SeedCol M r L k
          · exact hSeed r L hlen hr (m + 1) hn2 σ hCN hGN k hsc Lc c Rr hCL u hu
          · have hshp := (hBS (m + 1) hn2 (fun k hk1 _ τ hτ => hG k hk1 τ hτ) σ hCN
              (fun j _ hj => ⟨hGN.ot_o j hj, hGN.ot_v j hj⟩) k hix).2.2.2.1 hsc
            have hlevM : LevAt M ρ k u := by
              rcases hu with hu | hu
              · left
                rw [hu]
                rcases hshp with (⟨hv, _, _⟩ | ⟨hv, _⟩ | ⟨hN, _⟩) | ⟨hv, _⟩
                · exact hv
                · exact hv
                · rw [hN] at hCL; simp at hCL
                · exact hv
              · exact Or.inr (hPre r L hlen hr (m + 1) hn2 σ hCN hGN k hix hsc u hu)
            exact WfT2X.clField_of_shapeSX (Q := fun a Lv cv => QVRAt a Lv cv u)
              (fun a Lv cv cv' h1 h2 h3 h4 h5 => qVRAt_low a Lv cv cv' u h1 h2 h3 h4 h5)
              (WfT2X.qVRAt_lowV u) I.cons I.good hCN hGN hshp
              (fun Lc0 c0 R0 h => (vsmallRAll_iff.mp hVM) k Lc0 c0 R0 h u hlevM) Lc c Rr hCL
        · obtain ⟨a, rfl⟩ : ∃ a, k = r + a + L := ⟨k - L - r, by omega⟩
          have hia : r + a < (G2 M r L m).length := by
            have hkN : r + a + L < (G2 M r L (m + 1)).length :=
              (mem_children (cl_mem_children (show c ∈ CL _ (r + a + L) by rw [hCL]; simp))).1.trans
                (mem_children (cl_mem_children (show c ∈ CL _ (r + a + L) by rw [hCL]; simp))).2
            omega
          intro s y hsy ht hhi hku g hg
          by_cases hOmega : g ≤ psi s z z
          · exact Or.inl hOmega
          by_cases hState : g ≤ spArg (σ.v (r + a + L)) z (sumN (Lc.map σ.o))
          · exact Or.inr (Or.inl hState)
          obtain ⟨hu1, huV⟩ := hCopy r L hlen hr (m + 1) hn2 σ _ hCN hGN hCP hGP (r + a) (by omega) hia
            Lc c Rr hCL s y hsy ht hhi u hu hku g hg (lt_of_not_ge hOmega) (lt_of_not_ge hState)
          exact copyFrame_VRA hsh hF hCP hGP hrP hV' hVV (i := r + a) (by omega) hia (fun _ => huV)
            (fun hg Lc0 c0 R0 h => hKM r L hlen hr (m + 1) hn2 σ _ hCN hCP hGP (r + a) (by omega) hia hg
              Lc0 c0 R0 h u hu1 huV)
            (fun Lc0 c0 R0 h => (vsmallRAll_iff.mp hQP) (r + a) Lc0 c0 R0 h u hu1) Lc c Rr hCL
            s y hsy ht hhi hku g hg
  intro n hn σ hσ
  rw [hexp n] at hσ ⊢
  exact key n hn σ hσ


end Ytosk.V3Main
