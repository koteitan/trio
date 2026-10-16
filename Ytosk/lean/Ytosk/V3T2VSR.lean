/-
**3 行・t = 2: VSmallR を M[n] へ運ぶ（trio_terminates_main_GP の hVSRexp の t = 2 部分）。**

clField_expand_t2 の「最後の子を ◁ で下げても保つ」を、FrameShape の情報（v が変われば新しい子の引数は 0）つきの
強い形に替えた版 `clField_expand_t2S`。VSmallR の枠の性質 QVR は、添字が同じなら引数が下がっても前提が古い側へ移り、
添字が変われば引数 0 で書き換えないので、この強い形で保たれる（`qVR_low`）。
残り: QVR の σ 不変性 `QVRsh`（純粋な順序数の主張）と種の列の枠 `T2SeedFrames QVR`。
-/
import Ytosk.V3ExpT2FO
import Ytosk.V3ExpT1R
import Ytosk.V3T0VSR
import Ytosk.V3InvW

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

theorem clField_of_shapeS {Q : T → List T → T → Prop}
    (hQlow : ∀ a Lv cv cv', Q a Lv cv → Lhd z cv' cv → isOT cv' = true → (∃ s y, cv = psi s y z) →
      (∀ s y s' y', cv = psi s y z → cv' = psi s' y' z → s' ≠ s → y' = z) → Q a Lv cv')
    {M N : Mat} {ρ σ : Valn} {i : Nat} (hC : Cons M ρ) (hG : Good3 M ρ) (hCN : Cons N σ) (hGN : Good3 N σ)
    (hS : FrameShape M N ρ σ i)
    (hQ : ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → Q (ρ.v i) (Lc.map ρ.o) (ρ.o c)) :
    ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL N i = Lc ++ c :: R → Q (σ.v i) (Lc.map σ.o) (σ.o c) := by
  intro Lc c R hCL
  rcases hS with ⟨hv, hcl, hsame⟩ | ⟨hv, Lc0, c0, hclM, hclN, hsame, hl, hot, hchv⟩ | ⟨hN, _⟩
  · rw [hcl] at hCL
    have hmem : ∀ d ∈ Lc ++ [c], d ∈ CL M i := fun d hd => by
      rw [hCL]
      rcases List.mem_append.mp hd with h | h
      · exact List.mem_append_left _ h
      · simp at h; rw [h]; simp
    rw [hv, List.map_congr_left (fun d hd => hsame d (hmem d (List.mem_append_left _ hd))),
      hsame c (hmem c (by simp))]
    exact hQ Lc c R hCL
  · rw [hclN] at hCL
    by_cases hR : R = []
    · rw [hR] at hCL
      obtain ⟨h1, h2⟩ := List.append_inj' hCL rfl
      simp only [List.cons.injEq, and_true] at h2
      subst h1; subst h2
      rw [hv, List.map_congr_left hsame]
      have hcM : c0 < M.length := (mem_children (cl_mem_children (show c0 ∈ CL M i by rw [hclM]; simp))).2
      have hcN : c0 < N.length := (mem_children (cl_mem_children (show c0 ∈ CL N i by rw [hclN]; simp))).2
      refine hQlow _ _ _ _ (hQ Lc0 c0 [] hclM) hl hot (o_psi_form hC hcM) ?_
      intro s y s' y' hs hs' hne
      by_cases hvc : σ.v c0 = ρ.v c0
      · exfalso; apply hne
        obtain ⟨y0, hy0⟩ := o_psi_sub hCN hcN
        obtain ⟨y1, hy1⟩ := o_psi_sub hC hcM
        rw [hs'] at hy0; rw [hs] at hy1
        simp only [psi.injEq] at hy0 hy1
        rw [hy0.1, hy1.1, sf_ot (hGN.ot_v c0 hcN), sf_ot (hG.ot_v c0 hcM), hvc]
      · have := hchv hvc
        rw [hs'] at this; simp only [psi.injEq] at this; exact this.2.1
    · have hdl : (Lc ++ c :: R).dropLast = Lc0 := by rw [← hCL]; simp
      rw [List.dropLast_append_of_ne_nil (by simp)] at hdl
      have hLs : ∀ d ∈ Lc, d ∈ Lc0 := fun d hd => by rw [← hdl]; exact List.mem_append_left _ hd
      have hcs : c ∈ Lc0 := by
        rw [← hdl]
        apply List.mem_append_right
        obtain ⟨r0, rs, rfl⟩ := List.exists_cons_of_ne_nil hR
        simp
      have hclM' : CL M i = Lc ++ c :: R := by rw [hclM, hCL]
      rw [hv, List.map_congr_left (fun d hd => hsame d (hLs d hd)), hsame c hcs]
      exact hQ Lc c R hclM'
  · rw [hN] at hCL; simp at hCL


theorem clField_expand_t2S {Q : T → List T → T → Prop}
    (hQσ : ∀ (V V' a : T) (Lv : List T) (cv : T), isOT V = true → isOT V' = true → V < V' →
      isOT a = true → V ≤ a → (∀ t ∈ Lv ++ [cv], Single t) →
      (Lv ++ [cv]).Pairwise (fun a b => b ≤ a) → (V < a ∨ ∀ t ∈ Lv ++ [cv], V < lev t) →
      Q a Lv cv → Q (shf V V' a) (Lv.map (sh V V')) (sh V V' cv))
    (hQlow : ∀ a Lv cv cv', Q a Lv cv → Lhd z cv' cv → isOT cv' = true → (∃ s y, cv = psi s y z) →
      (∀ s y s' y', cv = psi s y z → cv' = psi s' y' z → s' ≠ s → y' = z) → Q a Lv cv')
    (hB : T2BelowXRes) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO)
    (I : Inv3W M ρ rk) (R : Res3W M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2) (hQM : CLField Q M ρ)
    (hQT : ∀ τ, Cons (M.take (M.length - 1)) τ → CLField Q (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames Q M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → CLField Q (expand M n) σ := by
  have hGall := good3_expand_t2 hM hS I R hz h2 (t2BelowXAll_of hB M ρ rk hM hS I R hz h2)
    (t2CopyResAll_holds M ρ rk hM hS I R hz h2)
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
  have hCR := t2CopyResAll_holds M ρ rk hM hS I R hz h2 r L hlen hr
  have hBS := t2BelowXS_of hB hM hS I R hz h2 hlen hr
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
            exact clField_of_shapeS hQlow I.cons I.good hCN hGN hsh (fun Lc c R h => hQM i (by omega) Lc c R h)
              Lc c R hCL
        · obtain ⟨a, rfl⟩ : ∃ a, i = r + a + L := ⟨i - L - r, by omega⟩
          exact hcopy (r + a) (by omega) (by omega) Lc c R hCL
  intro n hn σ hσ
  rw [hexp n] at hσ ⊢
  exact key n hn σ hσ

/-- **`σ`-invariance of `QVR`** (named residual; a statement about terms only). -/
def QVRsh : Prop :=
  ∀ (V V' a : T) (Lv : List T) (cv : T), isOT V = true → isOT V' = true → V < V' →
    isOT a = true → V ≤ a → (∀ t ∈ Lv ++ [cv], Single t) →
    (Lv ++ [cv]).Pairwise (fun a b => b ≤ a) → (V < a ∨ ∀ t ∈ Lv ++ [cv], V < lev t) →
    QVR a Lv cv → QVR (shf V V' a) (Lv.map (sh V V')) (sh V V' cv)

/-- **`QVR` survives lowering the last child** when the subscript stays or the new argument is `0`. -/
theorem qVR_low : ∀ a Lv cv cv', QVR a Lv cv → Lhd z cv' cv → isOT cv' = true → (∃ s y, cv = psi s y z) →
    (∀ s y s' y', cv = psi s y z → cv' = psi s' y' z → s' ≠ s → y' = z) → QVR a Lv cv' := by
  intro a Lv cv cv' hQ hl _ ⟨s, y, hcv⟩ hst s' y' hcv' htr hhi
  by_cases hss : s' = s
  · subst hss
    have hyy : y' < y := by
      have h := hl.1; rw [hcv', hcv] at h
      rcases psi_lt_psi_z_iff.mp h with h | ⟨_, h⟩
      · exact absurd h (lt_irrefl' _)
      · exact h
    refine hQ s' y hcv ⟨lt_trans htr.1 hyy, lt_trans htr.2 (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hyy⟩))⟩
      (split_fst_ne_of_le hhi (le_of_lt hyy))
  · have := hst s y s' y' hcv hcv' hss
    subst this
    exact absurd htr.1 (T.not_lt_z _)

theorem vsmallR_iff {N : Mat} {σ : Valn} : VSmallR N σ ↔ CLField QVR N σ := Iff.rfl

/-- **`hVSRexp` of `trio_terminates_main_GP`, the `t = 2` part**, from the residuals `QVRsh`, `T2BelowXRes` and
the seed frames. -/
theorem hVSRexp_t2 (hSh : QVRsh) (hB : T2BelowXRes)
    (hSeedF : ∀ M ρ rk, Std M → M ≠ SRO → Inv3W M ρ rk → Res3W M ρ rk → col M (M.length - 1) ≠ (0, 0, 0) →
      TRIO.srow M (M.length - 1) = 2 → T2SeedFrames QVR M) :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3W M ρ rk → Res3W M ρ rk → VSmallR M ρ →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 2 →
      ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∀ ρN rkN, Inv3V (expand M n) ρN rkN → VSmallR (expand M n) ρN := by
  intro M ρ rk hM hS hE I R P hz h2 n hn _ _ ρN rkN V
  have hlen1 : 1 ≤ M.length := by cases M with | nil => exact absurd rfl hE | cons => simp
  have hx : M.length - 1 + 1 = M.length := by omega
  have hdr := R.drop
  have hRk1 : Rk (M.take (M.length - 1)) rk :=
    rk_take (by omega) I.rank (counted_take_last hlen1 I.r0p I.z2 I.sd I.z1 I.uat)
  have hC1 : Cons (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) := cons_of_rk hRk1
  have hdrop := drop_all hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.vs hdr.vst
    I.fc I.fo hdr.argT
    (bump_drop hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 I.kd I.td hdr.ab hdr.ws)
    hdr.ua
  have hVT : VSmallR (M.take (M.length - 1)) (drop1 M (M.length - 1) rk) :=
    vsmallR_take hx I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1 hdrop P
  exact (clField_expand_t2S hSh qVR_low hB hM hS I R hz h2 P
    (fun τ hτ => vSmallR_congr (agree_of_cons hC1 hτ hRk1) hVT)
    (hSeedF M ρ rk hM hS I R hz h2) n (by omega) ρN V.cons)

end Ytosk
