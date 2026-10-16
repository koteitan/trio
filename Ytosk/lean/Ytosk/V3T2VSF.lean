/-
**3 行・t = 2: VSmallF を M[n] へ運ぶ（2026-10-16、t2）。**

VSmallF は枠の性質 `QVSF`（段 v(i) での子の添字の成分の上限）なので、t = 2 の骨組みで運ぶ。
- 写し: `QVSF` は σ で動く（`qVSF_sh`）。段 v(i) ≥ V なので成分は `comps_sh` で σ と交換する。
- x より前の種でない列: FrameShape で M の枠と同じか、最後の子だけ ◁ で下がる。添字が変わる子は
  M でも N でも引数 0 で、M の VSmallF と `vs_changed_bound` から（`qVSF_of_shape`）。
- 種の列の枠: 名前つきの残り `T2SeedFrames QVSF M`。
-/
import Ytosk.V3T2VSR
import Ytosk.V3VSF
import Ytosk.V3InvW

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- **The frame property of `VSmallF`**: the components of the child's subscript at the parent level. -/
def QVSF (a : T) (Lv : List T) (cv : T) : Prop :=
  ∀ s y, cv = psi s y z → ∀ g ∈ comps a s, g ≤ psi s z z ∨ g ≤ spArg a z (sumN Lv)

theorem vsmallF_of_clField {N : Mat} {σ : Valn} (hC : Cons N σ) (hG : Good3 N σ)
    (h : CLField QVSF N σ) : VSmallF N σ := by
  intro i hi L c R hcl g hg
  have hcN : c < N.length := (mem_children (cl_mem_children (show c ∈ CL N i by rw [hcl]; simp))).2
  obtain ⟨y, hy⟩ := o_form hC hG hcN
  exact h i hi L c R hcl (σ.v c) y hy g hg

theorem clField_of_vsmallF {N : Mat} {σ : Valn} (hC : Cons N σ) (hG : Good3 N σ)
    (h : VSmallF N σ) : CLField QVSF N σ := by
  intro i hi L c R hcl s y hsy g hg
  have hcN : c < N.length := (mem_children (cl_mem_children (show c ∈ CL N i by rw [hcl]; simp))).2
  obtain ⟨y0, hy0⟩ := o_form hC hG hcN
  rw [hsy] at hy0
  simp only [psi.injEq] at hy0
  obtain ⟨rfl, -⟩ := hy0
  exact h i hi L c R hcl g hg

/-- **`QVSF` moves with `σ`.** At the parent level `a ≥ V` the components of `f(s)` are the `σ`-images of
those of `s` (`comps_sh`); a subscript `s ≤ V` stays and the level only rises. -/
theorem qVSF_sh (V V' a : T) (Lv : List T) (cv : T) (hV : isOT V = true) (hV' : isOT V' = true)
    (hVV : V < V') (ha : isOT a = true) (hVa : V ≤ a) (hs : ∀ t ∈ Lv ++ [cv], Single t)
    (hp : (Lv ++ [cv]).Pairwise (fun a b => b ≤ a)) (hlev : V < a ∨ ∀ t ∈ Lv ++ [cv], V < lev t)
    (hQ : QVSF a Lv cv) : QVSF (shf V V' a) (Lv.map (sh V V')) (sh V V' cv) := by
  have hVV' : V ≤ V' := le_of_lt hVV
  have hLs : ∀ t ∈ Lv, Single t := fun t ht => hs t (List.mem_append_left _ ht)
  have hLp : Lv.Pairwise (fun a b => b ≤ a) := (List.pairwise_append.mp hp).1
  obtain ⟨hSot, hSsum⟩ := sumN_dec Lv hLs hLp
  have hlev' : V < a ∨ ∀ q ∈ summands (sumN Lv), lev q ≠ V := by
    rcases hlev with h | h
    · exact Or.inl h
    · right; rw [hSsum]; intro q hq; exact ne_of_gt (h q (List.mem_append_left _ hq))
  have hBot : isOT (spArg a z (sumN Lv)) = true := isOT_spArg a (sumN Lv) z rfl hSot
  have hB : spArg (shf V V' a) z (sumN (Lv.map (sh V V'))) = sh V V' (spArg a z (sumN Lv)) := by
    rw [← sh_sumN hV hV' hVV (fun t ht => (hLs t ht).1)]
    have hsp := sh_spArg hV hV' hVV ha hVa (b := z) rfl hSot hlev'
    rw [sh_z] at hsp
    exact hsp
  obtain ⟨hcvot, s, y, hcv⟩ := hs cv (by simp)
  subst hcv
  have hsot : isOT s = true := isOT_sub hcvot
  intro s' y' hcv' g' hg'
  rw [hB]
  by_cases hVs : V < s
  · rw [sh_psi_gt hVs, sh_z] at hcv'
    simp only [psi.injEq] at hcv'
    obtain ⟨rfl, -⟩ := hcv'
    have hg2 : g' ∈ comps (shf V V' a) (sh V V' (sub s V)) := by
      have hdef : shf V V' s = add V' (sh V V' (sub s V)) := rfl
      rw [hdef] at hg'
      obtain ⟨P, hP, hPs⟩ := add_eq_app_prefix V' (sh V V' (sub s V))
      rw [hP, comps_app] at hg'
      have hP0 : comps (shf V V' a) P = [] := by
        apply comps_eq_nil_of_lev
        intro q hq
        exact lt_of_lt_of_le (lev_lt_of_summand hV' (hPs q hq)) (le_shf hV hV' hVV' ha hVa)
      rw [hP0, List.nil_append] at hg'
      exact hg'
    obtain ⟨g, hg, rfl⟩ := comps_sh hV hV' hVV ha hVa (isOT_sub_sfx hsot V) g' hg2
    have hgs := comps_sub_sub a s V hg
    have hgot : isOT g = true := isOT_of_mem_comps a hsot hgs
    rcases hQ s y rfl g hgs with h | h
    · left
      have := sh_le_sh hV hV' hVV' hgot (isOT_psi_zz hsot) h
      rwa [sh_psi_gt hVs, sh_z] at this
    · right
      exact sh_le_sh hV hV' hVV' hgot hBot h
  · rw [sh_psi_le hVs, sh_z] at hcv'
    simp only [psi.injEq] at hcv'
    obtain ⟨hss, -⟩ := hcv'
    rw [← hss] at hg' ⊢
    have hg2 : g' ∈ comps a s := comps_mono (le_shf_self hV hV' hVV' ha hVa) hg'
    rcases hQ s y rfl g' hg2 with h | h
    · left; exact h
    · right; exact le_trans h (le_sh hV hV' hVV' hBot)

/-- **A frame of `N` before `x` from its shape against `M`** (`QVSF`). A child whose subscript changes is a
leaf in `M` and in `N`, so `vs_changed_bound` applies. -/
theorem qVSF_of_shape {M N : Mat} {ρ σ : Valn} {i : Nat} (hC : Cons M ρ) (hG : Good3 M ρ)
    (hCN : Cons N σ) (hGN : Good3 N σ) (hi : i < M.length) (hS : FrameShape M N ρ σ i)
    (hVM : VSmallF M ρ) :
    ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL N i = Lc ++ c :: R → QVSF (σ.v i) (Lc.map σ.o) (σ.o c) := by
  have hQ : ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R →
      QVSF (ρ.v i) (Lc.map ρ.o) (ρ.o c) :=
    fun Lc c R h => clField_of_vsmallF hC hG hVM i hi Lc c R h
  intro Lc c R hCL
  rcases hS with ⟨hv, hcl, hsame⟩ | ⟨hv, Lc0, c0, hclM, hclN, hsame, hl, hot, hchv, hchM⟩ | ⟨hN, _⟩
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
      intro s y hsy g hg
      obtain ⟨yN, hyN⟩ := o_form hCN hGN hcN
      rw [hsy] at hyN
      simp only [psi.injEq] at hyN
      obtain ⟨hsv, -⟩ := hyN
      by_cases hvc : σ.v c0 = ρ.v c0
      · obtain ⟨y0, hy0⟩ := o_form hC hG hcM
        rw [hsv, hvc] at hg ⊢
        exact hQ Lc0 c0 [] hclM (ρ.v c0) y0 hy0 g hg
      · have hoM := (hchM hvc).1
        have hlv := (hchM hvc).2
        rw [hsv] at hg ⊢
        obtain ⟨hsM, hpM⟩ := cl_vals hC hG hi
        rw [hclM, List.map_append, List.map_singleton] at hsM hpM
        have hLs := sumN_dec (Lc0.map ρ.o) (fun t ht => hsM t (List.mem_append_left _ ht))
          (List.pairwise_append.mp hpM).1
        have hBc : ∀ q ∈ summands (spArg (ρ.v i) z (sumN (Lc0.map ρ.o))), psi (ρ.v c0) z z ≤ q := by
          apply spArg_summands_ge ⟨_, _, rfl⟩ (sumN (Lc0.map ρ.o)) z hLs.1
          · rw [hLs.2]; intro q hq; rw [← hoM]
            exact (List.pairwise_append.mp hpM).2.2 q hq _ (by simp)
          · simp [summands]
        have hot0 : isOT (psi (ρ.v i) (step (ρ.v i) (spArg (ρ.v i) z (sumN (Lc0.map ρ.o))) (ρ.v c0) z z) z)
            = true := by
          have hfm := o_last_form hC hi (hG.ot_v i hi) hclM (fun d hd => single_o hC hG
            (mem_children (cl_mem_children hd)).2) (by
              rw [hclM, List.map_append, List.map_singleton]; exact hpM) hoM
          rw [← hfm]
          exact hG.ot_o i hi
        exact vs_changed_bound (hGN.ot_v c0 hcN) hlv hBc (hQ Lc0 c0 [] hclM (ρ.v c0) z hoM) hot0 g hg
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

/-- **VSmallF's frame property on every `M[n]`** (`t = 2`, `n ≥ 1`): copies by `qVSF_sh`, the frames before `x` off
the seeds by `qVSF_of_shape` from `VSmallF M`, the prefix `M.take x` and the seed frames given. -/
theorem vsmallF_expand_t2 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowXResAt M ρ rk) (hM : Std M)
    (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2)
    (hQT : ∀ τ, Cons (M.take (M.length - 1)) τ → CLField QVSF (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames QVSF M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → CLField QVSF (expand M n) σ := by
  have hGall := good3_expand_t2 hM hS I R hz h2 (t2BelowXE_of hB hM hS I R hz h2)
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
            exact qVSF_of_shape I.cons I.good hCN hGN (by omega) hsh I.vs Lc c R hCL
        · obtain ⟨a, rfl⟩ : ∃ a, i = r + a + L := ⟨i - L - r, by omega⟩
          exact hcopy (r + a) (by omega) (by omega) Lc c R hCL
  intro n hn σ hσ
  rw [hexp n] at hσ ⊢
  exact key n hn σ hσ

/-- **VSmallF of every `M[n]`** (`t = 2`, `n ≥ 1`), with the seed frames as the named residual. -/
theorem vsmallF_expand_t2V {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hB : T2BelowXResAt M ρ rk) (hM : Std M)
    (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk) (hz : col M (M.length - 1) ≠ (0, 0, 0))
    (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ → Good3 (M.take (M.length - 1)) τ ∧ VSmallF (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames QVSF M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → Good3 (expand M n) σ → VSmallF (expand M n) σ := by
  intro n hn σ hσ hG
  exact vsmallF_of_clField hσ hG (vsmallF_expand_t2 hB hM hS I R hz h2
    (fun τ hτ => clField_of_vsmallF hτ (hT τ hτ).1 (hT τ hτ).2) hSeed n hn σ hσ)

end Ytosk
