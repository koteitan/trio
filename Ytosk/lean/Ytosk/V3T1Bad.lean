/-
**Bad2 の t = 1（2026-10-25）。**

`Bad2` の行列で最後の列 x の型が t = 1 で、P₀(x) = P₁(x) = r のとき:
- r = x − 1 になる（`t1qr_bad_xm1`）。x が g の部分木にあれば r は g・p・x − 1 のどれかで、r = p は Z1C（行 2 = 1 の
  列の子の行 1 は親以下）と P₁(x) = p で矛盾、r = g は兄弟 p < x の SibDec と P₁(x) = g で矛盾する。
- エンジン（`qr_final4SG`・`frameMapT1_takeG`）を落とす補題の結論（`hdrop_of_U`）と条件のない ua（`HDropU`）から
  動かす。CntX の第 3 の選言は r = x − 1 なので第 2 の選言と同じに扱える。
- q ≠ r（P₀(x) ≠ P₁(x)）のエンジン（`t1_main_vlocSG`）は落とす補題の結論だけを読む。
t = 2 の `BadOutT2B` は V3TopT2B の `badOutT2B_of` で証明（エンジンを Bad2 でも動く文脈 StepCtxB で動かす）。
-/
import Ytosk.V3T0BadOut
import Ytosk.V3T1VSRAll

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **At `t = 1` with `P₀(x) = P₁(x) = r`, a `Bad2` matrix has `r = x − 1`.** -/
theorem t1qr_bad_xm1 {M : Mat} (hR0 : R0P M) (hSD : SibDec M) (hZ1 : Z1C M) (hB : Bad2 M) {r L : Nat}
    (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hq : par M 0 (r + L) = some r)
    (hx2 : entry M 2 (r + L) = 0) : r + 2 = M.length := by
  obtain ⟨⟨k, hu⟩, p, g, hp, hg, hb, hcase⟩ := hB
  have hx : M.length - 1 = r + L := by omega
  have hx2' : M.length - 2 = r + L - 1 := by omega
  rw [hx2'] at hu hp
  rw [hx] at hcase
  rcases hcase with ⟨hA | hA, _⟩ | ⟨hpx, _, _⟩
  · have hrx := par_lt M 0 _ _ hq
    have hpx := par_lt M 0 _ _ hp
    have hgp := par_lt M 0 _ _ hg
    have hgr : Anc0 M g r := anc0_par hA (by omega) hq
    have hrx1 : Anc0 M r (r + L - 1) :=
      anc_xm1 (x := r + L) (by omega) (Anc0.step hq (Anc0.refl r)) hrx
    by_cases h1' : r = r + L - 1
    · omega
    have hrp : Anc0 M r p := anc0_par hrx1 h1' hp
    have hp2 : entry M 2 p = 1 := by
      have : entry M 2 p = (bump M g).2.2 := by rw [← hb]; rfl
      simpa [bump] using this
    have hlt1 := par1_entry_lt h1
    by_cases h2 : r = p
    · subst h2
      have := hZ1 r (r + L) hp2 (mem_children_iff.mpr ⟨by omega, hq⟩)
      omega
    have hrg : r = g := anc0_antisymm (anc0_par hrp h2 hg) hgr
    subst hrg
    exfalso
    have hpM : p ∈ children M r := mem_children_iff.mpr ⟨by omega, hg⟩
    have hxM : r + L ∈ children M r := mem_children_iff.mpr ⟨by omega, hq⟩
    obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hpM
    have hxl : r + L ∈ l₂ := by
      have hs := children_sorted M r
      rw [hsplit] at hs hxM
      rcases List.mem_append.mp hxM with h' | h'
      · exfalso; have := (List.pairwise_append.mp hs).2.2 (r + L) h' p (by simp); omega
      · simp only [List.mem_cons] at h'
        rcases h' with h' | h'
        · omega
        · exact h'
    have hle := sib_le hSD l₂ l₁ p hsplit (r + L) hxl
    rw [hb] at hle
    unfold colLe bump at hle
    simp only [col_eq_entries] at hle
    have h0x := hR0 (r + L) r hq
    omega
  · exact absurd hx2 hA
  · rw [hq] at hpx
    have := Option.some.inj hpx
    have := par_lt M 1 _ _ h1
    omega

/-- **`Bad2` at `t = 1`**: the invariant of `M[n]` and the descent, from the drop residual, the one-column drop of
`Bad2` and the shared residuals. The engines read only the conclusion of the drop lemma, the unconditional absorption
at `x − 1` (`q = r`, where `r = x − 1`), and the value invariants. -/
theorem badOutT1 (hDU : HDropU) (hTB : TakeBadV2) (hF : HFrameV2) (hLf : HLeafV2)
    {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (hM : Std M) (hS : M ≠ SRO) (hE : M ≠ []) (hB : Bad2 M)
    (I : Inv3V2 M ρ rk) (h1t : TRIO.srow M (M.length - 1) = 1) :
    ∀ n, 2 ≤ n → (∃ ρN rkN, Inv3V2 (expand M n) ρN rkN) ∧ DropsAt M ρ n := by
  intro n hn
  have S := sInv_std hM hS
  have hz : col M (M.length - 1) ≠ (0, 0, 0) := bad2_col_ne_zero hB
  obtain ⟨r, hr⟩ := parLast_of S.e00 S.r01 S.r12 hz
  rw [h1t] at hr
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hrx : r < M.length - 1 := par_lt M 1 _ r hr
  have hlen2 : 2 ≤ M.length := by omega
  have hx2 : entry M 2 (M.length - 1) = 0 := by
    unfold TRIO.srow at h1t
    by_cases ha : 0 < TRIO.entry M 2 (M.length - 1)
    · rw [if_pos ha] at h1t; cases h1t
    · show TRIO.entry M 2 (M.length - 1) = 0; omega
  have hexp := expand_eq_gexp_t1 M n hlen2 hzT (by rw [h1t]; exact hr) h1t
  have hStdN : Std (expand M n) := Std.exp n hM
  obtain ⟨I1, _⟩ := hTB M ρ rk hM hS hlen2 hB I
  have hdrop := hdrop_of_U hDU hM hS hlen2 I
  have hUA := (hDU M ρ rk hM hS hE I).1.ua
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  rw [hL] at hexp hr hx2 I1 hdrop hUA
  simp only [Nat.add_sub_cancel_left] at hexp
  have hlen : r + L + 1 = M.length := by omega
  have hL0 : 0 < L := by omega
  have hrL : r < r + L := by omega
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) hr
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by
    have := anc0_e0_lt hA (by omega); omega
  have hPR : PassRootRes M r L ρ := passRootRes_of_S1 (sInvXJ_std hM hS).1 (s1Std M hM hS) hlen hr hx2
  have hstep : ExpStepT1 (fun N σ => T1Core r ρ N σ ∧ (FrameMapT1 M ρ r L N σ ∧ VrDomQ M ρ r L N σ)) M r L
      (entry M 0 (r + L) - entry M 0 r) ρ :=
    expStep_and (expStep_core_vsmallF_pass_inv3V2 S I hlen hL0 hd0e hr hx2 hPR)
      (expStep_frameMapT1 S I.cons I.good I.rank hlen hL0 hd0e hr hx2)
  have hUAs : ∀ k W, r + 1 = r + L → upg M r = some k → ρ.v k = add (vOpt ρ (par M 1 r)) W → W ≠ z →
      (∀ s ∈ summands (vOpt ρ (par M 1 r)), s < W → Lhd z s W) ∨ SmallSelf (add (vOpt ρ (par M 1 r)) one) :=
    fun k W hi hu hvk hWz => (hUA r k W hi hu hvk hWz).imp id (fun h => h.2)
  have hvle : VrLe r ρ (M.take (r + L)) (drop1 M (r + L) rk) := by
    rcases (hdrop r hrL).2.1 with h | ⟨h, _⟩
    · exact h.le
    · exact (le_iff _ _).mpr (Or.inl h.1)
  have hbase : T1Core r ρ (M.take (r + L)) (drop1 M (r + L) rk) ∧
      (FrameMapT1 M ρ r L (M.take (r + L)) (drop1 M (r + L) rk) ∧
        VrDomQ M ρ r L (M.take (r + L)) (drop1 M (r + L) rk)) :=
    ⟨⟨I1.copyCore, hvle, I1.vs⟩,
      frameMapT1_takeG S I.cons I.good I1.cons I1.rank hlen hx2 hdrop hUAs
        (fun hq => Or.inr (t1qr_bad_xm1 S.r0p S.sibDec S.z1c hB hlen hr hq hx2))⟩
  have hfin : ∃ ρN rkN, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
      Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) rkN ∧
      Good3 (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
      (T1Core r ρ (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
        (FrameMapT1 M ρ r L (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
          VrDomQ M ρ r L (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN)) ∧
      isOT (root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN) = true ∧
      root (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN < root M ρ := by
    by_cases hq : par M 0 (r + L) = some r
    · have hr2 : r + 2 = M.length := t1qr_bad_xm1 S.r0p S.sibDec S.z1c hB hlen hr hq hx2
      obtain ⟨b0, hro, _, _⟩ := qr_o_r hlen S.r0p S.sibDec hr hx2 hq I.cons I.good I.rank
      have hlt := qr_seed_lt hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hr hx2 hq I.cons I.good I.rank hdrop
      have hseedC := qr_seedC_of hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab I.cons I.good I.rank hdrop hrL hro
        hlt hUAs (Or.inr hr2)
      exact qr_final4SG hlen hL0 hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00
        hr hx2 hq I.cons I.good I.rank I.kd I.td hdrop hseedC
        I.tp1w (I.tplowAt hlen hr) I.auwl I.auw0 (I.adwAt hlen hr) I.tp1 I.trigs I.tplon I.adn I.rootS I.rootP
        _ hbase hstep n hn
    · have hrM : r < M.length := by omega
      obtain ⟨br, hro⟩ := o_psi_sub I.cons hrM
      rw [sf_ot (I.good.ot_v r hrM)] at hro
      have hne : (drop1 M (r + L) rk).o r ≠ ρ.o r :=
        ne_of_lt (o_r_strict0 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2
          hr hx2 hq I.cons I.good I1.cons I1.rank hdrop)
      exact t1_main_vlocSG hlen hL0 hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00
        hr hx2 hq I.cons I.good I.rank I.vs I.fc I.fo I.tp1 I.tplos I.ads I.aus
        I.kd I.td hdrop hne rfl hro I.rootS I.rootP I1.good
        _ hbase hstep n hn
  obtain ⟨ρN, rkN, hCN, hRN, hGN, ⟨hcore, hmap, _⟩, hot, hlt⟩ := hfin
  rw [hexp] at hStdN
  have hNE : TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [len_N (d0 := entry M 0 (r + L) - entry M 0 r) hlen (show 2 ≤ n from hn)]
    omega
  have hNS := ne_SRO_of_rk hRN
  obtain ⟨hTP, hTPW⟩ := hLf _ ρN rkN hStdN hNS hNE hCN hRN hGN
  refine ⟨⟨ρN, rkN, ?_⟩, dropsAt_of hexp ⟨ρN, rkN, hCN, hRN, hot, hlt⟩⟩
  rw [hexp]
  exact inv3V2_of_core hRN hcore (vsmallRAll_of_mapT1 hmap I.vra)
    (hF _ ρN rkN hStdN hNS hNE hCN hRN hGN) hTP hTPW

/-- **`BadOutV2` at `t = 2`** (2026-10-25; `t = 0` is `BadOutT0`, `t = 1` is `badOutT1`). Proved by `badOutT2B_of`
(V3TopT2B): the `t = 2` engines run on the context `StepCtxB`, which holds on `Bad2` too. -/
def BadOutT2B : Prop :=
  ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Bad2 M → Inv3V2 M ρ rk → TRIO.srow M (M.length - 1) = 2 →
    ∀ n, 2 ≤ n → (∃ ρN rkN, Inv3V2 (expand M n) ρN rkN) ∧ DropsAt M ρ n

theorem badOutT12_of (hDU : HDropU) (hTB : TakeBadV2) (hF : HFrameV2) (hLf : HLeafV2) (hN : BadOutT2B) :
    BadOutT12 := by
  intro M ρ rk hM hS hE hB I hs0 n hn
  have hsrow : TRIO.srow M (M.length - 1) = 0 ∨ TRIO.srow M (M.length - 1) = 1 ∨
      TRIO.srow M (M.length - 1) = 2 := by
    unfold TRIO.srow; split_ifs <;> simp
  rcases hsrow with h0 | h1t | h2t
  · exact absurd h0 hs0
  · exact badOutT1 hDU hTB hF hLf hM hS hE hB I h1t n hn
  · exact hN M ρ rk hM hS hE hB I h2t n hn

end Ytosk
