/-
**帰納法の基底 hBase: SRO[n] は評価 bval (1 + 3n) 1 と順位 brk で Inv3 と Res3A を満たす。**

構造の項目は `sInv_std`、値の項目は V3BaseI。Res3A の `drop` は、落とした行列 SRO[n].take (3n) = Mlen (3n)
の評価が ω² を底にした塔 bval (3n) ω² になること（`cons_unique`）から:
- argT・VSmallNew の後半: 数える子の o は ψ_s(0) の形（引数が 0）。
- VSmallNew の前半: 塔 P^k(ω²) の成分は 0 と 2 だけ。
- BumpWeakSrc: A の子は B だけ、B の子は D だけ、v(P_1 i) = 0。
- UpgAbsX・BumpAbsC: v(P_1 i) = 0 で吸収は空。
`seed` は前件が立たない（最後の列 x の行 0 の親は x − 1 ≠ 0）。`fch` は数える子の前の状態が 0。
-/
import Ytosk.V3BaseI

namespace Ytosk

open T

section
variable {n : Nat}

theorem base_ne_SRO (n : Nat) : Mlen (1 + 3 * n) ≠ SRO := by
  intro h
  have := congrArg List.length h
  rw [Mlen_length] at this
  simp [SRO] at this; omega

theorem base_sinv (n : Nat) : SInv (Mlen (1 + 3 * n)) := by
  rw [← expand_SRO_eq]
  exact sInv_std (Std.exp n Std.sro) (by rw [expand_SRO_eq]; exact base_ne_SRO n)

/-- The drop valuation is the tower valuation over `ω²`. -/
theorem drop_eq (n : Nat) :
    ∀ i, i < 3 * n → (drop1 (Mlen (1 + 3 * n)) (3 * n) (brk (1 + 3 * n))).o i = (bval (3 * n) w2).o i ∧
      (drop1 (Mlen (1 + 3 * n)) (3 * n) (brk (1 + 3 * n))).v i = (bval (3 * n) w2).v i := by
  have hle : 3 * n ≤ 1 + 3 * n := by omega
  have hC : Cons (Mlen (3 * n)) (drop1 (Mlen (1 + 3 * n)) (3 * n) (brk (1 + 3 * n))) := by
    unfold drop1; rw [Mlen_take hle]; exact cons_of_rk (brk_rk hle)
  intro i hi
  exact cons_unique hC (bval_cons (Or.inr ⟨by omega, rfl⟩)) (brk_rk hle) i (by simpa using hi)

/-- Counted children of the dropped matrix are `A` or `D` columns. -/
theorem CL_drop_kind {i c : Nat} {Lc : List Nat}
    (h : CL ((Mlen (1 + 3 * n)).take (3 * n)) i = Lc ++ [c]) :
    c < 3 * n ∧ 1 ≤ c ∧ (c - 1) % 3 ≠ 1 := by
  rw [Mlen_take (by omega)] at h
  obtain ⟨_, hc, hcase⟩ := CL_split (L := 3 * n) (β := w2) (Or.inr ⟨by omega, rfl⟩) h
  have := (mem_children hc).2
  simp at this
  omega

theorem base_dropRes : DropRes (Mlen (1 + 3 * n)) ((Mlen (1 + 3 * n)).length - 1) (bval (1 + 3 * n) one)
    (drop1 (Mlen (1 + 3 * n)) ((Mlen (1 + 3 * n)).length - 1) (brk (1 + 3 * n))) := by
  have hx : (Mlen (1 + 3 * n)).length - 1 = 3 * n := by simp
  rw [hx]
  have hF : BaseFit (1 + 3 * n) one := Or.inl ⟨by omega, rfl⟩
  have hβ2 : GoodBase w2 := Or.inr rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- argT
    intro i _ Lc cs hCL s y ho _ g hg
    obtain ⟨hcs, hc1, hk⟩ := CL_drop_kind hCL
    rw [(drop_eq n cs hcs).1, bval_oAD (by omega) hk] at ho
    cases ho
    simp [comps] at hg
  · -- VSmallNew
    intro i _ Lc cs hCL _
    obtain ⟨hcs, hc1, hk⟩ := CL_drop_kind hCL
    intro g hg
    left
    rw [(drop_eq n cs hcs).2, bval_vAD (by omega) hk] at hg ⊢
    rcases comps_tw hβ2 _ _ g hg with rfl | ⟨rfl, _⟩
    · exact z_le _
    · left; show two < psi (tw w2 (Kd (3 * n) cs)) z z
      unfold two; rw [psi_lt_psi]; left; exact z_lt_tw hβ2 _
  · -- BumpWeakSrc: the shape, and `WeakCS` (every `v′` is countable here)
    refine ⟨fun i h1 _ j hj hb k hk _ _ => ?_, fun i hi _ => Or.inl ?_, ?_⟩
    rotate_left 2
    · rintro ⟨⟨k, _, _, hu, _⟩, _⟩
      rw [Mlen_upg_none (by simp only [Mlen_length]; omega)] at hu
      cases hu
    swap
    · rw [(drop_eq n i hi).2]
      intro g hg
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0; rw [bval_v0] at hg; simp [comps] at hg
      · by_cases hk : (i - 1) % 3 = 1
        · rw [bval_vB (by omega) hk] at hg
          simp [wT, one, comps] at hg
          rcases hg.2 with rfl | ⟨_, rfl⟩ <;> decide
        · rw [bval_vAD (by omega) hk] at hg
          rcases comps_tw hβ2 _ _ g hg with rfl | ⟨rfl, _⟩ <;> decide
    have hiL : i < 1 + 3 * n := by
      rcases Nat.lt_or_ge i (1 + 3 * n) with h | h
      · exact h
      · exact absurd (entry_out (by simpa using h) 1) h1
    have hi1 : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; rw [Mlen_e1 hiL, if_pos rfl] at h1; exact absurd rfl h1
      · exact h
    have hjc : j = i + 1 ∧ i + 1 < 1 + 3 * n ∧ (i - 1) % 3 ≠ 2 := by
      by_cases h : i + 1 < 1 + 3 * n ∧ (i - 1) % 3 ≠ 2
      · rw [Mlen_children_AB h.1 hi1 h.2] at hj; simp at hj; exact ⟨hj, h⟩
      · rw [Mlen_children_nil (by omega)] at hj; simp at hj
    rw [hjc.1] at hj hb hk ⊢
    have hkA := (Mlen_col_eq_bump hjc.2.1 hi1 rfl).mp hb
    have hch := Mlen_children_AB hjc.2.1 hi1 hjc.2.2
    have hk' : i + 1 + 1 < 1 + 3 * n := by
      by_contra hne
      rw [Mlen_children_nil (Or.inl (by omega))] at hk; simp at hk
    have hchj := Mlen_children_AB hk' (by omega) (by omega)
    rw [hchj] at hk; simp at hk; subst hk
    exact ⟨hch, by rw [hchj]; rfl⟩
  · -- UpgAbsX
    intro i k W _ _ _ _; left; intro r hr; rw [vOpt_par1] at hr; simp [summands] at hr
  · -- BumpAbsC
    intro _ _ i _ _ _ _ r hr; rw [vOpt_par1] at hr; simp [summands] at hr

theorem base_fch : FrameClosedHi (Mlen (1 + 3 * n)) (bval (1 + 3 * n) one) := by
  intro i _ L' c R h _
  obtain ⟨rfl, _, _⟩ := CL_split (Or.inl ⟨by omega, rfl⟩ : BaseFit (1 + 3 * n) one) h
  intro u _ g hg
  simp [spArg, sumN_nil, comps] at hg

theorem base_res3A : Res3A (Mlen (1 + 3 * n)) (bval (1 + 3 * n) one) (brk (1 + 3 * n)) := by
  have hx : (Mlen (1 + 3 * n)).length - 1 = 3 * n := by simp
  refine ⟨base_dropRes, ?_, ?_⟩
  · -- seed
    intro r h1 h0
    rw [hx] at h1 h0
    exfalso
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [show 3 * 0 = 0 from rfl, Mlen_par1_0] at h1; cases h1
    · rw [Mlen_par1 (by omega) (by omega)] at h1; cases h1
      rw [Mlen_par0_BD (by omega) (by omega) (by omega)] at h0
      have := Option.some.inj h0; omega
  · -- AbsSR: `v(P_1 i) = 0`
    refine ⟨fun _ _ _ i _ _ _ r hr => ?_, fun _ _ _ _ i _ _ _ _ _ _ r hr => ?_⟩ <;>
      (rw [vOpt_par1] at hr; simp [summands] at hr)

end

/-- **The base of the induction**: every `SRO[n]` satisfies `Inv3` and `Res3A`. -/
theorem hBase_holds : ∀ n, expand SRO n ≠ [] →
    ∃ ρ rk, Inv3 (expand SRO n) ρ rk ∧ Res3A (expand SRO n) ρ rk := by
  intro n _
  rw [expand_SRO_eq]
  have hF : BaseFit (1 + 3 * n) one := Or.inl ⟨by omega, rfl⟩
  have hS := base_sinv n
  have hL : 1 ≤ 1 + 3 * n := by omega
  refine ⟨bval (1 + 3 * n) one, brk (1 + 3 * n), ⟨hS.r0p, hS.z2, hS.sibDec, hS.z1c, hS.uat, hS.uab,
    hS.r12, hS.bumpE2, hS.r01, hS.e00, bval_cons hF, base_good3 hF, brk_rk le_rfl, base_vsmallF hF,
    base_frameClosed hF, base_frameOT hF, base_kd hF, base_td hF, base_ad hF, base_au hF,
    base_tp1 hF, base_tplo hF, base_tp1w hF, base_tplow hF, base_auw hF, base_adw hF, base_trig hF,
    base_tplon hF, base_adn hF, base_rootS hF hL, base_rootP hF hL⟩, base_res3A⟩

end Ytosk
