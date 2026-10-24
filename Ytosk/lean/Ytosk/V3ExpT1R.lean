/-
**3 行・t = 1: drop-fix の VSmallR を展開の鎖で運ぶ（trio_terminates_main_GP の hVSRexp 用）。**

x より前の枠では、親の v と前の数える子の o は変わらない（FrameOT と同じ）。子 c が D の v に入らず c ≠ x なら
添字 s = v(c) も変わらず、o(c) の引数だけが小さくなる（y′ ≤ y）。前提「書き換える」「高い部分がある」は
新しい側から古い側へ移るので、M の VSmallR から出る。写しの枠は M[n − 1] から。
残り `VSRRes`: 子 c が D の v の列か c = x の枠。
-/
import Ytosk.V3ExpT1L
import Ytosk.V3DropR
import Ytosk.V3DropRH

namespace Ytosk

open T

set_option linter.unusedSectionVars false

theorem head_le_of_le : ∀ {t t' : T}, t ≤ t' → head t ≤ head t'
  | z, _, _ => z_le _
  | psi a b c, z, h => by
    rcases (le_iff _ _).mp h with h | h
    · exact absurd h (T.not_lt_z _)
    · cases h
  | psi a b c, psi a' b' c', h => by
    show psi a b z ≤ psi a' b' z
    rcases (le_iff _ _).mp h with h | h
    · rcases T.psi_lt_psi.mp h with h' | ⟨rfl, h'⟩ | ⟨rfl, rfl, _⟩
      · exact (le_iff _ _).mpr (Or.inl (T.psi_lt_psi.mpr (Or.inl h')))
      · exact (le_iff _ _).mpr (Or.inl (T.psi_lt_psi.mpr (Or.inr (Or.inl ⟨rfl, h'⟩))))
      · exact le_refl _
    · cases h; exact le_refl _

/-- A high part survives going up. -/
theorem split_fst_ne_of_le {y' y θ : T} (h : (split y' θ).1 ≠ z) (hle : y' ≤ y) : (split y θ).1 ≠ z := by
  cases y' with
  | z => exact absurd rfl h
  | psi a b c =>
    have hn : ¬ lt (psi a b z) θ = true := by
      intro hl; apply h; simp [split, hl]
    cases y with
    | z =>
      rcases (le_iff _ _).mp hle with h' | h'
      · exact absurd h' (T.not_lt_z _)
      · cases h'
    | psi a' b' c' =>
      have hh : psi a b z ≤ psi a' b' z := head_le_of_le hle
      have hn' : ¬ lt (psi a' b' z) θ = true := fun hl => hn (lt_of_le_of_lt hh hl)
      simp [split, hn']

/-- **Residual of the VSmallR carry** (`t = 1`): the frames below `x` whose counted child is a `v` call of `D`
(実測: そのような枠は M[n] で一度も書き換えない。C′ 1.9 万件・T0Ext 由来 10.8 万件). The frame of `x` is proved:
`v_N(x) = v_P(r) ≤ v(r) ≤ v(q)`, and a rewriting child has subscript `≥ v(q)`, so it is `v(q)`. -/
def VSRRes (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ (ρP : Valn) (Z : Nat → T), HoleInfo M r L n ρ ρP Z →
    Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z) →
    ∀ i, i < r + L → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R →
    DepX M (r + L) false c → c < r + L →
    ∀ s y, (glueZ M (r + L) ρ (shiftV ρP L) Z).o c = psi s y z →
    (lt (spArg (ρ.v i) z (sumN (Lc.map ρ.o))) y = true ∧ lt (psi (ρ.v i) z z) (psi s y z) = true) →
    (split y (psi (succ s) z z)).1 ≠ z →
    ∀ u, ¬ lt (ρ.v i) u = true → ∀ g ∈ comps u s,
      g ≤ psi s z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)) ∨ ∃ d ∈ comps u (ρ.v i), g ≤ d

theorem expStep_vsmallR {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hVSR : VSmallR M ρ) (hRes : VSRRes M r L d0 ρ) :
    ExpStepT1 (fun N σ => VrLe r ρ N σ ∧ VSmallR N σ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q0, hq0⟩ := par0_of_anc hA (by omega)
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hOS := hOS_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq0
  intro n hn ρP Z hCP hGP hQP0 hCN hGN hoto hotv hle hlex hH
  refine ⟨expStep_vrle I hlen h1 hx2 n hn ρP Z hCP hGP hQP0.1 hCN hGN hoto hotv hle hlex hH, ?_⟩
  have hQP := hQP0.2
  have hR := hRes n hn ρP Z hH hCN
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2
    (hxnb_t1 hlen hL hA hd0e I.z2 I.z1 h1 n hn)
    (hiu_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn) (hiux_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn)
  have hσo : ∀ a, σ.o (r + L + a) = ρP.o (r + a) := by
    intro a; rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.o (r + L + a - L) = ρP.o (r + a); congr 1; omega
  have hσv : ∀ a, σ.v (r + L + a) = ρP.v (r + a) := by
    intro a; rw [hσ, glueZ_v_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.v (r + L + a - L) = ρP.v (r + a); congr 1; omega
  intro i hi Lc c R hCL
  rcases Nat.lt_or_ge i (r + L) with h | h
  · have hS := hSA i h
    have hCLe : CL (TRIO.gexp M r L d0 0 n) i = CL M i := by
      unfold CL; rw [hS.ch]
      apply List.filter_congr
      intro c hc
      exact decide_eq_decide.mpr (counted_iff_of_cnt (hS.cnt c hc))
    rw [hCLe] at hCL
    have hcCL : c ∈ CL M i := by rw [hCL]; simp
    have hcch : c ∈ children M i := (List.mem_filter.mp hcCL).1
    have hccnt : Counted M i c := by simpa using (List.mem_filter.mp hcCL).2
    have hvd : ¬ DepX M (r + L) false i := by
      intro hv
      rcases hOS i h (DepX.ov hv) with ⟨_, hnc⟩ | ⟨hnv, _⟩
      · rcases hnc c hcch with h' | h'
        · exact hccnt.1 h'
        · exact hccnt.2 h'
      · exact hnv hv
    have hLd : ∀ d ∈ Lc, ¬ DepX M (r + L) true d := by
      intro d hd hdD
      have hdCL : d ∈ CL M i := by rw [hCL]; simp [hd]
      have hdch : d ∈ children M i := (List.mem_filter.mp hdCL).1
      have hdcnt : Counted M i d := by simpa using (List.mem_filter.mp hdCL).2
      have hdc : d < c := by
        have hs : (CL M i).Pairwise (· < ·) := (children_sorted M i).filter _
        rw [hCL] at hs
        exact (List.pairwise_append.mp hs).2.2 d hd c List.mem_cons_self
      have hiD : DepX M (r + L) true i := DepX.ochild hdch hdcnt.1 hdcnt.2 hdD
      rcases hOS i h hiD with ⟨hv, _⟩ | ⟨_, L', c', R', hch, _, _, hR', hL'⟩
      · exact hvd hv
      · have hdc' : d = c' := by
          rw [hch] at hdch
          rcases List.mem_append.mp hdch with h' | h'
          · exact absurd hdD (hL' d h' hdcnt)
          · rcases List.mem_cons.mp h' with h' | h'
            · exact h'
            · rcases hR' d h' with h'' | h''
              · exact absurd h'' hdcnt.1
              · exact absurd h'' hdcnt.2
        subst hdc'
        have hsort := children_sorted M i
        rw [hch] at hsort hcch
        rcases List.mem_append.mp hcch with h' | h'
        · have := (List.pairwise_append.mp hsort).2.2 c h' d List.mem_cons_self
          omega
        · rcases List.mem_cons.mp h' with h' | h'
          · omega
          · rcases hR' c h' with h'' | h''
            · exact hccnt.1 h''
            · exact hccnt.2 h''
    have hLo : Lc.map σ.o = Lc.map ρ.o := by
      apply List.map_congr_left
      intro d hd
      have hdCL : d ∈ CL M i := by rw [hCL]; simp [hd]
      have hdM := (mem_children (List.mem_filter.mp hdCL).1).2
      have hdx : d < r + L := by
        rcases Nat.lt_or_ge d (r + L) with h' | h'
        · exact h'
        · exfalso
          have : d = r + L := by omega
          exact hLd d hd (this ▸ DepX.leaf)
      rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hdx (hLd d hd)]
    rw [hσ, glueZ_v_lt ρ (shiftV ρP L) Z h hvd, ← hσ, hLo]
    have hcM := (mem_children hcch).2
    by_cases hcxe : c = r + L
    · -- the frame of `x`: the subscript is `v(q)`
      intro s y hso hrw _ u _ g hg
      right; right
      have h0 : par M 0 c = some i := (mem_children_iff.mp hcch).2
      have hvx : σ.v c = ρP.v r := by
        rw [hcxe, hσ, glueZ_v_ge ρ (shiftV ρP L) Z (le_refl _)]
        show ρP.v (r + L - L) = ρP.v r; rw [Nat.add_sub_cancel]
      have hs : s = σ.v c := o_sub_eq_v hCN hGN (by have := Nat.mul_pos (show 0 < n - 1 by omega) hL; omega) hso
      have hle1 : s ≤ ρ.v i := by
        rw [hs, hvx]
        exact le_trans hQP0.1 (v_par1_le_par0 I.cons I.good I.rank hcM h0 (by rw [hcxe]; exact h1))
      have hge : ¬ s < ρ.v i := by
        intro hlt
        have h2 := hrw.2
        have : psi s y z < psi (ρ.v i) z z := psi_lt_psi_z_iff.mpr (Or.inl hlt)
        exact lt_irrefl' _ (T.lt_trans' this h2)
      have hseq : s = ρ.v i := by
        rcases (le_iff _ _).mp hle1 with h' | h'
        · exact absurd h' hge
        · exact h'
      rw [hseq] at hg
      exact ⟨g, hg, le_refl _⟩
    by_cases hcv : DepX M (r + L) false c
    · exact hR i h Lc c R hCL hcv (by
        rcases Nat.lt_or_ge c (r + L) with h' | h'
        · exact h'
        · exfalso; exact hcxe (by omega))
    have hcx : c < r + L := by
      rcases Nat.lt_or_ge c (r + L) with h' | h'
      · exact h'
      · exfalso; exact hcxe (by omega)
    have hcv' : ¬ DepX M (r + L) false c := hcv
    intro s y hso hrw hhi u hu g hg
    obtain ⟨s0, y0, h0⟩ := o_psi_form I.cons (show c < M.length by omega)
    have hs0 : s0 = ρ.v c := o_sub_eq_v I.cons I.good (by omega) h0
    have hvc : σ.v c = ρ.v c := by rw [hσ]; exact glueZ_v_lt ρ (shiftV ρP L) Z hcx hcv'
    have hs : s = ρ.v c := by
      rw [← hvc]; exact o_sub_eq_v hCN hGN (by have := Nat.mul_pos (show 0 < n - 1 by omega) hL; omega) hso
    have hle' : σ.o c ≤ ρ.o c := by
      by_cases hdo : DepX M (r + L) true c
      · rw [hσ, glueZ_o_dep ρ (shiftV ρP L) Z hcx hdo]; exact (hle c hcx hdo).1
      · rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hcx hdo]
    rw [hso, h0, hs0, ← hs] at hle'
    have hyy : y ≤ y0 := by
      rcases (le_iff _ _).mp hle' with h' | h'
      · rcases T.psi_lt_psi.mp h' with h'' | ⟨_, h''⟩ | ⟨_, _, h''⟩
        · exact absurd h'' (lt_irrefl' _)
        · exact (le_iff _ _).mpr (Or.inl h'')
        · exact absurd h'' (T.not_lt_z _)
      · rw [(T.psi.inj h').2.1]
    rw [hs0, ← hs] at h0
    refine hVSR i (by omega) Lc c R hCL s y0 h0 ⟨?_, ?_⟩ (split_fst_ne_of_le hhi hyy) u hu g hg
    · exact lt_of_lt_of_le hrw.1 hyy
    · exact lt_of_lt_of_le hrw.2 (le_psi_arg hyy)
  · obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
    have ha : a < (n - 1) * L := by omega
    have hCLs : CL (TRIO.gexp M r L d0 0 n) (r + L + a) =
        (CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a)).map (· + L) := by
      unfold CL
      rw [children_shift (d0 := d0) hlen hL hA hd0e hn ha, List.filter_map]
      congr 1
      apply List.filter_congr
      intro d hd
      have hdc := mem_children hd
      rw [hlP] at hdc
      show decide (Counted (TRIO.gexp M r L d0 0 n) (r + L + a) (d + L)) =
        decide (Counted (TRIO.gexp M r L d0 0 (n - 1)) (r + a) d)
      apply decide_eq_decide.mpr
      apply counted_iff_of_cnt1 (cnt_copy hlen hL hA hd0e hn hpath (I.z2 r) (ρ := ρ) (Z := Z) ha hd)
      · have := hσo (d - r); rw [show r + L + (d - r) = d + L by omega,
          show r + (d - r) = d by omega] at this
        exact this
      · obtain ⟨s, y, he⟩ := o_psi_form hCP (i := d) (by rw [hlP]; omega)
        rw [he]; simp
    rw [hCLs] at hCL
    obtain ⟨Lc', T', hsplit, hLc, hT⟩ := List.map_eq_append_iff.mp hCL
    obtain ⟨c', R', hT', hc', hR'⟩ := List.map_eq_cons_iff.mp hT
    subst hLc hc' hR'
    rw [hT'] at hsplit
    have hLo : (Lc'.map (· + L)).map σ.o = Lc'.map ρP.o := by
      rw [List.map_map]
      apply List.map_congr_left
      intro d hd
      have hdCL : d ∈ CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a) := by rw [hsplit]; simp [hd]
      have hdc := mem_children (List.mem_filter.mp hdCL).1
      have := hσo (d - r)
      rw [show r + L + (d - r) = d + L by omega, show r + (d - r) = d by omega] at this
      exact this
    have hc'c := mem_children (List.mem_filter.mp (show c' ∈ CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a) by
      rw [hsplit]; simp)).1
    rw [hlP] at hc'c
    have hvc : σ.v (c' + L) = ρP.v c' := by
      have := hσv (c' - r)
      rw [show r + L + (c' - r) = c' + L by omega, show r + (c' - r) = c' by omega] at this
      exact this
    have hoc : σ.o (c' + L) = ρP.o c' := by
      have := hσo (c' - r)
      rw [show r + L + (c' - r) = c' + L by omega, show r + (c' - r) = c' by omega] at this
      exact this
    rw [hσv, hLo, hoc]
    exact hQP (r + a) (by rw [hlP]; omega) Lc' c' R' hsplit

/-- **`VSRRes` holds**: a counted child `c` of `D`'s `v` calls has no counted children (`OShape`), so
`o(c) = ψ_{v(c)}(0)` and `o_N(c) = ψ_{fsD(v(c), ζ)}(0)` (`v(c)` has a hole, not a successor): the argument is
`0`, so the child never rewrites. -/
theorem vsrRes_holds {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    VSRRes M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hrx := par_lt M 1 _ r h1
  obtain ⟨q0, hq0⟩ := par0_of_anc hA (by omega)
  have hOS := hOS_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq0
  intro n hn ρP Z hH hCN i hi Lc c R hCL hcv hcx s y hso hrw
  exfalso
  obtain ⟨μ, br, vr, seed, k0, hHD, _, _, _, _, _⟩ := hH
  have hcM : c < M.length := by omega
  have hnc : ∀ d ∈ children M c, col M d = bump M c ∨ (isUpg M d = true ∧ topped M d = true) := by
    rcases hOS c hcx (DepX.ov hcv) with ⟨_, hnc⟩ | ⟨hnv, _⟩
    · exact hnc
    · exact absurd hcv hnv
  have hoc := o_nocnt I.cons I.good hcM hnc
  have hHv := hHD.hole false c hcv hcx
  simp only [valB, cond_false] at hHv
  rw [glueZ_o_dep ρ (shiftV ρP L) Z hcx (DepX.ov hcv), hoc,
    fsD_sub (holeT_ne_z hHv) (holeT_not_succ hHv)] at hso
  have hy : y = z := (T.psi.inj hso).2.1.symm
  rw [hy] at hrw
  exact T.not_lt_z _ hrw.1

/-- `VSmallR` depends only on the values on the columns. -/
theorem vSmallR_congr {N : Mat} {σ τ : Valn} (h : Agree N σ τ) (hV : VSmallR N σ) : VSmallR N τ := by
  intro i hi Lc c R hCL s y ho hrw hhi u hu g hg
  have hcCL : c ∈ CL N i := by rw [hCL]; simp
  have hcN := (mem_children (List.mem_filter.mp hcCL).1).2
  have hLo : Lc.map τ.o = Lc.map σ.o := by
    apply List.map_congr_left
    intro d hd
    have hdCL : d ∈ CL N i := by rw [hCL]; simp [hd]
    exact ((h d (mem_children (List.mem_filter.mp hdCL).1).2).1).symm
  rw [← (h i hi).2] at hrw hu ⊢
  rw [hLo] at hrw ⊢
  rw [← (h c hcN).1] at ho
  exact hV i hi Lc c R hCL s y ho hrw hhi u hu g hg

/-- **`VSmallR` of `M[n]`** (`t = 1`, the chain valuation), with the residual `VSRRes`. -/
theorem vsmallR_gexp_t1 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk) (R : Res3A M ρ rk)
    {r L : Nat} (hlen : r + L + 1 = M.length) (hr : par M 1 (r + L) = some r)
    (hx2 : entry M 2 (r + L) = 0) (hVSR : VSmallR M ρ)
    (hRes : VSRRes M r L (entry M 0 (r + L) - entry M 0 r) ρ) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN ∧
      Rk (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) rkN ∧
      VSmallR (TRIO.gexp M r L (entry M 0 (r + L) - entry M 0 r) 0 n) ρN := by
  intro n hn
  have hL0 : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h; have := par_lt M 1 _ r hr; omega
    · exact h
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) hr
  have hd0e : entry M 0 (r + L) = entry M 0 r + (entry M 0 (r + L) - entry M 0 r) := by
    have := anc0_e0_lt hA (by omega); omega
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hdr := R.drop
  rw [show M.length - 1 = r + L by omega] at hdr
  have hVI : ValInv M ρ := ⟨I.good, I.vs, I.fc, I.fo, I.kd, I.td⟩
  have V1 := valInv_drop1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.rank hVI hdr
  have hcnt := hcnt_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat
  have hRk1 : Rk (M.take (r + L)) rk := rk_take (by omega) I.rank hcnt
  have hC1 : Cons (M.take (r + L)) (drop1 M (r + L) rk) := cons_of_rk hRk1
  have hdrop := drop_all (show r + L + 1 = M.length from hlen) I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1
    hRk1 I.vs hdr.vst I.fc I.fo hdr.argT
    (bump_drop (show r + L + 1 = M.length from hlen) I.r0p I.z2 I.sd I.z1 I.uat I.uab I.cons I.good hC1 hRk1
      I.kd I.td hdr.ab hdr.ws) hdr.ua
  have hP1 : VrLe r ρ (M.take (r + L)) (drop1 M (r + L) rk) ∧ VSmallR (M.take (r + L)) (drop1 M (r + L) rk) :=
    ⟨vrle_base I R hlen hr, vsmallR_take (show r + L + 1 = M.length from hlen) I.r0p I.z2 I.sd I.z1 I.uat I.uab
      I.cons I.good hC1 hRk1 hdrop hVSR⟩
  have hPs := expStep_vsmallR I hlen hL0 hd0e hr hx2 hVSR hRes
  by_cases hqr : q = r
  · subst hqr
    obtain ⟨ρN, rkN, hCN, hRN, _, hPN, _, _⟩ :=
      qr_final4 hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hr hx2 hq
        I.cons I.good I.rank I.vs I.fc I.fo hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua I.ad I.tp1w
        (I.tplow.toAt _) I.auw (I.adw.toAt _) I.tp1 I.trig I.tplon I.adn I.rootS I.rootP
        (fun N σ => VrLe q ρ N σ ∧ VSmallR N σ) hP1 hPs n hn
    exact ⟨ρN, rkN, hCN, hRN, hPN.2⟩
  · obtain ⟨s0, y0, h0⟩ := o_psi_form I.cons (show r < M.length by omega)
    obtain ⟨ρN, rkN, hCN, hRN, _, hPN, _, _⟩ :=
      t1_main_final hlen hL0 hd0e I.r0p I.z2 I.sd I.z1 I.uat I.uab I.r12 I.be I.r01 I.e00 hr hx2
        (fun h' => hqr (Option.some.inj (hq.symm.trans h'))) I.cons I.good I.rank I.vs I.fc I.fo
        I.tp1 I.tplo I.ad I.au hdr.argT I.kd I.td hdr.ab hdr.ws hdr.vst hdr.ua rfl h0 I.rootS I.rootP
        V1.g (fun N σ => VrLe r ρ N σ ∧ VSmallR N σ) hP1 hPs n hn
    exact ⟨ρN, rkN, hCN, hRN, hPN.2⟩

/-- **`hVSRexp` of `trio_terminates_main_GP`, the `t = 1` part** (no residual). -/
theorem hVSRexp_t1 :
    ∀ M ρ rk, Std M → M ≠ SRO → M ≠ [] → Inv3 M ρ rk → Res3A M ρ rk → VSmallR M ρ →
      col M (M.length - 1) ≠ (0, 0, 0) → TRIO.srow M (M.length - 1) = 1 →
      ∀ n, 2 ≤ n → expand M n ≠ SRO → expand M n ≠ [] →
        ∀ ρN rkN, Inv3V (expand M n) ρN rkN → VSmallR (expand M n) ρN := by
  intro M ρ rk hM hS hE I R P hz h1t n hn _ _ ρN' rkN' V
  obtain ⟨r, hr⟩ := parLast_of I.e00 I.r01 I.r12 hz
  have hzT : ¬ (TRIO.entry M 0 (M.length - 1) = 0 ∧ TRIO.entry M 1 (M.length - 1) = 0 ∧
      TRIO.entry M 2 (M.length - 1) = 0) := fun h => hz ((col_zero_iff M _).mpr h)
  have hlen2 : 2 ≤ M.length := by
    by_contra h
    have hx0 : M.length - 1 = 0 := by omega
    apply hz
    rw [hx0]
    have e0 := I.e00
    have e1 := I.r01 0 e0
    have e2 := I.r12 0 e1
    exact (col_zero_iff M 0).mpr ⟨e0, e1, e2⟩
  have hx2 : entry M 2 (M.length - 1) = 0 := by
    unfold TRIO.srow at h1t
    by_cases ha : 0 < TRIO.entry M 2 (M.length - 1)
    · rw [if_pos ha] at h1t; cases h1t
    · show TRIO.entry M 2 (M.length - 1) = 0; omega
  rw [h1t] at hr
  have hexp := expand_eq_gexp_t1 M n hlen2 hzT (by rw [h1t]; exact hr) h1t
  have hrx : r < M.length - 1 := par_lt M 1 _ r hr
  obtain ⟨L, hL⟩ : ∃ L, M.length - 1 = r + L := ⟨M.length - 1 - r, by omega⟩
  rw [hL] at hexp hr hx2
  simp only [Nat.add_sub_cancel_left] at hexp
  have hlen : r + L + 1 = M.length := by omega
  obtain ⟨ρN, rkN, hCN, hRN, hVN⟩ :=
    vsmallR_gexp_t1 I R hlen hr hx2 P (vsrRes_holds I hlen hr hx2) n hn
  rw [← hexp] at hCN hRN hVN
  exact vSmallR_congr (agree_of_cons hCN V.cons hRN) hVN

end Ytosk
