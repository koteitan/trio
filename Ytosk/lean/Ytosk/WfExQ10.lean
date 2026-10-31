/-
**WfExQ10 (2026-11-01): VSmallF through the DQ copy, reduced to the changed `D` children (`VSFResQ`).**
Copy of `expStep_vsmallFS` (V3ExpT1A) for `glueQ`: frames off the changed children are those of `M` (parent `v` and
earlier counted children unchanged), copy frames those of `M[n-1]`, the frame of `x` has no components
(`v_N(x) = v_P(r) ≤ v(r) ≤ v(q)`, `VrLe` carried: `r ∉ D_v`).  The residual `VSFResQ` is the condition at a frame
below `x` whose counted child `c` is a `v` call of `D`, at the new value `vq c` (the old `VSFRes` with `fsD`).
-/
import Ytosk.WfExQ9

namespace Ytosk.WfExQ10
open T Ytosk Ytosk.WfExQ1 Ytosk.WfExQ2 Ytosk.WfExQ4 Ytosk.WfExQ8 Ytosk.WfExQ9 Ytosk.WfQrL1 Ytosk.WfQrL7

set_option linter.unusedSectionVars false

/-- **The residual of VSmallF at the changed `D` children**, at the new values. -/
def VSFResQ (M : Mat) (r L d0 : Nat) (ρ : Valn) : Prop :=
  ∀ n, 2 ≤ n → ∀ (ρP : Valn) (oq vq : Nat → T),
    Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP → Good3 (TRIO.gexp M r L d0 0 (n - 1)) ρP →
    Cons (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq) →
    Good3 (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq) →
    ExDQY M r L ρ n ρP oq vq →
    ∀ i, i < r + L → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R →
    DepX M (r + L) false c → c < r + L →
    ∀ g ∈ comps (ρ.v i) ((glueQ M (r + L) ρ (shiftV ρP L) oq vq).v c),
      g ≤ psi ((glueQ M (r + L) ρ (shiftV ρP L) oq vq).v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o))

theorem expStepQR_vsmallF {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rk) (hVS : VSmallF M ρ)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hRes : VSFResQ M r L d0 ρ) :
    ExpStepQR (fun N σ => VrLe r ρ N σ ∧ VSmallF N σ) (fun N σ => VrLe r ρ N σ ∧ VSmallF N σ)
      (ExDQY M r L ρ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q0, hq0⟩ := par0_of_anc hA (by omega)
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hOS := hOS_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq0
  intro n hn ρP oq vq hCP hGP hQP0 hCN hGN hEx
  refine ⟨le_of_eq (glueQ_v_lt (par_lt M 1 _ r h1)
    (not_depX_v_r1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab h1 hx2)), ?_⟩
  have hQP := hQP0.2
  have hR := hRes n hn ρP oq vq hCP hGP hCN hGN hEx
  set σ := glueQ M (r + L) ρ (shiftV ρP L) oq vq with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2
    (hxnb_t1 hlen hL hA hd0e S.z2 S.z1c h1 n hn)
    (hiu_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn) (hiux_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn)
  have hσo : ∀ a, σ.o (r + L + a) = ρP.o (r + a) := by
    intro a; rw [hσ, glueQ_o_ge (by omega)]
    show ρP.o (r + L + a - L) = ρP.o (r + a); congr 1; omega
  have hσv : ∀ a, σ.v (r + L + a) = ρP.v (r + a) := by
    intro a; rw [hσ, glueQ_v_ge (by omega)]
    show ρP.v (r + L + a - L) = ρP.v (r + a); congr 1; omega
  have hσoZ : ∀ a, (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => z)).o (r + L + a) = ρP.o (r + a) := by
    intro a; rw [glueZ_o_ge ρ (shiftV ρP L) (fun _ => z) (by omega)]
    show ρP.o (r + L + a - L) = ρP.o (r + a); congr 1; omega
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
      rw [hσ, glueQ_o_lt hdx (hLd d hd)]
    rw [hσ, glueQ_v_lt h hvd, ← hσ, hLo]
    have hcM := (mem_children hcch).2
    by_cases hcxe : c = r + L
    · -- the frame of `x`: `v_N(x) = v_P(r) ≤ v(r) ≤ v(q)`, no components at the level `v(q)`
      intro g hg
      exfalso
      have h0 : par M 0 c = some i := (mem_children_iff.mp hcch).2
      have hvx : σ.v c = ρP.v r := by
        rw [hcxe, hσ, glueQ_v_ge (le_refl _)]
        show ρP.v (r + L - L) = ρP.v r; rw [Nat.add_sub_cancel]
      have hle' : ρP.v r ≤ ρ.v i :=
        le_trans hQP0.1 (v_par1_le_par0 hC hG hRM hcM h0 (by rw [hcxe]; exact h1))
      have hot : isOT (ρP.v r) = true := hGP.ot_v r (by rw [hlP]; have := Nat.mul_pos (show 0 < n - 1 by omega) hL; omega)
      rw [hvx, comps_nil_of_le hot hle'] at hg
      simp at hg
    · have hcx : c < r + L := by omega
      by_cases hcv : DepX M (r + L) false c
      · exact hR i h Lc c R hCL hcv hcx
      · rw [hσ, glueQ_v_lt hcx hcv]
        exact hVS i (by omega) Lc c R hCL
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
      apply counted_iff_of_cnt1 (cnt_copy hlen hL hA hd0e hn hpath (S.z2 r) (ρ := ρ) (Z := fun _ => z) ha hd)
      · have := hσoZ (d - r); rw [show r + L + (d - r) = d + L by omega,
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
    rw [hσv, hLo, hvc]
    exact hQP (r + a) (by rw [hlP]; omega) Lc' c' R' hsplit

/-- The carried property with the chain bound and `VrLe` at `r`. -/
def PnV3s (ρ : Valn) (r : Nat) (N : Mat) (σ : Valn) : Prop := PnV3 N σ ∧ σ.o r < ρ.o r ∧ σ.v r ≤ ρ.v r

open Ytosk.G Ytosk.WfExQ4 Ytosk.WfExQ5 Ytosk.WfExQ6 Ytosk.WfExQ9 Ytosk.WfQrH6 in
/-- **`ExpStepQ` of `PnV3s` with `ExDQX`**: remaining `VSFResQ`, `VSmallRAll`, `FrameAtN`. -/
theorem expStepQ_V3s {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (I : Inv3V3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    (hVSF : VSFResQ M r L d0 ρ)
    (hVRA : ExpStepQR PnV3 (fun N σ => VSmallRAll N σ) (ExDQY M r L ρ) M r L d0 ρ)
    (hFr : FrameAtN M r L d0) :
    ExpStepQ (PnV3s ρ r) (ExDQX M r L ρ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hox : ∃ t, ρ.o (r + L) = psi (succ t) z z :=
    ⟨_, o_last_t1 hlen I.cons I.good h1 (by have := par1_entry_lt h1; omega) hx2⟩
  intro n hn ρP oq vq hCP hGP hPPs hCN hGN hEX
  have hEx : ExDQY M r L ρ n ρP oq vq := ⟨hEX, hPPs.2.1⟩
  have hPP : PnV3 (TRIO.gexp M r L d0 0 (n - 1)) ρP := hPPs.1
  have hrD : DepX M (r + L) true r := dep_anc_x S.uat S.z2 S.r12 S.bumpE2 hlen hx2 hA
  have hrx : r < r + L := by omega
  obtain ⟨_, _, ⟨rkN, hR⟩, hS, hP⟩ :=
    expStepQ_easy hlen hL hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab S.r12 S.bumpE2 S.r01 S.e00 h1 hx2
      I.rank I.rootP PnV3 n hn ρP oq vq hCP hGP hPP hCN hGN hEX.1
  obtain ⟨_, J⟩ := hPP
  have hxnb := hxnb_t1 hlen hL hA hd0e S.z2 S.z1c h1 n hn
  have hiu := hiu_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn
  have hiux := hiux_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn
  have hOS := hOS_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq
  have hph : PH3cG (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq) :=
    ph3c_iff.mpr (frameQR_N_t1Q hlen hL hA hd0e hn PH' (fun _ _ _ _ _ hyy ht h => ph'_drop hyy ht h)
      hpath hx2 hxnb (S.z2 r) hiu hiux hCP hOS I.cons (ph3c_iff.mp I.ph)
      (omQ_qr PH' (fun _ _ _ _ _ _ hb hge hδz hδ _ => ph'_app hb hge hδz hδ) S I hlen hL h1 hx2 hq hn hGN hEx.2)
      (ph3c_iff.mp J.ph) hEX.1.1 hEX.2 hox)
  have hf3 : FC3 (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq) :=
    fc3_iff.mpr (frameQR_N_t1Q hlen hL hA hd0e hn F3' (fun _ _ _ _ _ hyy ht h => f3'_drop hyy ht h)
      hpath hx2 hxnb (S.z2 r) hiu hiux hCP hOS I.cons (fc3_iff.mp I.fc3)
      (omQ_qr F3' (fun _ _ _ _ _ _ hb hge hδz hδ _ => f3'_app hb hge hδz hδ) S I hlen hL h1 hx2 hq hn hGN hEx.2)
      (fc3_iff.mp J.fc3) hEX.1.1 hEX.2 hox)
  have hlN := len_N (d0 := d0) hlen hn
  have hGo : ∀ c, c < r + L → DepX M (r + L) true c → isOT (oq c) = true := by
    intro c hc hd
    have := hGN.ot_o c (by omega)
    rwa [glueQ_o_dep hc hd] at this
  have hfc : FrameClosed (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq) :=
    WfExQ5.frameClosed_N_t1Q hlen hL hA hd0e hn hpath hx2 hxnb (S.z2 r) hiu hiux hCP hOS I.cons I.good I.fc
      (fcOm_qr S I hlen hL h1 hx2 hq n hn ρP oq vq hGN hEx.2) hGo J.fc hEX.1.1 hEX.2 hox
  have hfo := expStepQR_fo S I hlen hL hd0e h1 hx2 (ExDQY M r L ρ) n hn ρP oq vq hCP hGP ⟨_, J⟩ hCN hGN hEx
  obtain ⟨hkd, htd⟩ := expStepQR_bumpDec S I hlen hL hd0e h1 hx2 n hn ρP oq vq hCP hGP ⟨_, J⟩ hCN hGN hEX
  have hVV := expStepQR_vsmallF S I.cons I.good I.rank I.vs hlen hL hd0e h1 hx2 hVSF n hn ρP oq vq hCP hGP
    ⟨hPPs.2.2, J.vs⟩ hCN hGN hEx
  have hvs := hVV.2
  have hvra := hVRA n hn ρP oq vq hCP hGP ⟨_, J⟩ hCN hGN hEx
  obtain ⟨F, hTP, hTPW⟩ := hFr n hn _ rkN hCN hR hGN
  refine ⟨⟨rkN, inv3V3_of_parts hCN hGN hR hS hP ⟨hvs, hfc, hfo, hkd, htd, hph, hf3, hvra⟩ F hTP hTPW⟩, ?_, hVV.1⟩
  rw [glueQ_o_dep hrx hrD]
  obtain ⟨η, hD⟩ := hEX.1.1 r hrx hrD
  exact hD.lt


section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e

open Ytosk.WfQrL5 Ytosk.WfQrL6 Ytosk.WfQrL8 Ytosk.WfQrL9 Ytosk.WfQrL10 Ytosk.WfQrL16 Ytosk.WfQrL18 Ytosk.WfQrH5
  Ytosk.WfQrH6 Ytosk.WfQrH3 Ytosk.WfQrH2 in
/-- **The q = r chain carrying `Inv3V3`** (`qr_chainH3` with `Pn = PnV3s ρ r`, `Ex = ExDQX`; the `Ex` conjunct of
`hLocH` is gone: it follows from the C_strip conjuncts).  Remaining value residuals: `hVSF`, `hVRA`, `hFr`. -/
theorem qr_chainV3s (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ n, 2 ≤ n → ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ n, 2 ≤ n → ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : ∀ n, 2 ≤ n → isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    (hnd : ∀ n, 2 ≤ n → ∀ g, g ≤ r → ∀ a, a < (n - 1) * L →
      (par (TRIO.gexp M r L d0 0 (n - 1)) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 (n - 1)) (r + a) = some g) → ¬ DepX M (r + L) false g)
    {ρ : Valn} {rkM : Bool → Nat → Nat}
    (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rkM)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
    (h1x : entry M 1 (r + L) ≠ 0) (hp1 : par M 1 (r + L) = some r)
    (hrD : DepX M (r + L) true r)
    {Rt : Nat} (hRA : Anc0 M Rt (r + L))
    (hR0 : col M Rt = (0, 0, 0)) (hRlast : ∀ j, Rt < j → j ≤ r + L → entry M 0 j ≠ 0)
    (hRd : DepX M (r + L) true Rt)
    (hsM : ∀ i ∈ roots M, Single (ρ.o i)) (hpM : ((roots M).map ρ.o).Pairwise (fun a b => b ≤ a))
    (hOSD : ∀ i, i < r + L → DepX M (r + L) true i → OShapeD M (r + L) i)
    (hVS : ∀ i, i < r + L → DepX M (r + L) false i → VShape M (r + L) i)
    (hPre : ∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R →
      isOT (preState M ρ i L') = true)
    (hLocH : ∀ n, 2 ≤ n → ∀ ρP σ : Valn, Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      ρP.o r < ρ.o (r + L) → ρP.o r ≠ z → Cons (TRIO.gexp M r L d0 0 n) σ →
        -- C_strip (standard form of the new values)
        (∀ c, c ≤ r + L → DepX M (r + L) true c → ∃ η tS, DQC η false (ρ.o c) (σ.o c) tS) ∧
        (∀ i, i < r + L → DepX M (r + L) false i → ∃ η tS, DQC η true (ρ.v i) (σ.v i) tS) ∧
        -- the `o` frame fields
        (∀ i L' c R, i < r + L → DepX M (r + L) true i → children M i = L' ++ c :: R → DepX M (r + L) true c →
          ∀ η, DQ η false (ρ.o c) (σ.o c) → OFields (ρ.v i) (preState M ρ i L') (ρ.o c) (σ.o c) η) ∧
        (∀ i k, i < r + L → DepX M (r + L) false i → upg M i = some k → entry M 2 i = 0 →
          Single (last (ρ.v k)) ∧ Single (last (σ.v k)) ∧
          ∀ η, DQ η true (ρ.v k) (σ.v k) → DQ η false (last (ρ.v k)) (last (σ.v k))) ∧
        (∀ i L' K j k, i < r + L → DepX M (r + L) false i → children M i = L' ++ [j] → col M j = bump M i →
          children M j = K ++ [k] → DepX M (r + L) true k →
          Single (bumpW M ρ i) ∧ Single (bumpWQ M ρ i L' K (σ.o k)) ∧
          ((∃ η, DQ η false (ρ.o k) (σ.o k)) →
            ∃ η', DQ η' false (bumpW M ρ i) (bumpWQ M ρ i L' K (σ.o k)))))
    {ρ1 : Valn} {rk1 : Bool → Nat → Nat}
    (hC1 : Cons (TRIO.gexp M r L d0 0 1) ρ1) (hR1 : Rk (TRIO.gexp M r L d0 0 1) rk1)
    (hG1 : Good3 (TRIO.gexp M r L d0 0 1) ρ1)
    (hv1 : ρ1.v r ≤ ρ.v r)
    (hPv1 : ∀ g, g ≤ r → ∀ a, a < L →
      (par (TRIO.gexp M r L d0 0 1) 1 (r + a) = some g ∨
        upg (TRIO.gexp M r L d0 0 1) (r + a) = some g) → ρ.v g = ρ1.v g)
    (S : SInv M) (I : Inv3V3 M ρ rkM) (hq : par M 0 (r + L) = some r)
    (hVSF : VSFResQ M r L d0 ρ)
    (hVRA : ExpStepQR PnV3 (fun N σ => VSmallRAll N σ) (ExDQY M r L ρ) M r L d0 ρ)
    (hFr : FrameAtN M r L d0)
    (hP1 : PnV3 (TRIO.gexp M r L d0 0 1) ρ1) (hs1 : ρ1.o r < ρ.o r) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ PnV3s ρ r (TRIO.gexp M r L d0 0 n) ρN ∧
      ρN.o r < ρ.o r ∧ ρN.o r < ρ.o (r + L) ∧ ρN.o r ≠ z ∧
      (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ :=
  WfQrH7.qr_chainH3 hlen hL hA hd0e hpath hx2 hxnb hz2 hiu hiux hnd hC hG hRM hOS h1x hp1 hrD hRA hR0 hRlast hRd
    hsM hpM (ExDQX M r L ρ) hOSD hVS hPre
    (fun n hn ρP σ hCP hlt hne hCN => by
      obtain ⟨ho, hv, hOF, hU, hB⟩ := hLocH n hn ρP σ hCP hlt hne hCN
      exact ⟨ho, hv, WfExQ7.exDQX_of_loc n ρP hlt ho hv, hOF, hU, hB⟩)
    hC1 hR1 hG1 hv1 hPv1 (PnV3s ρ r) ⟨hP1, hs1, hv1⟩
    (expStepQ_V3s S I hlen hL hd0e hp1 hx2 hq hVSF hVRA hFr)

end


end Ytosk.WfExQ10
