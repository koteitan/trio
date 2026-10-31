/-
**WfExQ11 (2026-11-01): VSmallRAll through the DQ copy (no residual).**
Copy of `expStep_frameMapT1` (V3T1VSRAll) for `glueQ`: the frame map `FrameMapT1` (frames of `M[n]` map to frames
of `M` with the same `v`, state and subscript and a larger argument) uses the `D` values only through
`value ≤ old value`, `value ≠ 0` (DQ.lt, o_ne_z_of_cons) and `ρP.o r ≤ o(x)`.  Then `vsmallRAll_of_mapT1` gives
`VSmallRAll` of `M[n]` from that of `M` alone.
-/
import Ytosk.WfExQ10
import Ytosk.V3T1VSRAll

namespace Ytosk.WfExQ11
open T Ytosk Ytosk.WfExQ1 Ytosk.WfExQ2 Ytosk.WfExQ4 Ytosk.WfExQ8 Ytosk.WfQrL1 Ytosk.WfQrL7

set_option linter.unusedSectionVars false

section
variable {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
  (hR : Rk M rk) {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
  (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
include S hC hG hR hlen hL hd0e h1 hx2

/-- **The frame map survives each `t = 1` copy.** -/
theorem expStepQR_frameMapT1 :
    ExpStepQR (fun N σ => FrameMapT1 M ρ r L N σ ∧ VrDomQ M ρ r L N σ)
      (fun N σ => FrameMapT1 M ρ r L N σ ∧ VrDomQ M ρ r L N σ) (ExDQY M r L ρ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hrx : r < r + L := par_lt M 1 _ r h1
  obtain ⟨q0, hq0⟩ := par0_of_anc hA (by omega)
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hvr : ¬ DepX M (r + L) false r := not_depX_v_r1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab h1 hx2
  intro n hn ρP oq vq hCP hGP hPP hCN hGN hEx
  have hle : ∀ c, c < r + L → DepX M (r + L) true c → oq c ≤ ρ.o c ∧ oq c ≠ z := by
    intro c hc hd
    obtain ⟨η, hD⟩ := hEx.1.1.1 c hc hd
    refine ⟨le_of_lt hD.lt, ?_⟩
    have := WfQrH5.o_ne_z_of_cons hCN (c := c)
      (by rw [len_N (d0 := d0) hlen hn]; omega)
    rwa [glueQ_o_dep hc hd] at this
  have hlex : ρP.o r ≤ ρ.o (r + L) ∧ ρP.o r ≠ z :=
    ⟨hEx.1.2, WfQrH5.o_ne_z_of_cons hCP (c := r)
      (by rw [len_P (d0 := d0) (n := n) hlen]; have := Nat.mul_pos (show 0 < n - 1 by omega) hL; omega)⟩
  set σ := glueQ M (r + L) ρ (shiftV ρP L) oq vq with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2
    (hxnb_t1 hlen hL hA hd0e S.z2 S.z1c h1 n hn)
    (hiu_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn) (hiux_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn)
  have hCLeq : ∀ j, j < r + L → CL (TRIO.gexp M r L d0 0 n) j = CL M j := by
    intro j hj
    have hS := hSA j hj
    unfold CL; rw [hS.ch]
    apply List.filter_congr
    intro d hd
    exact decide_eq_decide.mpr (counted_iff_of_cnt (hS.cnt d hd))
  have hσoZ : ∀ a, (glueZ M (r + L) ρ (shiftV ρP L) (fun _ => z)).o (r + L + a) = ρP.o (r + a) := by
    intro a; rw [glueZ_o_ge ρ (shiftV ρP L) (fun _ => z) (by omega)]
    show ρP.o (r + L + a - L) = ρP.o (r + a); congr 1; omega
  have hσo : ∀ a, σ.o (r + L + a) = ρP.o (r + a) := by
    intro a; rw [hσ, glueQ_o_ge (by omega)]
    show ρP.o (r + L + a - L) = ρP.o (r + a); congr 1; omega
  have hσv : ∀ a, σ.v (r + L + a) = ρP.v (r + a) := by
    intro a; rw [hσ, glueQ_v_ge (by omega)]
    show ρP.v (r + L + a - L) = ρP.v (r + a); congr 1; omega
  have hσvr : σ.v r = ρ.v r := by rw [hσ, glueQ_v_lt hrx hvr]
  refine ⟨?_, fun _ u g hg => Or.inr ⟨g, hσvr ▸ hg, le_refl g⟩⟩
  intro k c Lc R s y hCL hsy hrw
  have hy0 : y ≠ z := ne_z_of_lt hrw.1
  rcases Nat.lt_or_ge k (r + L) with hk | hk
  · -- the frames before `x`
    rw [hCLeq k hk] at hCL
    have hcCL : c ∈ CL M k := by rw [hCL]; simp
    have hcch : c ∈ children M k := (List.mem_filter.mp hcCL).1
    have hccnt : Counted M k c := by simpa using (List.mem_filter.mp hcCL).2
    have hcM := (mem_children hcch).2
    have hkc := (mem_children hcch).1
    have h0 : par M 0 c = some k := (mem_children_iff.mp hcch).2
    have hvk : ¬ DepX M (r + L) false k := fun hv =>
      uncnt_of_depv hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq0 hk hv hcch hccnt
    have hσvk : σ.v k = ρ.v k := by rw [hσ, glueQ_v_lt hk hvk]
    have hφk := phiT1_lt (r := r) (L := L) hk
    rcases Nat.lt_or_ge c (r + L) with hcx | hcx
    · -- an ordinary child
      left
      have hφc := phiT1_lt (r := r) (L := L) hcx
      rw [hφk, hφc]
      have hcN : c < (TRIO.gexp M r L d0 0 n).length := by rw [hlN]; omega
      have hcv : ¬ DepX M (r + L) false c := by
        intro hcd
        have hCLc : CL M c = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro d hd
          exact uncnt_of_depv hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq0 hcx hcd
            (List.mem_filter.mp hd).1 (by simpa using (List.mem_filter.mp hd).2)
        have hoc : σ.o c = psi (σ.v c) z z := by
          rw [o_cl_eq hCN hGN hcN, hCLeq c hcx, hCLc]; rfl
        rw [hoc] at hsy
        simp only [psi.injEq] at hsy
        exact hy0 hsy.2.1.symm
      have hσvc : σ.v c = ρ.v c := by rw [hσ, glueQ_v_lt hcx hcv]
      obtain ⟨y1, hy1⟩ := o_psi_sub hCN hcN
      rw [hsy, sf_ot (hGN.ot_v c hcN), hσvc] at hy1
      simp only [psi.injEq] at hy1
      obtain ⟨hs, -⟩ := hy1
      obtain ⟨yM, hyM⟩ := o_psi_sub hC hcM
      rw [sf_ot (hG.ot_v c hcM), ← hs] at hyM
      have hole : σ.o c ≤ ρ.o c := by
        by_cases hD : DepX M (r + L) true c
        · rw [hσ, glueQ_o_dep hcx hD]; exact (hle c hcx hD).1
        · rw [hσ, glueQ_o_lt hcx hD]
      rw [hsy, hyM] at hole
      have hyy := arg_le_of_psi_le hole
      have hLo : Lc.map ρ.o = Lc.map σ.o := by
        apply List.map_congr_left
        intro d hd
        have hdCL : d ∈ CL M k := by rw [hCL]; simp [hd]
        have hdch : d ∈ children M k := (List.mem_filter.mp hdCL).1
        have hdc : d < c := by
          have hs' : (CL M k).Pairwise (· < ·) := (children_sorted M k).filter _
          rw [hCL] at hs'
          exact (List.pairwise_append.mp hs').2.2 d hd c (by simp)
        have hdD : ¬ DepX M (r + L) true d := fun hD =>
          p1_dep hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq0 hk hdch hcch hdc hD hccnt
        rw [hσ, glueQ_o_lt (by omega) hdD]
      refine ⟨Lc, R, yM, hCL, hσvk, hLo, hyM, hyy, ?_⟩
      rw [hLo, ← hσvk]
      exact rw_up hyy hrw
    · -- the copy root `x`
      right
      have hcxe : c = r + L := by omega
      subst hcxe
      have hkq : k = q0 := by rw [h0] at hq0; exact Option.some.inj hq0
      subst hkq
      have hkr : k = r := by
        by_contra hkr
        have hAk : Anc0 M r k := anc0_par hA (by omega) h0
        have hrk : r < k := lt_of_le_of_ne hAk.le (Ne.symm hkr)
        have hHi : HiR M r k := fun s hs1 hs2 hs3 =>
          hpath s hs1 (hs2.trans (Anc0.step h0 (Anc0.refl k))) hs3 (by have := hs2.le; omega)
        have hlt := v_chain_lt hC hG hR k hrk (by omega) hAk hHi
        have hox : ρ.o (r + L) = psi (succ (ρ.v r)) z z :=
          o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2
        have hσx : σ.o (r + L) = ρP.o r := by have := hσo 0; simpa using this
        have h2 := hrw.2
        rw [hσvk, ← hsy, hσx] at h2
        have h3 : ρP.o r ≤ psi (ρ.v k) z z :=
          le_trans hlex.1 (by rw [hox]; exact psi_z_le (succ_le_of_lt hlt))
        exact lt_irrefl' _ (lt_of_lt_of_le h2 h3)
      rw [hkr] at h0 hσvk hk ⊢
      refine ⟨phiT1_lt hk, phiT1_x hL, hσvk, ?_⟩
      have hxN : r + L < (TRIO.gexp M r L d0 0 n).length := by
        rw [hlN]; have := Nat.mul_pos (show 0 < n - 1 by omega) hL; omega
      obtain ⟨y1, hy1⟩ := o_psi_sub hCN hxN
      rw [hsy, sf_ot (hGN.ot_v _ hxN)] at hy1
      simp only [psi.injEq] at hy1
      have hsv : s = ρP.v r := by rw [hy1.1]; have := hσv 0; simpa using this
      rw [hsv]
      exact hPP.2 h0
  · -- the copies
    obtain ⟨a, rfl⟩ : ∃ a, k = r + L + a := ⟨k - (r + L), by omega⟩
    have hkN : r + L + a < (TRIO.gexp M r L d0 0 n).length := by
      have hcch : c ∈ children (TRIO.gexp M r L d0 0 n) (r + L + a) :=
        (List.mem_filter.mp (show c ∈ CL _ (r + L + a) by rw [hCL]; simp)).1
      have := mem_children hcch; omega
    have ha : a < (n - 1) * L := by rw [hlN] at hkN; omega
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
    have hc'CL : c' ∈ CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a) := by rw [hsplit]; simp
    have hc'c := mem_children (List.mem_filter.mp hc'CL).1
    have hLo : (Lc'.map (· + L)).map σ.o = Lc'.map ρP.o := by
      rw [List.map_map]
      apply List.map_congr_left
      intro d hd
      have hdCL : d ∈ CL (TRIO.gexp M r L d0 0 (n - 1)) (r + a) := by rw [hsplit]; simp [hd]
      have hdc := mem_children (List.mem_filter.mp hdCL).1
      have := hσo (d - r)
      rw [show r + L + (d - r) = d + L by omega, show r + (d - r) = d by omega] at this
      exact this
    have hoc : σ.o (c' + L) = ρP.o c' := by
      have := hσo (c' - r)
      rw [show r + L + (c' - r) = c' + L by omega, show r + (c' - r) = c' by omega] at this
      exact this
    rw [hoc] at hsy
    rw [hσv, hLo] at hrw
    have hφk : phiT1 r L (r + L + a) = phiT1 r L (r + a) := by
      rw [show r + L + a = (r + a) + L by omega]; exact phiT1_shift (by omega)
    have hφc : phiT1 r L (c' + L) = phiT1 r L c' := phiT1_shift (by omega)
    rw [hφk, hφc, hσv, hLo]
    exact hPP.1 (r + a) c' Lc' R' s y hsplit hsy hrw

end

/-- The carried property: `Inv3V3`, the chain bound, `VrLe`, and the frame map to `M`. -/
def PnV3f (M : Mat) (ρ : Valn) (r L : Nat) (N : Mat) (σ : Valn) : Prop :=
  PnV3 N σ ∧ σ.o r < ρ.o r ∧ σ.v r ≤ ρ.v r ∧ (FrameMapT1 M ρ r L N σ ∧ VrDomQ M ρ r L N σ)

open Ytosk.G Ytosk.WfExQ5 Ytosk.WfExQ6 Ytosk.WfExQ9 Ytosk.WfExQ10 Ytosk.WfQrH6 in
/-- **`ExpStepQ` of `PnV3f` with `ExDQX`**: remaining only `VSFResQ` and `FrameAtN`. -/
theorem expStepQ_V3f {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (I : Inv3V3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    (hVSF : VSFResQ M r L d0 ρ)
    (hFr : FrameAtN M r L d0) :
    ExpStepQ (PnV3f M ρ r L) (ExDQX M r L ρ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hox : ∃ t, ρ.o (r + L) = psi (succ t) z z :=
    ⟨_, o_last_t1 hlen I.cons I.good h1 (by have := par1_entry_lt h1; omega) hx2⟩
  intro n hn ρP oq vq hCP hGP hPPs hCN hGN hEX
  have hEx : ExDQY M r L ρ n ρP oq vq := ⟨hEX, hPPs.2.1⟩
  have hPP : PnV3 (TRIO.gexp M r L d0 0 (n - 1)) ρP := hPPs.1
  have hFM := expStepQR_frameMapT1 S I.cons I.good I.rank hlen hL hd0e h1 hx2 n hn ρP oq vq hCP hGP
    hPPs.2.2.2 hCN hGN hEx
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
    ⟨hPPs.2.2.1, J.vs⟩ hCN hGN hEx
  have hvs := hVV.2
  have hvra := vsmallRAll_of_mapT1 hFM.1 I.vra
  obtain ⟨F, hTP, hTPW⟩ := hFr n hn _ rkN hCN hR hGN
  refine ⟨⟨rkN, inv3V3_of_parts hCN hGN hR hS hP ⟨hvs, hfc, hfo, hkd, htd, hph, hf3, hvra⟩ F hTP hTPW⟩, ?_, hVV.1, hFM⟩
  rw [glueQ_o_dep hrx hrD]
  obtain ⟨η, hD⟩ := hEX.1.1 r hrx hrD
  exact hD.lt

open Ytosk.WfExQ9 Ytosk.WfExQ10
section
variable {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
include hlen hL hA hd0e

open Ytosk.WfQrL5 Ytosk.WfQrL6 Ytosk.WfQrL8 Ytosk.WfQrL9 Ytosk.WfQrL10 Ytosk.WfQrL16 Ytosk.WfQrL18 Ytosk.WfQrH5
  Ytosk.WfQrH6 Ytosk.WfQrH3 Ytosk.WfQrH2 in
/-- **The q = r chain carrying `Inv3V3`** (`qr_chainH3` with `Pn = PnV3f M ρ r L`, `Ex = ExDQX`; the `Ex` conjunct of
`hLocH` is gone: it follows from the C_strip conjuncts).  Remaining value residuals: `hVSF` (VSFResQ), `hFr`. -/
theorem qr_chainV3f (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
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
    (hFr : FrameAtN M r L d0)
    (hP1 : PnV3 (TRIO.gexp M r L d0 0 1) ρ1) (hs1 : ρ1.o r < ρ.o r)
    (hF1 : FrameMapT1 M ρ r L (TRIO.gexp M r L d0 0 1) ρ1 ∧ VrDomQ M ρ r L (TRIO.gexp M r L d0 0 1) ρ1) :
    ∀ n, 2 ≤ n → ∃ ρN rkN, Cons (TRIO.gexp M r L d0 0 n) ρN ∧ Rk (TRIO.gexp M r L d0 0 n) rkN ∧
      Good3 (TRIO.gexp M r L d0 0 n) ρN ∧ PnV3f M ρ r L (TRIO.gexp M r L d0 0 n) ρN ∧
      ρN.o r < ρ.o r ∧ ρN.o r < ρ.o (r + L) ∧ ρN.o r ≠ z ∧
      (∀ g, g < r + L → ¬ DepX M (r + L) false g → ρN.v g = ρ.v g) ∧
      isOT (root (TRIO.gexp M r L d0 0 n) ρN) = true ∧ root (TRIO.gexp M r L d0 0 n) ρN < root M ρ :=
  WfQrH7.qr_chainH3 hlen hL hA hd0e hpath hx2 hxnb hz2 hiu hiux hnd hC hG hRM hOS h1x hp1 hrD hRA hR0 hRlast hRd
    hsM hpM (ExDQX M r L ρ) hOSD hVS hPre
    (fun n hn ρP σ hCP hlt hne hCN => by
      obtain ⟨ho, hv, hOF, hU, hB⟩ := hLocH n hn ρP σ hCP hlt hne hCN
      exact ⟨ho, hv, WfExQ7.exDQX_of_loc n ρP hlt ho hv, hOF, hU, hB⟩)
    hC1 hR1 hG1 hv1 hPv1 (PnV3f M ρ r L) ⟨hP1, hs1, hv1, hF1⟩
    (expStepQ_V3f S I hlen hL hd0e hp1 hx2 hq hVSF hFr)

end



end Ytosk.WfExQ11
