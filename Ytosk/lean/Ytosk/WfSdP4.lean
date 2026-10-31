/-
**WfSdP4: the live `t = 1` producers over `ExpStepT1D` (2026-11-01).**

Copies (suffix `D`) of the producers of the carried property of the `q = r` chain that are live under
`trio_terminates_main_V2_cur` (tmp/wf/WfSdP/expdeps.lean): the type `ExpStepT1` → `ExpStepT1D` (WfSdP3). The three
readers of the old `hS` (`frameClosedOmN_t1S`, `G.frameQROmN_t1S`: `SeedOK v(r)` → `HoleDataW.Sr`; `vsf_frameS`:
`hole_dom` → `hole_domD` with the index-0 condition of the column read through `last` and `DiagAt.append`).
`expStepT1_of_D` turns each of them back into the old form (the `q ≠ r` chain).
-/
import Ytosk.WfSdP3
import Ytosk.V3ExpInv2
import Ytosk.V3T1VSRAll

namespace Ytosk

open T

/-- The hole information of `ExpStepT1AtD`. -/
def HoleInfoD (M : Mat) (r L n : Nat) (ρ ρP : Valn) (Z : Nat → T) : Prop :=
  ∃ μ br vr seed k0, HoleDataW M (r + L) ρ μ br vr seed ∧ OkD μ br vr seed ∧
      (∀ i, ∃ k, k0 ≤ k ∧ Z i = gamS μ br seed k ∧
        (k = 0 → ∀ bb, DepX M (r + L) bb i → i < r + L → ∀ a', ¬ lt vr a' = true →
          isOT (psi a' br z) = true → DiagAt a' br μ (valB ρ bb i) → SeedOK a' br μ seed)) ∧
    ρP.o r = gamS μ br seed k0 ∧ k0 = n - 2 ∧
    μ = vr ∧ ρ.o r = psi vr br z

section

theorem expStep_vrleSD {M : Mat} {ρ : Valn} (S : SInv M)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) : ExpStepT1D (VrLe r ρ) M r L d0 ρ := by
  intro n hn ρP Z _ _ _ _ _ _ _ _ _ _
  have hrx : r < r + L := par_lt M 1 _ r h1
  show (glueZ M (r + L) ρ (shiftV ρP L) Z).v r ≤ ρ.v r
  rw [glueZ_v_lt ρ (shiftV ρP L) Z hrx (not_depX_v_r1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab h1 hx2)]
end


section

/-- **FrameClosedOmN of the glued valuation** (`t = 1`), from the chain's hole information. Below `x` a
counted child with old value `Ω_{t+1}` is not in `D` (its new value is the old one, no trigger). At `x`:
for `q ≠ r` no trigger (F1); for `q = r` the new argument is `b + δ` with `δ < Ω_{μ+1}` (`frameDom_app`). -/
theorem frameClosedOmN_t1SD {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rk)
    {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hn : 2 ≤ n)
    {ρP : Valn} {Z : Nat → T}
    (hGN : Good3 (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z))
    (hlex : ρP.o r ≤ ρ.o (r + L) ∧ ρP.o r ≠ z)
    (hH : ∃ μ br vr seed k0, HoleDataW M (r + L) ρ μ br vr seed ∧ OkD μ br vr seed ∧
      (∀ i, ∃ k, k0 ≤ k ∧ Z i = gamS μ br seed k ∧
        (k = 0 → ∀ bb, DepX M (r + L) bb i → i < r + L → ∀ a', ¬ lt vr a' = true →
          isOT (psi a' br z) = true → DiagAt a' br μ (valB ρ bb i) → SeedOK a' br μ seed)) ∧ ρP.o r = gamS μ br seed k0 ∧ k0 = n - 2 ∧
      μ = vr ∧ ρ.o r = psi vr br z) :
    FrameClosedOmN M r L ρ (glueZ M (r + L) ρ (shiftV ρP L) Z) := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hOS := hOS_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq
  have hox := o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2
  obtain ⟨μ', br', vr', seed, k0, hHD, _, _, hPr, hk0n, hμv, hro'⟩ := hH
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hσx : σ.o (r + L) = ρP.o r := by
    rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (Nat.le_refl _)]
    show ρP.o (r + L - L) = ρP.o r; rw [Nat.add_sub_cancel]
  intro i hi Lc c R hCL t hct htv s y hc ⟨ht1, ht2⟩
  have hcCL : c ∈ CL M i := by rw [hCL]; simp
  have hcm : c ∈ children M i := cl_mem_children hcCL
  have hcnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
  have hcM := (mem_children hcm).2
  rcases Nat.lt_or_ge c (r + L) with hc' | hc'
  · exfalso
    by_cases hd : DepX M (r + L) true c
    · rcases hOS c hc' hd with ⟨hvc, hnc⟩ | ⟨_, L', c', R', hch', hcb', hcu', hR', _⟩
      · have hHv := hHD.hole false c hvc hc'
        simp only [valB, cond_false] at hHv
        have hoc := o_nocnt hC hG hcM hnc
        rw [hct] at hoc
        have hs : succ t = ρ.v c := (T.psi.inj hoc).1
        have := holeT_not_succ hHv
        rw [← hs, isSucc_succ] at this; cases this
      · have hc'M := (mem_children (by rw [hch']; exact List.mem_append_right _ List.mem_cons_self :
          c' ∈ children M c)).2
        have hfr := o_frame hC hG hcM hch' hcb' hcu' hR' hc'M
        obtain ⟨s3, y3, hc3⟩ := o_psi_form hC hc'M
        rw [hc3, spArg_single, hct] at hfr
        exact step_ne_z' _ _ _ _ _ (T.psi.inj hfr).2.1.symm
    · rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hc' hd, hct] at hc
      rw [← (T.psi.inj hc).2.1] at ht1
      exact T.not_lt_z _ ht1
  have hcx : c = r + L := by omega
  subst hcx
  have hix : par M 0 (r + L) = some i := (mem_children_iff.mp hcm).2
  have hiq : i = q := Option.some.inj (hix.symm.trans hq)
  subst hiq
  have hsy : psi s y z ≤ psi (succ (ρ.v r)) z z := by rw [← hc, hσx, ← hox]; exact hlex.1
  have hyz : y ≠ z := by intro h'; rw [h'] at ht1; exact T.not_lt_z _ ht1
  have hsr : s ≤ ρ.v r := by
    rcases (le_iff _ _).mp hsy with h' | h'
    · rcases psi_lt_psi_z_iff.mp h' with h'' | ⟨_, h''⟩
      · exact lt_succ_iff.mp h''
      · exact absurd h'' (T.not_lt_z _)
    · exact absurd (T.psi.inj h').2.1 hyz
  have his : ρ.v i ≤ s := by
    rcases psi_lt_psi_z_iff.mp ht2 with h' | ⟨h', _⟩
    · exact le_of_lt h'
    · rw [h']
  by_cases hqr : i = r
  · subst hqr
    obtain ⟨b, hro, hbe, hb⟩ := qr_o_r hlen S.r0p S.sibDec h1 hx2 hq hC hG hRM
    have hsμ : s = ρ.v i := le_antisymm hsr his
    subst hsμ
    -- the state is `b`
    have hRn : R = [] := by
      rcases R with _ | ⟨d, R'⟩
      · rfl
      · exfalso
        have hdCL : d ∈ CL M i := by rw [hCL]; simp
        have hdm := cl_mem_children hdCL
        have hsort := children_sorted M i
        have hdx : d ≤ i + L := by have := (mem_children hdm).2; omega
        have hCLs : (CL M i).Pairwise (· < ·) := List.Pairwise.filter _ hsort
        rw [hCL] at hCLs
        have := (List.pairwise_cons.mp (List.pairwise_append.mp hCLs).2.1).1 d (by simp)
        omega
    subst hRn
    have hBb : spArg (ρ.v i) z (sumN (Lc.map ρ.o)) = b := by
      have hcv := cvals_eq_map hC hG i
      rw [hCL] at hcv
      unfold cvals at hcv
      rw [qr_children hlen h1 hx2 hq, List.map_append, nzs_append] at hcv
      have hxc := qr_x_counted hlen h1 hx2 hq
      have hox0 : ρ.o (i + L) ≠ z := by rw [hox]; simp
      have hlast : nzs ([i + L].map (cnt M ρ i)) = [ρ.o (i + L)] := by
        simp only [List.map_cons, List.map_nil]
        rw [cnt_cnt ρ hxc.1 hxc.2]
        simp [nzs, hox0]
      rw [hlast, List.map_append, List.map_singleton] at hcv
      have := List.append_cancel_right hcv
      rw [hbe]; unfold preState; rw [this]
    rw [hBb] at ht1 ⊢
    -- pin the hole data
    rw [hro] at hro'
    obtain ⟨hvr, hbr', _⟩ := T.psi.inj hro'
    subst hvr hμv hbr'
    have hot : isOT (psi (ρ.v i) (app b (psi (succ (ρ.v i)) z z)) z) = true := by
      rw [← hro]; exact hG.ot_o i (by omega)
    have hSr := hHD.Sr
    have hcbr : cof (app b (psi (succ (ρ.v i)) z z)) = .big (ρ.v i) := cof_br
    have hotN : isOT (psi (ρ.v i) y z) = true := by rw [← hc]; exact hGN.ot_o (i + L) (by rw [hlN]; have := Nat.mul_pos (show 0 < n - 1 by omega) hL; omega)
    have hsa : ∀ u, ¬ lt (ρ.v i) u = true → ∀ g ∈ comps u (ρ.v i), ∃ d ∈ comps u (ρ.v i), g ≤ d :=
      fun _ _ g hg => ⟨g, hg, le_refl _⟩
    -- the new argument is `b + δ`
    rw [hσx, hPr] at hc
    cases k0 with
    | succ j =>
      change psi (ρ.v i) (fs (app b (psi (succ (ρ.v i)) z z)) (gamS (ρ.v i) _ seed j)) z = psi (ρ.v i) y z at hc
      rw [fs_br] at hc
      have hy := (T.psi.inj hc).2.1
      subst hy
      have hseedz : seed ≠ z := by obtain ⟨a, X, h⟩ := hHD.seedS; rw [h]; simp
      exact frameDom_app hb (gamS_ne_z_gen hseedz j)
        (gamS_lt_om hot hcbr (lt_irrefl' _) hSr j) hotN hsa
    | zero =>
      change seed = psi (ρ.v i) y z at hc
      have hnext := hSr.lt_next
      rw [fs_br, hc] at hnext
      have hyb : y < app b (psi (ρ.v i) y z) := by
        rcases psi_lt_psi_z_iff.mp hnext with h' | ⟨_, h'⟩
        · exact absurd h' (lt_irrefl' _)
        · exact h'
      obtain ⟨c0, hc0, hc0z, hc0le⟩ := between_app (A := b) (x := z) (y := psi (ρ.v i) y z) (c := y)
        (by rw [app_z_right]; exact ht1) (le_of_lt hyb)
      have hc0z' : c0 ≠ z := by intro h'; rw [h'] at hc0z; exact T.not_lt_z _ hc0z
      have hc0lt : c0 < psi (succ (ρ.v i)) z z := by
        apply lt_of_le_of_lt hc0le
        rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self _)
      rw [hc0] at hotN ⊢
      exact frameDom_app hb hc0z' hc0lt hotN hsa
  · -- `q ≠ r`: no trigger (F1)
    exfalso
    have hqr' : par M 0 (r + L) ≠ some r := fun h' => hqr (Option.some.inj (hq.symm.trans h'))
    have hri : r < i := by
      rcases Nat.eq_or_lt_of_le (par0_ge_of_anc hA (show r < r + L by omega) (Nat.le_refl _) hix) with h' | h'
      · exact absurd h'.symm hqr
      · exact h'
    have hdi : DepX M (r + L) true i := dep_anc_x S.uat S.z2 S.r12 S.bumpE2 hlen hx2 (anc0_of_par M 0 i _ hix)
    have hvi : ¬ DepX M (r + L) false i := by
      rcases hOS i hi hdi with ⟨_, hnc⟩ | ⟨hv', _⟩
      · rcases hnc _ hcm with h' | h'
        · exact absurd h' hcnt.1
        · exact absurd h' hcnt.2
      · exact hv'
    have hF := hF1_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab h1 hC hG hRM i hri hi hdi hvi
    exact lt_irrefl' _ (lt_of_lt_of_le hF (le_trans his hsr))
end


section

/-- **FrameClosed is carried** (`t = 1`), with no residual. -/
theorem expStep_frameClosed_t1SD {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rk) (hFC : FrameClosed M ρ)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    ExpStepT1D (fun N σ => FrameClosed N σ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hox : ∃ t, ρ.o (r + L) = psi (succ t) z z :=
    ⟨_, o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2⟩
  intro n hn ρP Z hCP _ hFCP _ hGN hoto _ hle hlex hH
  have hxnb := hxnb_t1 hlen hL hA hd0e S.z2 S.z1c h1 n hn
  have hiu := hiu_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn
  have hiux := hiux_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn
  have hOS := hOS_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq
  exact frameClosed_N_t1 hlen hL hA hd0e hn hpath hx2 hxnb (S.z2 r) hiu hiux hCP hOS hC hG hFC
    (frameClosedOmN_t1SD S hC hG hRM hlen hL hd0e h1 hx2 hn hGN hlex hH) hoto hFCP
    (fun c hc hd => (hle c hc hd).1) hlex.1 hox
end


section

/-- **FrameOT is carried along the chain of expansions.** -/
theorem expStep_frameOTD {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ n, 2 ≤ n → ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ n, 2 ≤ n → ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : ∀ n, 2 ≤ n → isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    {ρ : Valn} (hFO : FrameOT M ρ)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i) :
    ExpStepT1D FrameOT M r L d0 ρ := by
  intro n hn ρP Z hCP _ hFOP _ _ _ _ _ _ _
  exact frameOT_N_t1 hlen hL hA hd0e hn hpath hx2 (hxnb n hn) hz2 (hiu n hn) (hiux n hn) hCP hFO hFOP hOS
end


section

/-- **FrameOT is carried** (`t = 1`), with the structural hypotheses from the invariants of `M`. -/
theorem expStep_frameOT_t1D {M : Mat} {r L d0 q : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some q)
    {ρ : Valn} (hFO : FrameOT M ρ) : ExpStepT1D FrameOT M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  exact expStep_frameOTD hlen hL hA hd0e hpath hx2 (hxnb_t1 hlen hL hA hd0e hZ2 hZ1 h1) (hZ2 r)
    (fun n hn => hiu_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn)
    (fun n hn => hiux_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn) hFO
    (hOS_t1 hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq)
end


namespace G
section

/-- **The residual of the glued valuation** (`t = 1`), for a property that holds when the new argument
extends the state by `0 < δ < Ω_{s+1}` (as in `frameClosedOmN_t1`). -/
theorem frameQROmN_t1SD (Q' : T → List T → T → T → Prop)
    (hQapp : ∀ a Lv s b δ, spArg a z (sumN Lv) = b → AllGeT (psi (succ s) z z) b → δ ≠ z →
      δ < psi (succ s) z z → Q' a Lv s (app b δ))
    {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rk)
    {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hn : 2 ≤ n)
    {ρP : Valn} {Z : Nat → T}
    (hGN : Good3 (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z))
    (hlex : ρP.o r ≤ ρ.o (r + L) ∧ ρP.o r ≠ z)
    (hH : ∃ μ br vr seed k0, HoleDataW M (r + L) ρ μ br vr seed ∧ OkD μ br vr seed ∧
      (∀ i, ∃ k, k0 ≤ k ∧ Z i = gamS μ br seed k ∧
        (k = 0 → ∀ bb, DepX M (r + L) bb i → i < r + L → ∀ a', ¬ lt vr a' = true →
          isOT (psi a' br z) = true → DiagAt a' br μ (valB ρ bb i) → SeedOK a' br μ seed)) ∧ ρP.o r = gamS μ br seed k0 ∧ k0 = n - 2 ∧
      μ = vr ∧ ρ.o r = psi vr br z) :
    ∀ i, i < r + L → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → ∀ t,
      ρ.o c = psi (succ t) z z → ¬ lt t (ρ.v i) = true →
      QR Q' (ρ.v i) (Lc.map ρ.o) ((glueZ M (r + L) ρ (shiftV ρP L) Z).o c) := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hOS := hOS_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq
  have hox := o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2
  obtain ⟨μ', br', vr', seed, k0, hHD, _, _, hPr, hk0n, hμv, hro'⟩ := hH
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hσx : σ.o (r + L) = ρP.o r := by
    rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (Nat.le_refl _)]
    show ρP.o (r + L - L) = ρP.o r; rw [Nat.add_sub_cancel]
  intro i hi Lc c R hCL t hct htv s y hc ⟨ht1, ht2⟩
  have hcCL : c ∈ CL M i := by rw [hCL]; simp
  have hcm : c ∈ children M i := cl_mem_children hcCL
  have hcnt : Counted M i c := by unfold CL at hcCL; simpa using (List.mem_filter.mp hcCL).2
  have hcM := (mem_children hcm).2
  rcases Nat.lt_or_ge c (r + L) with hc' | hc'
  · exfalso
    by_cases hd : DepX M (r + L) true c
    · rcases hOS c hc' hd with ⟨hvc, hnc⟩ | ⟨_, L', c', R', hch', hcb', hcu', hR', _⟩
      · have hHv := hHD.hole false c hvc hc'
        simp only [valB, cond_false] at hHv
        have hoc := o_nocnt hC hG hcM hnc
        rw [hct] at hoc
        have hs : succ t = ρ.v c := (T.psi.inj hoc).1
        have := holeT_not_succ hHv
        rw [← hs, isSucc_succ] at this; cases this
      · have hc'M := (mem_children (by rw [hch']; exact List.mem_append_right _ List.mem_cons_self :
          c' ∈ children M c)).2
        have hfr := o_frame hC hG hcM hch' hcb' hcu' hR' hc'M
        obtain ⟨s3, y3, hc3⟩ := o_psi_form hC hc'M
        rw [hc3, spArg_single, hct] at hfr
        exact step_ne_z' _ _ _ _ _ (T.psi.inj hfr).2.1.symm
    · rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hc' hd, hct] at hc
      rw [← (T.psi.inj hc).2.1] at ht1
      exact T.not_lt_z _ ht1
  have hcx : c = r + L := by omega
  subst hcx
  have hix : par M 0 (r + L) = some i := (mem_children_iff.mp hcm).2
  have hiq : i = q := Option.some.inj (hix.symm.trans hq)
  subst hiq
  have hsy : psi s y z ≤ psi (succ (ρ.v r)) z z := by rw [← hc, hσx, ← hox]; exact hlex.1
  have hyz : y ≠ z := by intro h'; rw [h'] at ht1; exact T.not_lt_z _ ht1
  have hsr : s ≤ ρ.v r := by
    rcases (le_iff _ _).mp hsy with h' | h'
    · rcases psi_lt_psi_z_iff.mp h' with h'' | ⟨_, h''⟩
      · exact lt_succ_iff.mp h''
      · exact absurd h'' (T.not_lt_z _)
    · exact absurd (T.psi.inj h').2.1 hyz
  have his : ρ.v i ≤ s := by
    rcases psi_lt_psi_z_iff.mp ht2 with h' | ⟨h', _⟩
    · exact le_of_lt h'
    · rw [h']
  by_cases hqr : i = r
  · subst hqr
    obtain ⟨b, hro, hbe, hb⟩ := qr_o_r hlen S.r0p S.sibDec h1 hx2 hq hC hG hRM
    have hsμ : s = ρ.v i := le_antisymm hsr his
    subst hsμ
    have hRn : R = [] := by
      rcases R with _ | ⟨d, R'⟩
      · rfl
      · exfalso
        have hdCL : d ∈ CL M i := by rw [hCL]; simp
        have hdm := cl_mem_children hdCL
        have hsort := children_sorted M i
        have hdx : d ≤ i + L := by have := (mem_children hdm).2; omega
        have hCLs : (CL M i).Pairwise (· < ·) := List.Pairwise.filter _ hsort
        rw [hCL] at hCLs
        have := (List.pairwise_cons.mp (List.pairwise_append.mp hCLs).2.1).1 d (by simp)
        omega
    subst hRn
    have hBb : spArg (ρ.v i) z (sumN (Lc.map ρ.o)) = b := by
      have hcv := cvals_eq_map hC hG i
      rw [hCL] at hcv
      unfold cvals at hcv
      rw [qr_children hlen h1 hx2 hq, List.map_append, nzs_append] at hcv
      have hxc := qr_x_counted hlen h1 hx2 hq
      have hox0 : ρ.o (i + L) ≠ z := by rw [hox]; simp
      have hlast : nzs ([i + L].map (cnt M ρ i)) = [ρ.o (i + L)] := by
        simp only [List.map_cons, List.map_nil]
        rw [cnt_cnt ρ hxc.1 hxc.2]
        simp [nzs, hox0]
      rw [hlast, List.map_append, List.map_singleton] at hcv
      have := List.append_cancel_right hcv
      rw [hbe]; unfold preState; rw [this]
    rw [hBb] at ht1
    rw [hro] at hro'
    obtain ⟨hvr, hbr', _⟩ := T.psi.inj hro'
    subst hvr hμv hbr'
    have hot : isOT (psi (ρ.v i) (app b (psi (succ (ρ.v i)) z z)) z) = true := by
      rw [← hro]; exact hG.ot_o i (by omega)
    have hSr := hHD.Sr
    have hcbr : cof (app b (psi (succ (ρ.v i)) z z)) = .big (ρ.v i) := cof_br
    rw [hσx, hPr] at hc
    cases k0 with
    | succ j =>
      change psi (ρ.v i) (fs (app b (psi (succ (ρ.v i)) z z)) (gamS (ρ.v i) _ seed j)) z = psi (ρ.v i) y z at hc
      rw [fs_br] at hc
      have hy := (T.psi.inj hc).2.1
      subst hy
      have hseedz : seed ≠ z := by obtain ⟨a, X, h⟩ := hHD.seedS; rw [h]; simp
      exact hQapp _ _ _ _ _ hBb hb (gamS_ne_z_gen hseedz j) (gamS_lt_om hot hcbr (lt_irrefl' _) hSr j)
    | zero =>
      change seed = psi (ρ.v i) y z at hc
      have hnext := hSr.lt_next
      rw [fs_br, hc] at hnext
      have hyb : y < app b (psi (ρ.v i) y z) := by
        rcases psi_lt_psi_z_iff.mp hnext with h' | ⟨_, h'⟩
        · exact absurd h' (lt_irrefl' _)
        · exact h'
      obtain ⟨c0, hc0, hc0z, hc0le⟩ := between_app (A := b) (x := z) (y := psi (ρ.v i) y z) (c := y)
        (by rw [app_z_right]; exact ht1) (le_of_lt hyb)
      have hc0z' : c0 ≠ z := by intro h'; rw [h'] at hc0z; exact T.not_lt_z _ hc0z
      have hc0lt : c0 < psi (succ (ρ.v i)) z z := by
        apply lt_of_le_of_lt hc0le
        rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self _)
      rw [hc0]
      exact hQapp _ _ _ _ _ hBb hb hc0z' hc0lt
  · -- `q ≠ r`: no trigger (F1)
    exfalso
    have hri : r < i := by
      rcases Nat.eq_or_lt_of_le (par0_ge_of_anc hA (show r < r + L by omega) (Nat.le_refl _) hix) with h' | h'
      · exact absurd h'.symm hqr
      · exact h'
    have hdi : DepX M (r + L) true i := dep_anc_x S.uat S.z2 S.r12 S.bumpE2 hlen hx2 (anc0_of_par M 0 i _ hix)
    have hvi : ¬ DepX M (r + L) false i := by
      rcases hOS i hi hdi with ⟨_, hnc⟩ | ⟨hv', _⟩
      · rcases hnc _ hcm with h' | h'
        · exact absurd h' hcnt.1
        · exact absurd h' hcnt.2
      · exact hv'
    have hF := hF1_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab h1 hC hG hRM i hri hi hdi hvi
    exact lt_irrefl' _ (lt_of_lt_of_le hF (le_trans his hsr))
end

end G

namespace G
section

/-- **PH3cG is carried** (`t = 1`). -/
theorem expStep_ph3c_t1SD {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rk) (hP : PH3cG M ρ)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    ExpStepT1D (fun N σ => PH3cG N σ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hox : ∃ t, ρ.o (r + L) = psi (succ t) z z :=
    ⟨_, o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2⟩
  intro n hn ρP Z hCP _ hPP _ hGN _ _ hle hlex hH
  have hxnb := hxnb_t1 hlen hL hA hd0e S.z2 S.z1c h1 n hn
  have hiu := hiu_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn
  have hiux := hiux_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn
  have hOS := hOS_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq
  exact ph3c_iff.mpr (frameQR_N_t1 hlen hL hA hd0e hn PH' (fun _ _ _ _ _ hyy ht h => ph'_drop hyy ht h)
    hpath hx2 hxnb (S.z2 r) hiu hiux hCP hOS hC (ph3c_iff.mp hP)
    (frameQROmN_t1SD PH' (fun _ _ _ _ _ hb hge hδz hδ => ph'_app hb hge hδz hδ) S hC hG hRM hlen hL hd0e h1 hx2 hn hGN
      hlex hH)
    (ph3c_iff.mp hPP) (fun c hc hd => (hle c hc hd).1) hlex.1 hox)
end

end G

namespace G
section

/-- **FC3 is carried** (`t = 1`). -/
theorem expStep_fc3_t1SD {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ) (hRM : Rk M rk) (hP : FC3 M ρ)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    ExpStepT1D (fun N σ => FC3 N σ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hox : ∃ t, ρ.o (r + L) = psi (succ t) z z :=
    ⟨_, o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2⟩
  intro n hn ρP Z hCP _ hPP _ hGN _ _ hle hlex hH
  have hxnb := hxnb_t1 hlen hL hA hd0e S.z2 S.z1c h1 n hn
  have hiu := hiu_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn
  have hiux := hiux_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn
  have hOS := hOS_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq
  exact fc3_iff.mpr (frameQR_N_t1 hlen hL hA hd0e hn F3' (fun _ _ _ _ _ hyy ht h => f3'_drop hyy ht h)
    hpath hx2 hxnb (S.z2 r) hiu hiux hCP hOS hC (fc3_iff.mp hP)
    (frameQROmN_t1SD F3' (fun _ _ _ _ _ hb hge hδz hδ => f3'_app hb hge hδz hδ) S hC hG hRM hlen hL hd0e h1 hx2 hn hGN
      hlex hH)
    (fc3_iff.mp hPP) (fun c hc hd => (hle c hc hd).1) hlex.1 hox)
end

end G

section

/-- **The root order is carried** (`t = 1`), with the structural hypotheses from the invariants of `M`. -/
theorem expStep_rootP_t1D {M : Mat} {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hZ2 : Z2 M) (hUAT : UAT M) (hR12 : R12 M) (hBE : BumpE2 M) (hR01 : R01 M) (h00 : entry M 0 0 = 0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    {ρ : Valn} (hpM : RootP M ρ) : ExpStepT1D RootP M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨Rt, hRA, hRt0, hRlast⟩ := root_t1 hR01 hR12 h00 (r + L)
  have hRd := dep_anc_x hUAT hZ2 hR12 hBE hlen hx2 hRA
  have hRx : Rt < r + L := by
    rcases Nat.lt_or_ge Rt (r + L) with h | h
    · exact h
    · exfalso
      have : Rt = r + L := by have := hRA.le; omega
      rw [this] at hRt0
      have h2 := congrArg (fun p : Nat × Nat × Nat => p.2.1) hRt0
      have he : entry M 1 (r + L) = 0 := by
        unfold entry; unfold col at h2; simpa using h2
      have := par1_entry_lt h1; omega
  intro n hn ρP Z _ _ _ _ _ _ _ hle _ _
  exact rootP_N_t1 hlen hL hA hd0e hn hRA hRt0 hRlast hRd hpM (hle Rt hRx hRd).1
end


section

/-- **BumpKidsDec and BumpTermDec are carried** (`t = 1`), with the structural hypotheses from the invariants
of `M`. -/
theorem expStep_bumpDec_t1D {M : Mat} {r L d0 q : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some q)
    {ρ : Valn} (hG : Good3 M ρ) (hB : BumpDec M ρ) : ExpStepT1D BumpDec M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hVS : ∀ i, i < r + L → DepX M (r + L) false i → VShape M (r + L) i :=
    fun i hi hv => dv_shape hlen hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hi hv
  intro n hn ρP Z _ _ hBP _ hGN _ _ hle hlex _
  have hlN := len_N (d0 := d0) hlen hn
  have hxnb := hxnb_t1 hlen hL hA hd0e hZ2 hZ1 h1 n hn
  have hiu := hiu_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn
  have hiux := hiux_t1 hlen hL hA hd0e hpath hx2 (hZ2 r) hn
  exact ⟨bumpKidsDec_N_t1 hlen hL hA hd0e hn hpath hx2 hxnb (hZ2 r) hiu hiux hVS hle hlex hB.1 hBP.1,
    bumpTermDec_N_t1 hlen hL hA hd0e hn hpath hx2 hxnb (hZ2 r) hiu hiux hVS hle hlex hG
      (fun k hk => hGN.ot_o k (by have := Nat.mul_pos (show 0 < n - 1 by omega) hL; omega)) hB.2 hBP.2⟩
end


section

/-- **The passing cofinality is above the chain level at the parent** (with an earlier counted child). -/
theorem mu_lt_viSD {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ) (hRM : Rk M rk) (V : ValInv M ρ)
    {r L : Nat} (hlen : r + L + 1 = M.length) (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hPR : PassRootRes M r L ρ)
    {μ br vr seed : T} (hHD : HoleDataW M (r + L) ρ μ br vr seed) (hμv : μ = vr) (hro : ρ.o r = psi vr br z)
    {i : Nat} {Lc : List Nat} {c : Nat} {R : List Nat} (hi : i < r + L) (hCL : CL M i = Lc ++ c :: R)
    (hcd : DepX M (r + L) false c) (hcx : c < r + L)
    (hcof : cof (last (ρ.v c)) = .big μ) (hLc : Lc ≠ []) : lt μ (ρ.v i) = true := by
  have hrx : r < r + L := par_lt M 1 _ r h1
  have hrM : r < M.length := by omega
  have hvr : vr = ρ.v r := chain_level hC V.g hrM hro
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hcCL : c ∈ CL M i := by rw [hCL]; simp
  have hcch : c ∈ children M i := (List.mem_filter.mp hcCL).1
  have hccnt : Counted M i c := by simpa using (List.mem_filter.mp hcCL).2
  have h0 : par M 0 c = some i := (mem_children_iff.mp hcch).2
  have hcofv : cof (ρ.v c) = .big μ := by rw [← cof_last_g]; exact hcof
  have hrc : r < c := by
    by_contra hcr
    have hOS := hOS_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq
    have hF1 : ∀ j, r < j → j < r + L → DepX M (r + L) true j → ¬ DepX M (r + L) false j →
        lt μ (ρ.v j) = true := by
      intro j h2 h3 h4 h5
      rw [hμv, hvr]
      exact hF1_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab h1 hC V.g hRM j h2 h3 h4 h5
    have hox : ρ.o (r + L) = psi (succ μ) z z := by
      rw [o_last_t1 hlen hC V.g h1 (by have := par1_entry_lt h1; omega) hx2, ← hvr, ← hμv]
    have hbr : br ≠ z := by
      intro h; have := hHD.cb; rw [h] at this; simp [cof] at this
    have hH := t1_hole0 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq hC V.g V.kd V.td hrx hA hro
      hHD.cb hμv hbr (Or.inl (by rw [hox]; exact cof_omega_succ μ)) hF1 hOS (hS2_t1 S.r0p hA (by omega))
      (hS3_t1 h1 hA (by omega) hlen S.r0p S.z2 S.sibDec S.z1c) false c hcd (Or.inl hcx)
    obtain ⟨a', _, hD⟩ := hH.2.1 (by omega)
    simp only [valB, cond_false] at hD
    rw [hD.cof_omega] at hcofv
    cases hcofv
  have hri : r ≤ i := par0_ge_of_anc hA hrc (by omega) h0
  rcases Nat.eq_or_lt_of_le hri with h | h
  · subst h
    exact absurd (hPR Lc c R hCL hcd hcx (by rw [hcof, hμv, hvr])) hLc
  · have hdi : DepX M (r + L) true i := DepX.ochild hcch hccnt.1 hccnt.2 (DepX.ov hcd)
    have hvd : ¬ DepX M (r + L) false i := fun hv =>
      uncnt_of_depv hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq hi hv hcch hccnt
    rw [hμv, hvr]
    exact hF1_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab h1 hC V.g hRM i h hi hdi hvd
end


section

/-- **VSFRes2 at one frame** (`t = 1`): the frame `(i, c)` with `c` a `v` call of `D`. Residual `PassRootRes`. -/
theorem vsf_frameSD {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ) (hRM : Rk M rk) (V : ValInv M ρ)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    {n : Nat} (hn : 2 ≤ n) {ρP : Valn} {Z : Nat → T} (hH : HoleInfoD M r L n ρ ρP Z)
    (hCN : Cons (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z))
    (hGN : Good3 (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z))
    {i : Nat} (hi : i < r + L) {Lc : List Nat} {c : Nat} {R : List Nat} (hCL : CL M i = Lc ++ c :: R)
    (hcd : DepX M (r + L) false c) (hcx : c < r + L)
    (hPR : PassRootRes M r L ρ) :
    ∀ g ∈ comps (ρ.v i) ((glueZ M (r + L) ρ (shiftV ρP L) Z).v c),
      g ≤ psi ((glueZ M (r + L) ρ (shiftV ρP L) Z).v c) z z ∨ g ≤ spArg (ρ.v i) z (sumN (Lc.map ρ.o)) := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q0, hq0⟩ := par0_of_anc hA (by omega)
  have hpath := hpath_of_par1 h1 hA (by omega)
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2
    (hxnb_t1 hlen hL hA hd0e S.z2 S.z1c h1 n hn)
    (hiu_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn) (hiux_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn)
  have hiM : i < M.length := by omega
  have hcCL : c ∈ CL M i := by rw [hCL]; simp
  have hcch : c ∈ children M i := (List.mem_filter.mp hcCL).1
  have hccnt : Counted M i c := by simpa using (List.mem_filter.mp hcCL).2
  have hcM := (mem_children hcch).2
  have h0 : par M 0 c = some i := (mem_children_iff.mp hcch).2
  have hCLeq : ∀ j, j < r + L → CL (TRIO.gexp M r L d0 0 n) j = CL M j := by
    intro j hj
    have hS := hSA j hj
    unfold CL; rw [hS.ch]
    apply List.filter_congr
    intro d hd
    exact decide_eq_decide.mpr (counted_iff_of_cnt (hS.cnt d hd))
  have hvd : ¬ DepX M (r + L) false i := fun hv =>
    uncnt_of_depv hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq0 hi hv hcch hccnt
  have hvi : σ.v i = ρ.v i := by rw [hσ, glueZ_v_lt ρ (shiftV ρP L) Z hi hvd]
  have hcN : c < (TRIO.gexp M r L d0 0 n).length := by rw [hlN]; omega
  have hvcot : isOT (σ.v c) = true := hGN.ot_v c hcN
  intro g hg
  by_cases hlt : σ.v c < ρ.v i
  · rw [comps_nil_of_le hvcot (le_of_lt hlt)] at hg; simp at hg
  have hge : ¬ lt (σ.v c) (ρ.v i) = true := hlt
  have hR : R = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro d hd
    have hdCL : d ∈ CL M i := by rw [hCL]; simp [hd]
    have hdch : d ∈ children M i := (List.mem_filter.mp hdCL).1
    have hdcnt : Counted M i d := by simpa using (List.mem_filter.mp hdCL).2
    have hcd' : c < d := by
      have hs : (CL M i).Pairwise (· < ·) := (children_sorted M i).filter _
      rw [hCL] at hs
      exact List.rel_of_pairwise_cons (List.pairwise_append.mp hs).2.1 hd
    exact p1_dep hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq0 hi hcch hdch hcd' (DepX.ov hcd) hdcnt
  subst hR
  have hCLcM : CL M c = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro d hd
    exact uncnt_of_depv hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq0 hcx hcd (List.mem_filter.mp hd).1
      (by simpa using (List.mem_filter.mp hd).2)
  have hoc : σ.o c = psi (σ.v c) z z := by
    rw [o_cl_eq hCN hGN hcN, hCLeq c hcx, hCLcM]; rfl
  by_cases hLc : Lc = []
  · subst hLc
    left
    have hCLN : CL (TRIO.gexp M r L d0 0 n) i = [c] := by rw [hCLeq i hi, hCL]; rfl
    have hoi := o_cl_eq hCN hGN (show i < (TRIO.gexp M r L d0 0 n).length by rw [hlN]; omega)
    rw [hCLN, List.map_singleton, hoc] at hoi
    have hsum : sumN [psi (σ.v c) z z] = psi (σ.v c) z z := by
      show sf (add z (psi (σ.v c) z z)) = _
      exact sf_ot (by simp [isOT, hvcot, comps])
    have hsp : spArg (σ.v i) z (psi (σ.v c) z z) = psi (σ.v c) z z := by
      rw [spArg_cons]
      unfold step
      rw [if_neg (fun h => T.not_lt_z _ h.1)]
      rfl
    rw [hsum, hsp] at hoi
    have hot := hGN.ot_o i (by rw [hlN]; omega)
    rw [hoi] at hot
    have hall : ∀ g ∈ comps (σ.v i) (psi (σ.v c) z z), lt g (psi (σ.v c) z z) = true := by
      simp only [isOT, Bool.and_eq_true, List.all_eq_true] at hot
      exact hot.2
    rw [hvi] at hall
    exact le_of_lt (hall g (by simp [comps, hge, hg]))
  · right
    obtain ⟨μ, br, vr, seed, k0, hHD, hokD, hZk, _, _, hμv, hro⟩ := hH
    obtain ⟨k, _, hZe, hk0⟩ := hZk c
    have hvc0 : ρ.v c ≠ z := by
      intro h0'
      rw [hσ, glueZ_v_dep ρ (shiftV ρP L) Z hcx hcd, h0'] at hg
      simp [fsD, comps] at hg
    rw [hσ, glueZ_v_dep ρ (shiftV ρP L) Z hcx hcd, fsD_init_last hvc0, comps_app,
      comps_init_v_nil hC V.g hRM hcM h0, List.nil_append, hZe] at hg
    have hHv := hHD.hole false c hcd hcx
    simp only [valB, cond_false] at hHv
    have hWot : isOT (last (ρ.v c)) = true := isOT_last (V.g.ot_v c hcM)
    obtain ⟨y, hy, hgy⟩ := hole_domD hHD.rot hHD.cb hHD.hμ hHD.Sr hokD hWot (holeT_last hHv) k
      (fun hk a' ha hot' hD => hk0 hk false hcd hcx a' ha hot' (by
        have h' := DiagAt.append (init (ρ.v c)) (last_ne_z'' hvc0) hD
        rw [init_app_last] at h'; exact h')) (ρ.v i) g hg
    have hocM : ρ.o c = psi (ρ.v c) z z := by
      rw [o_cl_eq hC V.g hcM, hCLcM]; rfl
    have hOmB := om_le_state hC V.g hiM hCL hocM hLc
    rcases hy with hy | rfl | ⟨hcof, hy⟩
    · rcases V.vs i hiM Lc c [] hCL y (comps_last_sub1 _ _ y hy) with h | h
      · exact le_trans hgy (le_trans h hOmB)
      · exact le_trans hgy h
    · exact le_trans hgy (z_le _)
    · have hSr := hHD.Sr
      rw [comps_gamS_nil hHD.seedS hSr.lt_om (mu_lt_viSD S hC hRM V hlen h1 hx2 hPR hHD hμv hro hi hCL hcd hcx hcof hLc) k] at hy
      simp at hy
end


section

/-- **VSmallF is carried** (`t = 1`) with the frames of the `v` calls of `D` done by `vsf_frameSD`; residual
`PassRootRes` only. -/
theorem expStep_vsmallF2SD {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ) (hRM : Rk M rk) (V : ValInv M ρ)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hPR : PassRootRes M r L ρ) :
    ExpStepT1D (fun N σ => VrLe r ρ N σ ∧ VSmallF N σ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q0, hq0⟩ := par0_of_anc hA (by omega)
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hOS := hOS_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq0
  intro n hn ρP Z hCP hGP hQP0 hCN hGN hoto hotv hle hlex hH
  refine ⟨expStep_vrleSD S hlen h1 hx2 n hn ρP Z hCP hGP hQP0.1 hCN hGN hoto hotv hle hlex hH, ?_⟩
  have hQP := hQP0.2
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  have hSA := sameAt_lt hlen hL hA hd0e hn hpath hx2
    (hxnb_t1 hlen hL hA hd0e S.z2 S.z1c h1 n hn)
    (hiu_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn) (hiux_t1 hlen hL hA hd0e hpath hx2 (S.z2 r) hn)
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
    · -- the frame of `x`: `v_N(x) = v_P(r) ≤ v(r) ≤ v(q)`, no components at the level `v(q)`
      intro g hg
      exfalso
      have h0 : par M 0 c = some i := (mem_children_iff.mp hcch).2
      have hvx : σ.v c = ρP.v r := by
        rw [hcxe, hσ, glueZ_v_ge ρ (shiftV ρP L) Z (le_refl _)]
        show ρP.v (r + L - L) = ρP.v r; rw [Nat.add_sub_cancel]
      have hle' : ρP.v r ≤ ρ.v i :=
        le_trans hQP0.1 (v_par1_le_par0 hC V.g hRM hcM h0 (by rw [hcxe]; exact h1))
      have hot : isOT (ρP.v r) = true := hGP.ot_v r (by rw [hlP]; have := Nat.mul_pos (show 0 < n - 1 by omega) hL; omega)
      rw [hvx, comps_nil_of_le hot hle'] at hg
      simp at hg
    · have hcx : c < r + L := by omega
      by_cases hcv : DepX M (r + L) false c
      · exact vsf_frameSD S hC hRM V hlen hL hd0e h1 hx2 hn hH hCN hGN h hCL hcv hcx hPR
      · rw [hσ, glueZ_v_lt ρ (shiftV ρP L) Z hcx hcv]
        exact V.vs i (by omega) Lc c R hCL
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
      apply counted_iff_of_cnt1 (cnt_copy hlen hL hA hd0e hn hpath (S.z2 r) (ρ := ρ) (Z := Z) ha hd)
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
    rw [hσv, hLo, hvc]
    exact hQP (r + a) (by rw [hlP]; omega) Lc' c' R' hsplit
end


section
variable {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (hC : Cons M ρ) (hG : Good3 M ρ)
  (hR : Rk M rk) {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
  (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
include S hC hG hR hlen hL hd0e h1 hx2
/-- **The frame map survives each `t = 1` copy.** -/
theorem expStep_frameMapT1D :
    ExpStepT1D (fun N σ => FrameMapT1 M ρ r L N σ ∧ VrDomQ M ρ r L N σ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hrx : r < r + L := par_lt M 1 _ r h1
  obtain ⟨q0, hq0⟩ := par0_of_anc hA (by omega)
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hvr : ¬ DepX M (r + L) false r := not_depX_v_r1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab h1 hx2
  intro n hn ρP Z hCP hGP hPP hCN hGN _ _ hle hlex _
  set σ := glueZ M (r + L) ρ (shiftV ρP L) Z with hσ
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
  have hσo : ∀ a, σ.o (r + L + a) = ρP.o (r + a) := by
    intro a; rw [hσ, glueZ_o_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.o (r + L + a - L) = ρP.o (r + a); congr 1; omega
  have hσv : ∀ a, σ.v (r + L + a) = ρP.v (r + a) := by
    intro a; rw [hσ, glueZ_v_ge ρ (shiftV ρP L) Z (by omega)]
    show ρP.v (r + L + a - L) = ρP.v (r + a); congr 1; omega
  have hσvr : σ.v r = ρ.v r := by rw [hσ, glueZ_v_lt ρ (shiftV ρP L) Z hrx hvr]
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
    have hσvk : σ.v k = ρ.v k := by rw [hσ, glueZ_v_lt ρ (shiftV ρP L) Z hk hvk]
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
      have hσvc : σ.v c = ρ.v c := by rw [hσ, glueZ_v_lt ρ (shiftV ρP L) Z hcx hcv]
      obtain ⟨y1, hy1⟩ := o_psi_sub hCN hcN
      rw [hsy, sf_ot (hGN.ot_v c hcN), hσvc] at hy1
      simp only [psi.injEq] at hy1
      obtain ⟨hs, -⟩ := hy1
      obtain ⟨yM, hyM⟩ := o_psi_sub hC hcM
      rw [sf_ot (hG.ot_v c hcM), ← hs] at hyM
      have hole : σ.o c ≤ ρ.o c := by
        by_cases hD : DepX M (r + L) true c
        · rw [hσ, glueZ_o_dep ρ (shiftV ρP L) Z hcx hD]; exact (hle c hcx hD).1
        · rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z hcx hD]
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
        rw [hσ, glueZ_o_lt ρ (shiftV ρP L) Z (by omega) hdD]
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
      apply counted_iff_of_cnt1 (cnt_copy hlen hL hA hd0e hn hpath (S.z2 r) (ρ := ρ) (Z := Z) ha hd)
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


section

/-- The two closure fields survive each copy without the false old fields. -/
theorem expStep_closure_inv3V2D {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V2 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    ExpStepT1D (fun N σ => PH3cG N σ ∧ FC3 N σ) M r L d0 ρ := by
  have hp := G.expStep_ph3c_t1SD S I.cons I.good I.rank I.ph hlen hL hd0e h1 hx2
  have hf := G.expStep_fc3_t1SD S I.cons I.good I.rank I.fc3 hlen hL hd0e h1 hx2
  intro n hn ρP Z hCP hGP hPP hCN hGN ho hv hle hlex hH
  exact ⟨hp n hn ρP Z hCP hGP hPP.1 hCN hGN ho hv hle hlex hH,
    hf n hn ρP Z hCP hGP hPP.2 hCN hGN ho hv hle hlex hH⟩
end


section

/-- Ten fields of Inv3V2 survive each t = 1 copy, using only the chain's
usual step premises. No old global absorption or trigger is assumed. -/
theorem expStep_core_inv3V2D {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V2 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    ExpStepT1D CopyCoreV2 M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hfc := expStep_frameClosed_t1SD S I.cons I.good I.rank I.fc hlen hL hd0e h1 hx2
  have hfo := expStep_frameOT_t1D hlen hL hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab h1 hx2 hq I.fo
  have hbd := expStep_bumpDec_t1D hlen hL hd0e S.r0p S.z2 S.sibDec S.z1c S.uat S.uab h1 hx2 hq
    I.good ⟨I.kd, I.td⟩
  have hrp := expStep_rootP_t1D hlen hL hd0e S.z2 S.uat S.r12 S.bumpE2 S.r01 S.e00 h1 hx2 I.rootP
  have hcl := expStep_closure_inv3V2D S I hlen hL hd0e h1 hx2
  intro n hn ρP Z hCP hGP hPP hCN hGN ho hv hle hlex hH
  have hfcN := hfc n hn ρP Z hCP hGP hPP.fc hCN hGN ho hv hle hlex hH
  have hfoN := hfo n hn ρP Z hCP hGP hPP.fo hCN hGN ho hv hle hlex hH
  obtain ⟨hkdN, htdN⟩ := hbd n hn ρP Z hCP hGP ⟨hPP.kd, hPP.td⟩ hCN hGN ho hv hle hlex hH
  have hrpN := hrp n hn ρP Z hCP hGP hPP.rootP hCN hGN ho hv hle hlex hH
  obtain ⟨hphN, hfc3N⟩ := hcl n hn ρP Z hCP hGP ⟨hPP.ph, hPP.fc3⟩ hCN hGN ho hv hle hlex hH
  exact ⟨hCN, hGN, hfcN, hfoN, hkdN, htdN, hphN, hfc3N, rootS_of_good hCN hGN, hrpN⟩
end


section

/-- VSmallF with only the passing-root ordering residual, rather than a
component bound at every new valuation and every chain index. -/
theorem expStep_vsmallF_pass_inv3V2D {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V2 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hPR : PassRootRes M r L ρ) :
    ExpStepT1D (fun N σ => VrLe r ρ N σ ∧ VSmallF N σ) M r L d0 ρ :=
  expStep_vsmallF2SD S I.cons I.rank I.valInv hlen hL hd0e h1 hx2 hPR
end


section

/-- The eleven proved value fields, together with the bound on v(r) used
when the next copy is attached. PassRootRes itself is still a premise. -/
theorem expStep_core_vsmallF_pass_inv3V2D {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (S : SInv M) (I : Inv3V2 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0)
    (hPR : PassRootRes M r L ρ) :
    ExpStepT1D (fun N σ => CopyCoreV2 N σ ∧ VrLe r ρ N σ ∧ VSmallF N σ) M r L d0 ρ :=
  expStepD_and (expStep_core_inv3V2D S I hlen hL hd0e h1 hx2)
    (expStep_vsmallF_pass_inv3V2D S I hlen hL hd0e h1 hx2 hPR)
end


end Ytosk
