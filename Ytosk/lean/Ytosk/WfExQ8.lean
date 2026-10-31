/-
**WfExQ8 (2026-11-01): the leaf residuals `OmQRes` / `FCOmRes` (WfExQ4/5) in the q = r frame.**

Copy of `G.frameQROmN_t1S` / `frameClosedOmN_t1S` for `glueQ`, restricted to `q = r`:
- a leaf child `c < x` with `o(c) = Ω_{t+1}` and `v(i) ≤ t` cannot be in `D` (`qr_holeD`: every `D` value below `x`
  is a hole, so not a successor), and off `D` the value is `Ω_{t+1}` (no trigger);
- the leaf child `c = x` (in the frame `i = r`): the new value is `ρP.o r`, and `ρP.o r < o(r) = ψ_μ(b + Ω_{μ+1})`
  alone gives the form `ψ_μ(b + δ)`, `0 < δ < Ω_{μ+1}` (the old proof used the chain term `gamS`).
So the only value fact needed is `ρP.o r < ρ.o r` (`ExDQY`).
-/
import Ytosk.WfExQ7

namespace Ytosk.WfExQ8
open T Ytosk Ytosk.G Ytosk.WfExQ1 Ytosk.WfExQ2 Ytosk.WfExQ4 Ytosk.WfExQ5 Ytosk.WfQrL1 Ytosk.WfQrL7

set_option linter.unusedSectionVars false

/-- **The leaf frames of a rewriting-frame property at the new values** (`q = r`). -/
theorem omQ_qr (Q' : T → List T → T → T → Prop)
    (hQapp : ∀ a Lv s b δ, a = s → spArg a z (sumN Lv) = b → AllGeT (psi (succ s) z z) b → δ ≠ z →
      δ < psi (succ s) z z → isOT (psi s (app b δ) z) = true → Q' a Lv s (app b δ))
    {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (I : Inv3V3 M ρ rk)
    {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    (hn : 2 ≤ n) {ρP : Valn} {oq vq : Nat → T}
    (hGN : Good3 (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq))
    (hPlt : ρP.o r < ρ.o r) :
    ∀ i, i < r + L → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → ∀ t,
      ρ.o c = psi (succ t) z z → ¬ lt t (ρ.v i) = true →
      QR Q' (ρ.v i) (Lc.map ρ.o) ((glueQ M (r + L) ρ (shiftV ρP L) oq vq).o c) := by
  have hC := I.cons
  have hG := I.good
  have hOS := hOS_t1 hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 hq
  have hox := o_last_t1 hlen hC hG h1 (by have := par1_entry_lt h1; omega) hx2
  obtain ⟨b, hro, hbe, hb⟩ := qr_o_r hlen S.r0p S.sibDec h1 hx2 hq hC hG I.rank
  have hHole := qr_holeD hlen S.r0p S.z2 S.sibDec S.z1c S.uat S.uab hx2 h1 hq hC hG I.kd I.td hro hox hOS
  set σ := glueQ M (r + L) ρ (shiftV ρP L) oq vq with hσ
  have hlN := len_N (d0 := d0) hlen hn
  have hσx : σ.o (r + L) = ρP.o r := by
    rw [hσ, glueQ_o_ge (Nat.le_refl _)]
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
      · have hHv := (hHole false c hvc hc').1
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
    · rw [hσ, glueQ_o_lt hc' hd, hct] at hc
      rw [← (T.psi.inj hc).2.1] at ht1
      exact T.not_lt_z _ ht1
  have hcx : c = r + L := by omega
  subst hcx
  have hix : par M 0 (r + L) = some i := (mem_children_iff.mp hcm).2
  have hir : i = r := Option.some.inj (hix.symm.trans hq)
  subst hir
  have hlex : ρP.o i ≤ ρ.o (i + L) := by
    rw [hox]; apply le_of_lt; apply lt_trans hPlt; rw [hro]
    rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self _)
  have hsy : psi s y z ≤ psi (succ (ρ.v i)) z z := by rw [← hc, hσx, ← hox]; exact hlex
  have hyz : y ≠ z := by intro h'; rw [h'] at ht1; exact T.not_lt_z _ ht1
  have hsr : s ≤ ρ.v i := by
    rcases (le_iff _ _).mp hsy with h' | h'
    · rcases psi_lt_psi_z_iff.mp h' with h'' | ⟨_, h''⟩
      · exact lt_succ_iff.mp h''
      · exact absurd h'' (T.not_lt_z _)
    · exact absurd (T.psi.inj h').2.1 hyz
  have his : ρ.v i ≤ s := by
    rcases psi_lt_psi_z_iff.mp ht2 with h' | ⟨h', _⟩
    · exact le_of_lt h'
    · rw [h']
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
  have hotN : isOT (psi (ρ.v i) y z) = true := by
    rw [← hc]; exact hGN.ot_o (i + L) (by rw [hlN]; have := Nat.mul_pos (show 0 < n - 1 by omega) hL; omega)
  -- `y < b + Ω_{μ+1}` from `ρP.o r < o(r)`
  rw [hσx] at hc
  have hy : y < app b (psi (succ (ρ.v i)) z z) := by
    have h' : psi (ρ.v i) y z < psi (ρ.v i) (app b (psi (succ (ρ.v i)) z z)) z := by
      rw [← hc, ← hro]; exact hPlt
    rcases psi_lt_psi_z_iff.mp h' with h'' | ⟨_, h''⟩
    · exact absurd h'' (lt_irrefl' _)
    · exact h''
  obtain ⟨c0, hc0, hc0z, hc0le⟩ := between_app (A := b) (x := z) (y := psi (succ (ρ.v i)) z z) (c := y)
    (by rw [app_z_right]; exact ht1) (le_of_lt hy)
  have hc0z' : c0 ≠ z := by intro h'; rw [h'] at hc0z; exact T.not_lt_z _ hc0z
  have hc0lt : c0 < psi (succ (ρ.v i)) z z := by
    rcases (le_iff _ _).mp hc0le with h' | h'
    · exact h'
    · exfalso; rw [hc0, h'] at hy; exact lt_irrefl' _ hy
  rw [hc0] at hotN ⊢
  exact hQapp _ _ _ _ _ rfl hBb hb hc0z' hc0lt hotN

/-- The extra facts with the chain value below `o(r)`. -/
def ExDQY (M : Mat) (r L : Nat) (ρ : Valn) (n : Nat) (ρP : Valn) (oq vq : Nat → T) : Prop :=
  ExDQX M r L ρ n ρP oq vq ∧ ρP.o r < ρ.o r

/-- **`OmQRes` for PH' / F3' in the q = r frame**, with `ExDQY`. -/
theorem omQRes_qr (Q' : T → List T → T → T → Prop)
    (hQapp : ∀ a Lv s b δ, a = s → spArg a z (sumN Lv) = b → AllGeT (psi (succ s) z z) b → δ ≠ z →
      δ < psi (succ s) z z → isOT (psi s (app b δ) z) = true → Q' a Lv s (app b δ))
    {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (I : Inv3V3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r) :
    ∀ n, 2 ≤ n → ∀ (ρP : Valn) (oq vq : Nat → T),
      Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP → Good3 (TRIO.gexp M r L d0 0 (n - 1)) ρP →
      Cons (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq) →
      Good3 (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq) →
      ExDQY M r L ρ n ρP oq vq →
      ∀ i, i < r + L → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → ∀ t,
        ρ.o c = psi (succ t) z z → ¬ lt t (ρ.v i) = true →
        QR Q' (ρ.v i) (Lc.map ρ.o) ((glueQ M (r + L) ρ (shiftV ρP L) oq vq).o c) :=
  fun n hn _ _ _ _ _ _ hGN hEx => omQ_qr Q' hQapp S I hlen hL h1 hx2 hq hn hGN hEx.2

/-- **`FCOmRes` in the q = r frame** (FrameDom of `b + δ`, `frameDom_app`). -/
theorem fcOm_qr {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (I : Inv3V3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r) :
    ∀ n, 2 ≤ n → ∀ (ρP : Valn) (oq vq : Nat → T),
      Good3 (TRIO.gexp M r L d0 0 n) (glueQ M (r + L) ρ (shiftV ρP L) oq vq) → ρP.o r < ρ.o r →
      FrameClosedOmN M r L ρ (glueQ M (r + L) ρ (shiftV ρP L) oq vq) := by
  intro _ hn ρP oq vq hGN hPlt i hi Lc c R hCL t hct htv s y hc ht
  exact omQ_qr (fun a Lv s y => FrameDom a (spArg a z (sumN Lv)) s (H s y))
    (fun a Lv s b δ has hB hAll hδz hδ hot => by
      subst has
      show FrameDom a (spArg a z (sumN Lv)) a (H a (app b δ))
      rw [hB]
      exact frameDom_app hAll hδz hδ hot (fun _ _ g hg => ⟨g, hg, le_refl _⟩))
    S I hlen hL h1 hx2 hq hn hGN hPlt i hi Lc c R hCL t hct htv s y hc ht

end Ytosk.WfExQ8

namespace Ytosk.WfExQ8
open T Ytosk Ytosk.G Ytosk.WfExQ1 Ytosk.WfExQ2 Ytosk.WfExQ4 Ytosk.WfExQ5 Ytosk.WfExQ6 Ytosk.WfQrL1 Ytosk.WfQrL7
  Ytosk.WfQrH6

/-- `ExDQY` from `hLocH`'s C_strip conjuncts, its premise `ρP.o r < o(x)`, and `ρP.o r < o(r)`. -/
theorem exDQY_of_loc {M : Mat} {r L : Nat} {ρ σ : Valn} (n : Nat) (ρP : Valn)
    (hlt : ρP.o r < ρ.o (r + L)) (hltr : ρP.o r < ρ.o r)
    (ho : ∀ c, c ≤ r + L → DepX M (r + L) true c → ∃ η tS, DQC η false (ρ.o c) (σ.o c) tS)
    (hv : ∀ i, i < r + L → DepX M (r + L) false i → ∃ η tS, DQC η true (ρ.v i) (σ.v i) tS) :
    ExDQY M r L ρ n ρP σ.o σ.v :=
  ⟨⟨exDQ_of_strip n ρP ho hv, le_of_lt hlt⟩, hltr⟩

/-- **`ExpStepQ` of `Inv3V3` in the q = r frame**: every field is proved except `VSmallF`, `VSmallRAll` (carried
component conditions) and the last-column frame fields of `M[n]` (`FrameAtN`). -/
theorem expStepQ_V3Y {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (S : SInv M) (I : Inv3V3 M ρ rk)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hq : par M 0 (r + L) = some r)
    (hVSF : ExpStepQR PnV3 (fun N σ => VSmallF N σ) (ExDQY M r L ρ) M r L d0 ρ)
    (hVRA : ExpStepQR PnV3 (fun N σ => VSmallRAll N σ) (ExDQY M r L ρ) M r L d0 ρ)
    (hFr : FrameAtN M r L d0) :
    ExpStepQ PnV3 (ExDQY M r L ρ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  have hox : ∃ t, ρ.o (r + L) = psi (succ t) z z :=
    ⟨_, o_last_t1 hlen I.cons I.good h1 (by have := par1_entry_lt h1; omega) hx2⟩
  intro n hn ρP oq vq hCP hGP hPP hCN hGN hEx
  have hEX := hEx.1
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
  have hvs := hVSF n hn ρP oq vq hCP hGP ⟨_, J⟩ hCN hGN hEx
  have hvra := hVRA n hn ρP oq vq hCP hGP ⟨_, J⟩ hCN hGN hEx
  obtain ⟨F, hTP, hTPW⟩ := hFr n hn _ rkN hCN hR hGN
  exact ⟨rkN, inv3V3_of_parts hCN hGN hR hS hP ⟨hvs, hfc, hfo, hkd, htd, hph, hf3, hvra⟩ F hTP hTPW⟩

end Ytosk.WfExQ8
