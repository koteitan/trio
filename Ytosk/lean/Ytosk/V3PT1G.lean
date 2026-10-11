/-
**PH3cG・FC3 は t = 1 の展開 N = M[n] に渡る（closure、2026-10-11）。**

`frameClosed_N_t1`・`frameClosedOmN_t1`（V3FrameClN・V3ExpT1）と同じ組み立てを、書き換える枠の性質 Q′ について
一般にした（`frameQR_N_t1`・`frameQROmN_t1`）。
- x より前の枠: 子の値は fsD で添字を保って下がる（挟み込み）か、もとの値が Ω_{t+1} の葉（残り）。
- 写しの枠: M[n − 1] の枠。
- 残り（もとの子が Ω_{t+1}、v(i) ≤ t）: x より前では起きない。x では q ≠ r なら書き換えない（F1）、q = r なら
  新しい引数は b + δ（b = 状態、b の項は Ω_{s+1} 以上、0 < δ < Ω_{s+1}）。PH3cG ではこれは種類 eq、FC3 では
  b = 0 なので hi = 0 で空。実測（deepA の t = 1、n = 2, 3）で x の枠は 284/284 が eq。
-/
import Ytosk.V3ExpT1
import Ytosk.V3PT0G
import Ytosk.V3PKindG

namespace Ytosk.G

open T

set_option linter.unusedSectionVars false

/-- A frame property of rewriting frames. -/
abbrev QR (Q' : T → List T → T → T → Prop) (a : T) (Lv : List T) (cv : T) : Prop :=
  ∀ s y, cv = psi s y z → lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s y z) = true →
    Q' a Lv s y

/-- The rewriting-frame property of `PH3cG`. -/
abbrev PH' (a : T) (Lv : List T) (s y : T) : Prop :=
  spArg a z (sumN Lv) ≠ z →
    PH3cKindG (spArg a z (sumN Lv)) (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 s

/-- The rewriting-frame property of `FC3`. -/
abbrev F3' (a : T) (Lv : List T) (s y : T) : Prop :=
  Lv = [] → (split y (psi (succ s) z z)).1 ≠ z → FC3c a s y

theorem ph'_drop {a : T} {Lv : List T} {s y y' : T} (hyy : y' ≤ y)
    (ht : lt (spArg a z (sumN Lv)) y' = true ∧ lt (psi a z z) (psi s y' z) = true)
    (h : PH' a Lv s y) : PH' a Lv s y' :=
  fun hB => ph3cKindG_squeeze (h hB) ht.1 hyy

theorem f3'_drop {a : T} {Lv : List T} {s y y' : T} (hyy : y' ≤ y)
    (ht : lt (spArg a z (sumN Lv)) y' = true ∧ lt (psi a z z) (psi s y' z) = true)
    (h : F3' a Lv s y) : F3' a Lv s y' := by
  intro hL hhi
  subst hL
  have hpp : psi s y' z ≤ psi s y z := by
    rcases (le_iff _ _).mp hyy with h' | h'
    · exact le_of_lt (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, h'⟩))
    · rw [h']
  exact fc3_squeeze (fun _ _ hhiM => h rfl hhiM) hyy ht.2 hhi

/-- At a frame whose new argument extends the state `b` by `0 < δ < Ω_{s+1}`. -/
theorem ph'_app {a : T} {Lv : List T} {s b δ : T} (hb : spArg a z (sumN Lv) = b)
    (hge : AllGeT (psi (succ s) z z) b) (hδz : δ ≠ z) (hδ : δ < psi (succ s) z z) : PH' a Lv s (app b δ) := by
  intro _
  have hsplit : split (app b δ) (psi (succ s) z z) = (b, δ) :=
    split_app_of hge (Or.inr (lt_of_le_of_lt (head_le_self δ) hδ))
  rw [hb, hsplit]
  exact Or.inl ⟨rfl, hδz⟩

theorem f3'_app {a : T} {Lv : List T} {s b δ : T} (hb : spArg a z (sumN Lv) = b)
    (hge : AllGeT (psi (succ s) z z) b) (_hδz : δ ≠ z) (hδ : δ < psi (succ s) z z) : F3' a Lv s (app b δ) := by
  intro hL hhi
  subst hL
  have hb0 : b = z := by rw [← hb]; rfl
  subst hb0
  have hsplit : split (app z δ) (psi (succ s) z z) = (z, δ) :=
    split_app_of hge (Or.inr (lt_of_le_of_lt (head_le_self δ) hδ))
  rw [hsplit] at hhi
  exact absurd rfl hhi

section
variable {M : Mat} {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
  (hA : Anc0 M r (r + L)) (hd0e : entry M 0 (r + L) = entry M 0 r + d0) (hn : 2 ≤ n)
include hlen hL hA hd0e hn

/-- **A rewriting-frame property that survives drops of the argument passes to the glued valuation of
`M[n]`** (`t = 1`), given the residual at the frames whose child was a leaf `Ω_{t+1}` in `M`. -/
theorem frameQR_N_t1 (Q' : T → List T → T → T → Prop)
    (hQd : ∀ a Lv s y y', y' ≤ y →
      lt (spArg a z (sumN Lv)) y' = true ∧ lt (psi a z z) (psi s y' z) = true → Q' a Lv s y → Q' a Lv s y')
    (hpath : ∀ s, Anc0 M r s → Anc0 M s (r + L) → s ≠ r → s ≠ r + L →
      entry M 1 r < entry M 1 s) (hx2 : entry M 2 (r + L) = 0)
    (hxnb : ∀ c, par M 0 (r + L) = some c →
      col (TRIO.gexp M r L d0 0 n) (r + L) ≠ bump (TRIO.gexp M r L d0 0 n) c)
    (hz2 : entry M 2 r ≤ 1)
    (hiu : ∀ c, c < r + L → isUpg (TRIO.gexp M r L d0 0 n) c = isUpg M c)
    (hiux : isUpg (TRIO.gexp M r L d0 0 n) (r + L) = false)
    {ρ ρP : Valn} {Z : Nat → T} (hCP : Cons (TRIO.gexp M r L d0 0 (n - 1)) ρP)
    (hOS : ∀ i, i < r + L → DepX M (r + L) true i → OShape M (r + L) i)
    (hC : Cons M ρ)
    (hFQ : ∀ i, i < M.length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R →
      QR Q' (ρ.v i) (Lc.map ρ.o) (ρ.o c))
    (hOmQ : ∀ i, i < r + L → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → ∀ t,
      ρ.o c = psi (succ t) z z → ¬ lt t (ρ.v i) = true →
      QR Q' (ρ.v i) (Lc.map ρ.o) ((glueZ M (r + L) ρ (shiftV ρP L) Z).o c))
    (hFQP : ∀ i, i < (TRIO.gexp M r L d0 0 (n - 1)).length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat),
      CL (TRIO.gexp M r L d0 0 (n - 1)) i = Lc ++ c :: R → QR Q' (ρP.v i) (Lc.map ρP.o) (ρP.o c))
    (hle : ∀ c, c < r + L → DepX M (r + L) true c → fsD (ρ.o c) (Z c) ≤ ρ.o c)
    (hlex : ρP.o r ≤ ρ.o (r + L)) (hox : ∃ t, ρ.o (r + L) = psi (succ t) z z) :
    ∀ i, i < (TRIO.gexp M r L d0 0 n).length → ∀ (Lc : List Nat) (c : Nat) (R : List Nat),
      CL (TRIO.gexp M r L d0 0 n) i = Lc ++ c :: R →
      QR Q' ((glueZ M (r + L) ρ (shiftV ρP L) Z).v i) (Lc.map (glueZ M (r + L) ρ (shiftV ρP L) Z).o)
        ((glueZ M (r + L) ρ (shiftV ρP L) Z).o c) := by
  have hlN := len_N (d0 := d0) hlen hn
  have hlP := len_P (d0 := d0) (n := n) hlen
  intro i hi Lc c R hCL s y hc ht
  rcases Nat.lt_or_ge i (r + L) with h | h
  · obtain ⟨hCLM, hv, hLo⟩ := frameHead_lt hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux hCP hOS h hCL
    rw [hv, hLo] at ht ⊢
    have hcCL : c ∈ CL M i := by rw [hCLM]; simp
    have hcM := mem_children (List.mem_filter.mp hcCL).1
    have hiM : i < M.length := by omega
    obtain ⟨s0, y0, h0⟩ := o_psi_form hC hcM.2
    have hc0 := hc
    by_cases hcx : c = r + L
    · rw [hcx] at hc hCLM hc0
      rw [glueZ_o_ge ρ (shiftV ρP L) Z (le_refl _)] at hc
      have hc' : ρP.o r = psi s y z := by
        have : (shiftV ρP L).o (r + L) = ρP.o r := by show ρP.o (r + L - L) = _; rw [Nat.add_sub_cancel]
        rw [← this]; exact hc
      obtain ⟨t, hto⟩ := hox
      have hnt := trig_back_succ (by rw [← hto]; exact hlex) hc' ht
      exact hOmQ i h Lc (r + L) R hCLM t hto hnt s y hc0 ht
    · have hcx' : c < r + L := by omega
      by_cases hd : DepX M (r + L) true c
      · rw [glueZ_o_dep ρ (shiftV ρP L) Z hcx' hd, h0] at hc
        have hl := hle c hcx' hd
        rw [h0] at hl
        rcases trig_back_fsD hl hc ht with htM | ⟨t, hst, hy0, hnt⟩
        · have hy0z : y0 ≠ z := ne_z_of_lt htM.1
          have hss : s = s0 := fsD_psi_shape hy0z hc
          subst hss
          have hle' : psi s y z ≤ psi s y0 z := by rw [← hc]; exact hl
          have hyy : y ≤ y0 := by
            rcases (le_iff _ _).mp hle' with h' | h'
            · rcases psi_lt_psi_z_iff.mp h' with h' | ⟨_, h'⟩
              · exact absurd h' (lt_irrefl' _)
              · exact le_of_lt h'
            · simp only [psi.injEq] at h'; rw [h'.2.1]
          exact hQd _ _ _ _ _ hyy ht (hFQ i hiM Lc c R hCLM s y0 h0 htM)
        · exact hOmQ i h Lc c R hCLM t (by rw [h0, hst, hy0]) hnt s y hc0 ht
      · rw [glueZ_o_lt ρ (shiftV ρP L) Z hcx' hd] at hc
        exact hFQ i hiM Lc c R hCLM s y hc ht
  · obtain ⟨a, rfl⟩ : ∃ a, i = r + L + a := ⟨i - (r + L), by omega⟩
    have ha : a < (n - 1) * L := by omega
    obtain ⟨Lc', c', R', hsp, hv, hLo, hco⟩ :=
      frameHead_copy hlen hL hA hd0e hn hpath hx2 hxnb hz2 hiu hiux hCP hOS ha hCL
    rw [hv, hLo] at ht ⊢
    rw [hco] at hc
    exact hFQP (r + a) (by rw [hlP]; omega) Lc' c' R' hsp s y hc ht

end

/-- **The residual of the glued valuation** (`t = 1`), for a property that holds when the new argument
extends the state by `0 < δ < Ω_{s+1}` (as in `frameClosedOmN_t1`). -/
theorem frameQROmN_t1 (Q' : T → List T → T → T → Prop)
    (hQapp : ∀ a Lv s b δ, spArg a z (sumN Lv) = b → AllGeT (psi (succ s) z z) b → δ ≠ z →
      δ < psi (succ s) z z → Q' a Lv s (app b δ))
    {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk)
    {r L d0 n : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) (hn : 2 ≤ n)
    {ρP : Valn} {Z : Nat → T}
    (hGN : Good3 (TRIO.gexp M r L d0 0 n) (glueZ M (r + L) ρ (shiftV ρP L) Z))
    (hlex : ρP.o r ≤ ρ.o (r + L) ∧ ρP.o r ≠ z)
    (hH : ∃ μ br vr seed k0, HoleData M (r + L) ρ μ br vr seed ∧
      (∀ i, ∃ k, k0 ≤ k ∧ Z i = gamS μ br seed k) ∧ ρP.o r = gamS μ br seed k0 ∧ k0 = n - 2 ∧
      μ = vr ∧ ρ.o r = psi vr br z) :
    ∀ i, i < r + L → ∀ (Lc : List Nat) (c : Nat) (R : List Nat), CL M i = Lc ++ c :: R → ∀ t,
      ρ.o c = psi (succ t) z z → ¬ lt t (ρ.v i) = true →
      QR Q' (ρ.v i) (Lc.map ρ.o) ((glueZ M (r + L) ρ (shiftV ρP L) Z).o c) := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hOS := hOS_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq
  have hox := o_last_t1 hlen I.cons I.good h1 (by have := par1_entry_lt h1; omega) hx2
  obtain ⟨μ', br', vr', seed, k0, hHD, _, hPr, hk0n, hμv, hro'⟩ := hH
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
        have hoc := o_nocnt I.cons I.good hcM hnc
        rw [hct] at hoc
        have hs : succ t = ρ.v c := (T.psi.inj hoc).1
        have := holeT_not_succ hHv
        rw [← hs, isSucc_succ] at this; cases this
      · have hc'M := (mem_children (by rw [hch']; exact List.mem_append_right _ List.mem_cons_self :
          c' ∈ children M c)).2
        have hfr := o_frame I.cons I.good hcM hch' hcb' hcu' hR' hc'M
        obtain ⟨s3, y3, hc3⟩ := o_psi_form I.cons hc'M
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
    obtain ⟨b, hro, hbe, hb⟩ := qr_o_r hlen I.r0p I.sd h1 hx2 hq I.cons I.good I.rank
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
      have hcv := cvals_eq_map I.cons I.good i
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
      rw [← hro]; exact I.good.ot_o i (by omega)
    have hSr := hHD.S (ρ.v i) (lt_irrefl' _) hot
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
    have hdi : DepX M (r + L) true i := dep_anc_x I.uat I.z2 I.r12 I.be hlen hx2 (anc0_of_par M 0 i _ hix)
    have hvi : ¬ DepX M (r + L) false i := by
      rcases hOS i hi hdi with ⟨_, hnc⟩ | ⟨hv', _⟩
      · rcases hnc _ hcm with h' | h'
        · exact absurd h' hcnt.1
        · exact absurd h' hcnt.2
      · exact hv'
    have hF := hF1_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab h1 I.cons I.good I.rank i hri hi hdi hvi
    exact lt_irrefl' _ (lt_of_lt_of_le hF (le_trans his hsr))

/-- **PH3cG is carried** (`t = 1`). -/
theorem expStep_ph3c_t1 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk) (hP : PH3cG M ρ)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    ExpStepT1 (fun N σ => PH3cG N σ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hox : ∃ t, ρ.o (r + L) = psi (succ t) z z :=
    ⟨_, o_last_t1 hlen I.cons I.good h1 (by have := par1_entry_lt h1; omega) hx2⟩
  intro n hn ρP Z hCP _ hPP _ hGN _ _ hle hlex hH
  have hxnb := hxnb_t1 hlen hL hA hd0e I.z2 I.z1 h1 n hn
  have hiu := hiu_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn
  have hiux := hiux_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn
  have hOS := hOS_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq
  exact ph3c_iff.mpr (frameQR_N_t1 hlen hL hA hd0e hn PH' (fun _ _ _ _ _ hyy ht h => ph'_drop hyy ht h)
    hpath hx2 hxnb (I.z2 r) hiu hiux hCP hOS I.cons (ph3c_iff.mp hP)
    (frameQROmN_t1 PH' (fun _ _ _ _ _ hb hge hδz hδ => ph'_app hb hge hδz hδ) I hlen hL hd0e h1 hx2 hn hGN
      hlex hH)
    (ph3c_iff.mp hPP) (fun c hc hd => (hle c hc hd).1) hlex.1 hox)

/-- **FC3 is carried** (`t = 1`). -/
theorem expStep_fc3_t1 {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} (I : Inv3 M ρ rk) (hP : FC3 M ρ)
    {r L d0 : Nat} (hlen : r + L + 1 = M.length) (hL : 0 < L)
    (hd0e : entry M 0 (r + L) = entry M 0 r + d0)
    (h1 : par M 1 (r + L) = some r) (hx2 : entry M 2 (r + L) = 0) :
    ExpStepT1 (fun N σ => FC3 N σ) M r L d0 ρ := by
  have hA : Anc0 M r (r + L) := anc0_of_par M 1 r (r + L) h1
  have hpath := hpath_of_par1 h1 hA (by omega)
  obtain ⟨q, hq⟩ := par0_of_anc hA (by omega)
  have hox : ∃ t, ρ.o (r + L) = psi (succ t) z z :=
    ⟨_, o_last_t1 hlen I.cons I.good h1 (by have := par1_entry_lt h1; omega) hx2⟩
  intro n hn ρP Z hCP _ hPP _ hGN _ _ hle hlex hH
  have hxnb := hxnb_t1 hlen hL hA hd0e I.z2 I.z1 h1 n hn
  have hiu := hiu_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn
  have hiux := hiux_t1 hlen hL hA hd0e hpath hx2 (I.z2 r) hn
  have hOS := hOS_t1 hlen I.r0p I.z2 I.sd I.z1 I.uat I.uab hx2 hq
  exact fc3_iff.mpr (frameQR_N_t1 hlen hL hA hd0e hn F3' (fun _ _ _ _ _ hyy ht h => f3'_drop hyy ht h)
    hpath hx2 hxnb (I.z2 r) hiu hiux hCP hOS I.cons (fc3_iff.mp hP)
    (frameQROmN_t1 F3' (fun _ _ _ _ _ hb hge hδz hδ => f3'_app hb hge hδz hδ) I hlen hL hd0e h1 hx2 hn hGN
      hlex hH)
    (fc3_iff.mp hPP) (fun c hc hd => (hle c hc hd).1) hlex.1 hox)

end Ytosk.G
