/-
**PH3cG・FC3 を t = 2 の M[n] へ（closure、2026-10-11）。**

t = 2 の一般形 `clField_expand_t2`（V3ExpT2FO）に差し込む。枠の性質は FrameOT の枠の性質 `QFO` と組にした
`QT2P`・`QT2F`（σ の補題で状態が標準形であることを使うため）。必要なのは
- σ で保たれる（`qT2P_sh`・`qT2F_sh`、V3PSh の `ph3cKindG_sh`・`fc3c_sh`）、
- 最後の子を ◁ で下げても保たれる（`qT2P_low`・`qT2F_low`）。ψ_{s′}(y′) ◁ ψ_s(y) で s′ < s なら、
  ◁ の定義に C = Ω_{s′+1} を入れて y′ = 0（`lhd_sub_drop`）なので書き換えない。添字が同じなら挟み込み。
残りは `clField_expand_t2` の仮定（T2BelowXRes、M.take x の枠、種の列の枠 T2SeedFrames）。
-/
import Ytosk.V3ExpT2FO
import Ytosk.V3PT1G
import Ytosk.V3PSh
import Ytosk.V3PShG
import Ytosk.V3PKindG
import Ytosk.V3InvW

namespace Ytosk.G

open T

/-! ## ◁ で添字が下がると引数は 0 -/

theorem psi_le_psi_any_t2 {s a x c : T} (h : s ≤ a) : psi s z z ≤ psi a x c :=
  le_trans (psi_le_psi_z (y := x) h) (by
    rcases (le_iff _ _).mp (z_le c) with h' | h'
    · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h'⟩))
    · rw [h'])

theorem comps_of_lev_lt {u : T} : ∀ {t : T}, (∀ q ∈ summands t, lev q < u) → comps u t = []
  | z, _ => rfl
  | psi v x c, h => by
    have hv : lt v u = true := h (psi v x z) (by simp [summands])
    simp only [comps, hv, if_true, List.nil_append]
    exact comps_of_lev_lt (fun q hq => h q (by simp [summands, hq]))

theorem comps_succ_self {s : T} (hs : isOT s = true) : ∀ e ∈ comps s (succ s), e = z := by
  intro e he
  unfold succ at he
  rw [comps_app, comps_of_lev_lt (fun q hq => lev_lt_of_summand hs hq), List.nil_append] at he
  by_cases h : lt z s = true
  · simp [one, comps, h] at he
  · simp [one, comps, h] at he; exact he

theorem lt_self_false (s : T) : lt s s = false := by
  cases h : lt s s
  · rfl
  · exact absurd h (lt_irrefl' s)

/-- **A `◁`-drop that lowers the subscript has argument `0`.** -/
theorem lhd_sub_drop {s y c s' y' c' : T} (hl : Lhd z (psi s' y' c') (psi s y c)) (hss : s' < s)
    (hs' : isOT s' = true) : y' = z := by
  have hc1 : psi s' y' c' < psi (succ s') z z := by
    rw [T.psi_lt_psi]; exact Or.inl (lt_succ_self s')
  have hc2 : psi (succ s') z z ≤ psi s y c := psi_le_psi_any_t2 (succ_le_of_lt hss)
  have hD := hl.2 s' (psi (succ s') z z) hc1 hc2
  have hy' : y' ∈ comps s' (psi s' y' c') := by
    simp [comps, lt_self_false s']
  obtain ⟨e, he, hye⟩ := hD y' hy'
  have hlt2 : lt (succ s') s' = false := by
    cases h : lt (succ s') s'
    · rfl
    · exact absurd (lt_trans (lt_succ_self s') h) (lt_irrefl' _)
  have e1 : comps s' (psi (succ s') z z) = z :: comps s' (succ s') := by simp [comps, hlt2]
  have e2 : Gc s' z = [z] := by simp [Gc, comps]
  rw [e1, e2] at he
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
  have hez : e = z := by
    rcases he with (he | he) | he
    · exact he
    · exact comps_succ_self hs' e he
    · exact he
  rw [hez] at hye
  rcases (le_iff _ _).mp hye with h | h
  · exact absurd h (T.not_lt_z _)
  · exact h

/-! ## 枠の性質 -/

/-- `PH3cG` at a frame, read off the head summand of the child's value. -/
abbrev QPHs (a : T) (Lv : List T) (cv : T) : Prop :=
  ∀ s y c, cv = psi s y c → lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s y z) = true →
    spArg a z (sumN Lv) ≠ z →
    PH3cKindG (spArg a z (sumN Lv)) (split y (psi (succ s) z z)).1 (split y (psi (succ s) z z)).2 s

/-- `FC3` at a frame, read off the head summand. -/
abbrev QF3s (a : T) (Lv : List T) (cv : T) : Prop :=
  ∀ s y c, cv = psi s y c → lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s y z) = true →
    Lv = [] → (split y (psi (succ s) z z)).1 ≠ z → FC3c a s y

abbrev QT2P (a : T) (Lv : List T) (cv : T) : Prop := QFO a Lv cv ∧ QPHs a Lv cv
abbrev QT2F (a : T) (Lv : List T) (cv : T) : Prop := QFO a Lv cv ∧ QF3s a Lv cv

theorem clField_qT2P {N : Mat} {σ : Valn} (hC : Cons N σ) (hFO : FrameOT N σ) (hP : PH3cG N σ) :
    CLField QT2P N σ := by
  intro i hi Lc c R hCL
  refine ⟨hFO i hi Lc c R hCL, fun s y c' hc ht hB => ?_⟩
  have hcN : c < N.length := (mem_children (cl_mem_children (show c ∈ CL N i by rw [hCL]; simp))).2
  obtain ⟨y0, hy0⟩ := o_psi_sub hC hcN
  have hc0 : c' = z := by rw [hy0] at hc; exact (T.psi.inj hc).2.2.symm
  subst hc0
  exact hP i hi Lc c R hCL s y hc hB ht

theorem ph3c_of_clField {N : Mat} {σ : Valn} (h : CLField QT2P N σ) : PH3cG N σ := by
  intro i hi Lc c R hCL s y hc hB ht
  exact (h i hi Lc c R hCL).2 s y z hc ht hB

theorem clField_qT2F {N : Mat} {σ : Valn} (hC : Cons N σ) (hFO : FrameOT N σ) (hP : FC3 N σ) :
    CLField QT2F N σ := by
  intro i hi Lc c R hCL
  refine ⟨hFO i hi Lc c R hCL, fun s y c' hc ht hL hhi => ?_⟩
  have hcN : c < N.length := (mem_children (cl_mem_children (show c ∈ CL N i by rw [hCL]; simp))).2
  obtain ⟨y0, hy0⟩ := o_psi_sub hC hcN
  have hc0 : c' = z := by rw [hy0] at hc; exact (T.psi.inj hc).2.2.symm
  subst hc0
  have hLc : Lc = [] := List.map_eq_nil_iff.mp hL
  subst hLc
  exact (fc3_iff.mp hP) i hi [] c R hCL s y hc ht rfl hhi

theorem fc3_of_clField {N : Mat} {σ : Valn} (h : CLField QT2F N σ) : FC3 N σ :=
  fc3_iff.mpr (fun i hi Lc c R hCL s y hc ht hL hhi => (h i hi Lc c R hCL).2 s y z hc ht hL hhi)

/-- **Lowering the last child by `◁`** keeps the frame properties. -/
theorem qT2P_low (a : T) (Lv : List T) (cv cv' : T) (hQ : QT2P a Lv cv) (hl : Lhd z cv' cv)
    (hot : isOT cv' = true) : QT2P a Lv cv' := by
  refine ⟨hQ.1, fun s' y' c' hc' ht' hB' => ?_⟩
  subst hc'
  cases cv with
  | z => exact absurd hl.1 (T.not_lt_z _)
  | psi s y c =>
    have hle : psi s' y' c' < psi s y c := hl.1
    rw [T.psi_lt_psi] at hle
    rcases hle with hss | ⟨rfl, hyy⟩ | ⟨rfl, rfl, _⟩
    · exfalso
      have := lhd_sub_drop hl hss (isOT_sub hot)
      rw [this] at ht'; exact T.not_lt_z _ ht'.1
    · have hMt : lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s' y z) = true :=
        ⟨lt_trans (show _ < y' from ht'.1) hyy,
          lt_trans (show psi a z z < psi s' y' z from ht'.2) (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, hyy⟩))⟩
      exact ph3cKindG_squeeze (hQ.2 s' y c rfl hMt hB') ht'.1 (le_of_lt hyy)
    · exact hQ.2 s' y' c rfl ht' hB'

theorem qT2F_low (a : T) (Lv : List T) (cv cv' : T) (hQ : QT2F a Lv cv) (hl : Lhd z cv' cv)
    (hot : isOT cv' = true) : QT2F a Lv cv' := by
  refine ⟨hQ.1, fun s' y' c' hc' ht' hL hhi => ?_⟩
  subst hc'
  cases cv with
  | z => exact absurd hl.1 (T.not_lt_z _)
  | psi s y c =>
    have hle : psi s' y' c' < psi s y c := hl.1
    rw [T.psi_lt_psi] at hle
    rcases hle with hss | ⟨rfl, hyy⟩ | ⟨rfl, rfl, _⟩
    · exfalso
      have := lhd_sub_drop hl hss (isOT_sub hot)
      rw [this] at ht'; exact T.not_lt_z _ ht'.1
    · subst hL
      exact fc3_squeeze (fun hy hrw hhiM => hQ.2 s' y c rfl ⟨lt_z_of_ne hy, hrw⟩ rfl hhiM) (le_of_lt hyy)
        ht'.2 hhi
    · exact hQ.2 s' y' c rfl ht' hL hhi

/-! ## σ -/

section
variable {V V' a : T} {Lv : List T} {cv : T} (hV : isOT V = true) (hV' : isOT V' = true) (hVV : V < V')
  (ha : isOT a = true) (hVa : V ≤ a) (hs : ∀ t ∈ Lv ++ [cv], Single t)
  (hp : (Lv ++ [cv]).Pairwise (fun a b => b ≤ a)) (hlev : V < a ∨ ∀ t ∈ Lv ++ [cv], V < lev t)
include hV hV' hVV ha hVa hs hp hlev

/-- The state moves by `σ`. -/
theorem state_sh : spArg (shf V V' a) z (sumN (Lv.map (sh V V'))) = sh V V' (spArg a z (sumN Lv)) := by
  have hLs : ∀ t ∈ Lv, Single t := fun t ht => hs t (List.mem_append_left _ ht)
  have hLp : Lv.Pairwise (fun a b => b ≤ a) := (List.pairwise_append.mp hp).1
  obtain ⟨hSot, hSsum⟩ := sumN_dec Lv hLs hLp
  have hlev' : V < a ∨ ∀ q ∈ summands (sumN Lv), lev q ≠ V := by
    rcases hlev with h | h
    · exact Or.inl h
    · right; rw [hSsum]; intro q hq; exact ne_of_gt (h q (List.mem_append_left _ hq))
  rw [← sh_sumN hV hV' hVV (fun t ht => (hLs t ht).1)]
  have hsp := sh_spArg hV hV' hVV ha hVa (b := z) rfl hSot hlev'
  rw [sh_z] at hsp
  exact hsp

/-- The rewriting of the moved frame goes back (`V < s`), and fails for `s ≤ V`. -/
theorem rw_back {s y : T} (hcv : cv = psi s y z)
    (ht : lt (sh V V' (spArg a z (sumN Lv))) (sh V V' y) = true ∧
      lt (psi (shf V V' a) z z) (sh V V' cv) = true)
    (hB : isOT (spArg a z (sumN Lv)) = true) :
    V < s ∧ lt (spArg a z (sumN Lv)) y = true ∧ lt (psi a z z) (psi s y z) = true := by
  have hcvot : isOT (psi s y z) = true := by rw [← hcv]; exact (hs cv (by simp)).1
  subst hcv
  have hV'a : V' ≤ shf V V' a := le_shf hV hV' (le_of_lt hVV) ha hVa
  by_cases hVs : V < s
  · refine ⟨hVs, (sh_lt_iff hV hV' (le_of_lt hVV) hB (isOT_arg hcvot)).mp ht.1, ?_⟩
    rcases (le_iff _ _).mp hVa with hVa' | hVa'
    · have e1 : sh V V' (psi a z z) = psi (shf V V' a) z z := by rw [sh_psi_gt hVa', sh_z]
      have := ht.2; rw [← e1] at this
      exact (sh_lt_iff hV hV' (le_of_lt hVV) (isOT_om.mpr ha) hcvot).mp this
    · rw [← hVa']; exact psi_lt_psi_z_iff.mpr (Or.inl hVs)
  · exfalso
    have h2 := ht.2
    rw [sh_psi_le hVs, sh_z] at h2
    have hss : s < shf V V' a := lt_of_le_of_lt (le_of_not_gt hVs) (lt_of_lt_of_le hVV hV'a)
    rcases psi_lt_psi_z_iff.mp (show psi _ z z < psi s y z from h2) with h | ⟨h, _⟩
    · exact lt_irrefl' _ (lt_trans h hss)
    · rw [h] at hss; exact lt_irrefl' _ hss

theorem qT2P_sh (hQ : QT2P a Lv cv) : QT2P (shf V V' a) (Lv.map (sh V V')) (sh V V' cv) := by
  refine ⟨qFO_sh V V' a Lv cv hV hV' hVV ha hVa hs hp hlev hQ.1, ?_⟩
  obtain ⟨s, y, hcv⟩ := (hs cv (by simp)).2
  have hBot : isOT (spArg a z (sumN Lv)) = true := isOT_arg hQ.1
  intro s' y' c' hc' ht' hB'
  rw [state_sh hV hV' hVV ha hVa hs hp hlev] at ht' hB' ⊢
  have hcvot : isOT (psi s y z) = true := by rw [← hcv]; exact (hs cv (by simp)).1
  by_cases hVs : V < s
  · rw [hcv, sh_psi_gt hVs, sh_z] at hc'
    obtain ⟨rfl, rfl, rfl⟩ := T.psi.inj hc'
    have ht2 : lt (sh V V' (spArg a z (sumN Lv))) (sh V V' y) = true ∧
        lt (psi (shf V V' a) z z) (sh V V' cv) = true := by
      rw [hcv, sh_psi_gt hVs, sh_z]; exact ht'
    obtain ⟨_, h1, h2⟩ := rw_back hV hV' hVV ha hVa hs hp hlev hcv ht2 hBot
    have hBP : spArg a z (sumN Lv) ≠ z := fun e => hB' (by rw [e, sh_z])
    exact ph3cKindG_sh hV hV' hVV (isOT_sub hcvot) hVs hBot (isOT_arg hcvot) (hQ.2 s y z hcv ⟨h1, h2⟩ hBP)
  · exfalso
    rw [hcv, sh_psi_le hVs, sh_z] at hc'
    obtain ⟨rfl, rfl, rfl⟩ := T.psi.inj hc'
    have hV'a : V' ≤ shf V V' a := le_shf hV hV' (le_of_lt hVV) ha hVa
    have hss : s < shf V V' a := lt_of_le_of_lt (le_of_not_gt hVs) (lt_of_lt_of_le hVV hV'a)
    rcases psi_lt_psi_z_iff.mp (show psi _ z z < psi s y z from ht'.2) with h | ⟨h, _⟩
    · exact lt_irrefl' _ (lt_trans h hss)
    · rw [h] at hss; exact lt_irrefl' _ hss

theorem qT2F_sh (hQ : QT2F a Lv cv) : QT2F (shf V V' a) (Lv.map (sh V V')) (sh V V' cv) := by
  refine ⟨qFO_sh V V' a Lv cv hV hV' hVV ha hVa hs hp hlev hQ.1, ?_⟩
  obtain ⟨s, y, hcv⟩ := (hs cv (by simp)).2
  have hBot : isOT (spArg a z (sumN Lv)) = true := isOT_arg hQ.1
  intro s' y' c' hc' ht' hL' hhi'
  have hL : Lv = [] := List.map_eq_nil_iff.mp hL'
  rw [state_sh hV hV' hVV ha hVa hs hp hlev] at ht'
  have hcvot : isOT (psi s y z) = true := by rw [← hcv]; exact (hs cv (by simp)).1
  by_cases hVs : V < s
  · rw [hcv, sh_psi_gt hVs, sh_z] at hc'
    obtain ⟨rfl, rfl, rfl⟩ := T.psi.inj hc'
    have ht2 : lt (sh V V' (spArg a z (sumN Lv))) (sh V V' y) = true ∧
        lt (psi (shf V V' a) z z) (sh V V' cv) = true := by
      rw [hcv, sh_psi_gt hVs, sh_z]; exact ht'
    obtain ⟨_, h1, h2⟩ := rw_back hV hV' hVV ha hVa hs hp hlev hcv ht2 hBot
    exact fc3c_sh hV hV' hVV ha hVa (isOT_sub hcvot) hVs (isOT_arg hcvot)
      (fun hhi => hQ.2 s y z hcv ⟨h1, h2⟩ hL hhi) hhi'
  · exfalso
    rw [hcv, sh_psi_le hVs, sh_z] at hc'
    obtain ⟨rfl, rfl, rfl⟩ := T.psi.inj hc'
    have hV'a : V' ≤ shf V V' a := le_shf hV hV' (le_of_lt hVV) ha hVa
    have hss : s < shf V V' a := lt_of_le_of_lt (le_of_not_gt hVs) (lt_of_lt_of_le hVV hV'a)
    rcases psi_lt_psi_z_iff.mp (show psi _ z z < psi s y z from ht'.2) with h | ⟨h, _⟩
    · exact lt_irrefl' _ (lt_trans h hss)
    · rw [h] at hss; exact lt_irrefl' _ hss

end

/-! ## t = 2 の M[n] -/

/-- **PH3cG of every `M[n]`** (`t = 2`), from PH3cG・FrameOT of `M` and `M.take x`, the residual of the frames
below `x` (`T2BelowXRes`), and the seed frames. -/
theorem ph3c_expand_t2 (hB : T2BelowXRes) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk) (hP : PH3cG M ρ)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ →
      FrameOT (M.take (M.length - 1)) τ ∧ PH3cG (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames QT2P M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → PH3cG (expand M n) σ := by
  intro n hn σ hσ
  apply ph3c_of_clField
  exact clField_expand_t2 (fun V V' a Lv cv hV hV' hVV ha hVa hs hp hlev hQ =>
      qT2P_sh hV hV' hVV ha hVa hs hp hlev hQ)
    qT2P_low hB hM hS I R hz h2 (clField_qT2P I.cons I.fo hP)
    (fun τ hτ => clField_qT2P hτ (hT τ hτ).1 (hT τ hτ).2) hSeed n hn σ hσ

/-- **FC3 of every `M[n]`** (`t = 2`). -/
theorem fc3_expand_t2 (hB : T2BelowXRes) {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat}
    (hM : Std M) (hS : M ≠ SRO) (I : Inv3W M ρ rk) (R : Res3W M ρ rk) (hP : FC3 M ρ)
    (hz : col M (M.length - 1) ≠ (0, 0, 0)) (h2 : TRIO.srow M (M.length - 1) = 2)
    (hT : ∀ τ, Cons (M.take (M.length - 1)) τ →
      FrameOT (M.take (M.length - 1)) τ ∧ FC3 (M.take (M.length - 1)) τ)
    (hSeed : T2SeedFrames QT2F M) :
    ∀ n, 1 ≤ n → ∀ σ, Cons (expand M n) σ → FC3 (expand M n) σ := by
  intro n hn σ hσ
  apply fc3_of_clField
  exact clField_expand_t2 (fun V V' a Lv cv hV hV' hVV ha hVa hs hp hlev hQ =>
      qT2F_sh hV hV' hVV ha hVa hs hp hlev hQ)
    qT2F_low hB hM hS I R hz h2 (clField_qT2F I.cons I.fo hP)
    (fun τ hτ => clField_qT2F hτ (hT τ hτ).1 (hT τ hτ).2) hSeed n hn σ hσ

end Ytosk.G
