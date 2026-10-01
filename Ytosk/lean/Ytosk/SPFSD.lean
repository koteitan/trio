/-
**正規化 sp と fsD の交換。**

fsD は一番深い位置に作用するだけなので、X ≠ 0 が後続でなければ fsD(ψ_a(X), ζ) = ψ_a(fsD(X, ζ))（`fsD_psi`）。
したがって経路の 1 段の交換は、cof が Ω 型（通過・対角化）でも ω 型でも 1 本の補題
fsD(spArg(a, b, c), ζ) = spArg(a, b, fsD(c, ζ))（`frame_fsD`）になる。条件は 3 通り:
書き換えない、書き換えて低い部分が残る、書き換えて低い部分が 0（どれも M[n] でも同じ型のまま）。
-/
import Ytosk.FSD
import Ytosk.SPFS

namespace Ytosk

open T

/-- With a big cofinality, `fsD` is `fs`. -/
theorem fsD_eq_fs : ∀ {t μ : T}, cof t = .big μ → ∀ η, fsD t η = fs t η
  | z, _, h, _ => by simp [cof] at h
  | psi a b (psi c d e), μ, h, η => by
    have h' : cof (psi c d e) = .big μ := by simpa [cof] using h
    show psi a b (fsD (psi c d e) η) = psi a b (fs (psi c d e) η)
    rw [fsD_eq_fs h' η]
  | psi a b z, μ, h, η => by
    unfold cof at h
    conv => lhs; unfold fsD
    conv => rhs; unfold fs
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h ⊢; rw [if_pos rfl]
      by_cases ha : a = z
      · subst ha; simp at h
      · rw [if_neg ha] at h ⊢; rw [if_neg ha]
        by_cases hs : isSucc a = true
        · rw [if_pos hs]; rw [if_pos hs]
        · rw [if_neg hs] at h ⊢; rw [if_neg hs]
          rw [fsD_eq_fs h η]
    · rw [if_neg hb] at h ⊢; rw [if_neg hb]
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; cases h
      · rw [if_neg hs] at h ⊢; rw [if_neg hs]
        cases hcb : cof b with
        | big ν =>
          rw [hcb] at h; simp only at h ⊢
          by_cases hν : lt ν a = true
          · rw [if_pos hν]
          · rw [if_neg hν] at h; cases h
        | zero => rw [hcb] at h; cases h
        | succ => rw [hcb] at h; cases h
        | omega => rw [hcb] at h; cases h

/-- `fsD` of a sum acts on its last summand. -/
theorem fsD_app : ∀ (B : T) {c : T}, c ≠ z → ∀ η, fsD (app B c) η = app B (fsD c η)
  | z, _, _, _ => by simp
  | psi a b B', c, hc, η => by
    simp only [app_psi]
    cases hB : app B' c with
    | z => exact absurd (app_eq_z hB).2 hc
    | psi d e f =>
      show fsD (psi a b (psi d e f)) η = psi a b (app B' (fsD c η))
      rw [← fsD_app B' hc η, hB]
      rfl

/-- **`fsD` goes under `ψ_a`** when the argument is nonzero and not a successor. -/
theorem fsD_psi {a X : T} (hX : X ≠ z) (hs : isSucc X = false) (η : T) :
    fsD (psi a X z) η = psi a (fsD X η) z := by
  conv => lhs; unfold fsD
  rw [if_neg hX, if_neg (by rw [hs]; simp)]
  cases hc : cof X with
  | big μ => simp only; rw [fsD_eq_fs hc]
  | zero => rfl
  | succ => rfl
  | omega => rfl

theorem isSucc_app (B : T) {c : T} (hc : c ≠ z) : isSucc (app B c) = isSucc c := by
  unfold isSucc
  induction B with
  | z => simp
  | psi a b B' _ _ ih =>
    simp only [app_psi]
    cases hB : app B' c with
    | z => exact absurd (app_eq_z hB).2 hc
    | psi d e f => rw [← ih, hB]; rfl

theorem DV_app : ∀ (B : T) {c : T}, c ≠ z → ∀ η, DV (app B c) η ↔ DV c η
  | z, _, _, _ => by simp
  | psi a b B', c, hc, η => by
    simp only [app_psi]
    cases hB : app B' c with
    | z => exact absurd (app_eq_z hB).2 hc
    | psi d e f =>
      show DV (psi d e f) η ↔ DV c η
      rw [← hB]; exact DV_app B' hc η

/-- Below `Ω_{μ+1}`, every term of cofinality `Ω_{μ+1}` takes the index. -/
theorem DV_of_big : ∀ {t μ η : T}, isOT η = true → cof t = .big μ → η < psi (succ μ) z z → DV t η
  | z, _, _, _, h, _ => by simp [cof] at h
  | psi a b (psi c d e), μ, η, hη, h, hl => by
    have h' : cof (psi c d e) = .big μ := by simpa [cof] using h
    show DV (psi c d e) η
    exact DV_of_big hη h' hl
  | psi a b z, μ, η, hη, h, hl => by
    unfold cof at h
    unfold DV
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at h ⊢
      by_cases ha : a = z
      · subst ha; simp at h
      · rw [if_neg ha] at h
        refine ⟨ha, ?_⟩
        by_cases hs : isSucc a = true
        · rw [if_pos hs] at h ⊢; cases h
          have : succ (init a) = a := init_app_one hs
          rw [this] at hl; exact hl
        · rw [if_neg hs] at h ⊢; exact DV_of_big hη h hl
    · rw [if_neg hb] at h ⊢
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; cases h
      · rw [if_neg hs] at h ⊢
        cases hcb : cof b with
        | big ν =>
          rw [hcb] at h; simp only at h ⊢
          by_cases hν : lt ν a = true
          · rw [if_pos hν] at h; cases h
            refine ⟨hl, fun _ g hg => ?_⟩
            have hηa : η < psi a z z := by
              apply lt_of_lt_of_le hl
              rcases (le_iff _ _).mp (succ_le_of_lt (show μ < a from hν)) with h1 | h1
              · exact le_of_lt (by rw [psi_lt_psi_z_iff]; exact Or.inl h1)
              · rw [h1]
            rw [comps_nil_of_lt_Om hη hηa] at hg; simp at hg
          · rw [if_neg hν] at h; cases h
        | zero => rw [hcb] at h; cases h
        | succ => rw [hcb] at h; cases h
        | omega => rw [hcb] at h; cases h

/-- `DV` of `ψ_s(y)`, `y ≠ 0`, is `DV` of `y` (plus the component condition). -/
theorem DV_psi_arg {s y η : T} (hη : isOT η = true) (hy : y ≠ z) (h : DV (psi s y z) η) : isSucc y = false ∧ DV y η := by
  unfold DV at h
  rw [if_neg hy] at h
  by_cases hs : isSucc y = true
  · rw [if_pos hs] at h; exact absurd h id
  · rw [if_neg hs] at h
    refine ⟨by simpa using hs, ?_⟩
    cases hcy : cof y with
    | big μ =>
      rw [hcy] at h
      exact DV_of_big hη hcy h.1
    | zero => rw [hcy] at h; exact h.1
    | succ => rw [hcy] at h; exact h.1
    | omega => rw [hcy] at h; exact h.1

/-! ## 1 段の交換 -/

/-- **Commutation, non-rewriting case.** -/
theorem frame_fsD_notrig {a b s y ζ : T} (hc : isOT (psi s y z) = true) (hζ : isOT ζ = true)
    (hDV : DV (psi s y z) ζ) (hno : y ≤ b ∨ s < a) (hbc : isOT (app b (psi s y z)) = true)
    (hno' : ∀ s' y', psi s' y' z ∈ summands (fsD (psi s y z) ζ) → y' ≤ b ∨ s' < a) :
    fsD (spArg a b (psi s y z)) ζ = spArg a b (fsD (psi s y z) ζ) := by
  obtain ⟨hfot, hflt⟩ := fsD_ot_lt hc hζ hDV
  have hcz : psi s y z ≠ z := by simp
  have h1 : spArg a b (psi s y z) = app b (psi s y z) := by
    apply spArg_eq_app hbc
    intro s' y' hq
    simp only [summands, List.mem_cons, List.mem_nil_iff, or_false, psi.injEq] at hq
    obtain ⟨rfl, rfl, _⟩ := hq; exact hno
  have hbot : isOT b = true := isOT_app_left hbc
  have hbf : isOT (app b (fsD (psi s y z) ζ)) = true := by
    apply isOT_app_of hbot hfot
    intro q hq
    exact le_trans (head_le_of_lt hflt) (summand_ge_of_app hbc hq)
  rw [h1, fsD_app b hcz, spArg_eq_app hbf hno']

/-- **Commutation, rewriting case with a lower part.** -/
theorem frame_fsD_trig {a b s y ζ : T} (hc : isOT (psi s y z) = true) (hζ : isOT ζ = true)
    (hDV : DV (psi s y z) ζ)
    (htr : lt b y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hlo : (split y (psi (succ s) z z)).2 ≠ z)
    (hlo' : fsD (split y (psi (succ s) z z)).2 ζ ≠ z)
    (hbη : lt b (fsD y ζ) = true) :
    fsD (spArg a b (psi s y z)) ζ = spArg a b (fsD (psi s y z) ζ) := by
  have hy : y ≠ z := by rintro rfl; simp [lt] at htr
  obtain ⟨hys, hDVy⟩ := DV_psi_arg hζ hy hDV
  have hfc : fsD (psi s y z) ζ = psi s (fsD y ζ) z := fsD_psi hy hys ζ
  have hcη : isOT (psi s (fsD y ζ) z) = true := by rw [← hfc]; exact isOT_fsD hc hζ hDV
  have hbpl := split_app (psi (succ s) z z) y
  have hpge := split_fst_ge (psi (succ s) z z) y
  have hlo1 := split_snd_head (psi (succ s) z z) y
  generalize hP : (split y (psi (succ s) z z)) = pr at hbpl hpge hlo1 hlo hlo'
  obtain ⟨p, lo⟩ := pr
  simp only at hbpl hpge hlo1 hlo hlo'
  have hloh : head lo < psi (succ s) z z := by rcases hlo1 with h | h; exact absurd h hlo; exact h
  have hH : spArg a b (psi s y z) = app p (psi s y z) := by
    rw [spArg_cons]; show step a b s y z = _
    unfold step; rw [if_pos htr, H_eq hc, hP]; simp [hlo]
  have hcz : psi s y z ≠ z := by simp
  rw [hH, fsD_app p hcz, hfc]
  have hfy : fsD y ζ = app p (fsD lo ζ) := by rw [← hbpl]; exact fsD_app p hlo ζ
  have hDVlo : DV lo ζ := (DV_app p hlo ζ).mp (by rw [hbpl]; exact hDVy)
  have hlolt : fsD lo ζ < lo := fsD_lt hDVlo
  have hsp : split (fsD y ζ) (psi (succ s) z z) = (p, fsD lo ζ) := by
    rw [hfy]
    apply split_app_of hpge
    right; exact lt_of_le_of_lt (head_le_of_lt hlolt) hloh
  rw [spArg_cons]; show _ = step a b s (fsD y ζ) z
  unfold step
  have hy' : fsD y ζ ≠ z := by intro h; rw [h] at hbη; simp [lt] at hbη
  have htr' : lt b (fsD y ζ) = true ∧ lt (psi a z z) (psi s (fsD y ζ) z) = true :=
    ⟨hbη, by rw [← trig_cond hy hy']; exact htr.2⟩
  rw [if_pos htr', H_eq hcη, hsp]
  simp [hlo']

/-- **Commutation, rewriting case with no lower part** (on either side). -/
theorem frame_fsD_trig0 {a b s y ζ : T} (hc : isOT (psi s y z) = true) (hζ : isOT ζ = true)
    (hDV : DV (psi s y z) ζ)
    (htr : lt b y = true ∧ lt (psi a z z) (psi s y z) = true)
    (hlo : (split y (psi (succ s) z z)).2 = z)
    (hlo' : (split (fsD y ζ) (psi (succ s) z z)).2 = z)
    (hbη : lt b (fsD y ζ) = true) :
    fsD (spArg a b (psi s y z)) ζ = spArg a b (fsD (psi s y z) ζ) := by
  have hy : y ≠ z := by rintro rfl; simp [lt] at htr
  obtain ⟨hys, _⟩ := DV_psi_arg hζ hy hDV
  have hfc : fsD (psi s y z) ζ = psi s (fsD y ζ) z := fsD_psi hy hys ζ
  have hcη : isOT (psi s (fsD y ζ) z) = true := by rw [← hfc]; exact isOT_fsD hc hζ hDV
  have hH : spArg a b (psi s y z) = y := by
    rw [spArg_cons]; show step a b s y z = _
    unfold step; rw [if_pos htr, H_eq hc, if_pos hlo, app_z_right]
    have := split_app (psi (succ s) z z) y; rw [hlo, app_z_right] at this; exact this
  rw [hH, hfc]
  rw [spArg_cons]; show _ = step a b s (fsD y ζ) z
  unfold step
  have hy' : fsD y ζ ≠ z := by intro h; rw [h] at hbη; simp [lt] at hbη
  have htr' : lt b (fsD y ζ) = true ∧ lt (psi a z z) (psi s (fsD y ζ) z) = true :=
    ⟨hbη, by rw [← trig_cond hy hy']; exact htr.2⟩
  rw [if_pos htr', H_eq hcη, if_pos hlo', app_z_right]
  have := split_app (psi (succ s) z z) (fsD y ζ); rw [hlo', app_z_right] at this; exact this.symm

/-! ## 経路の文脈 -/

/-- The commutation at one frame, as a condition. -/
def FrameD (a b c ζ : T) : Prop :=
  spArg a b c ≠ z ∧ isSucc (spArg a b c) = false ∧ fsD (spArg a b c) ζ = spArg a b (fsD c ζ)

theorem node_fsD {a b c ζ : T} (h : FrameD a b c ζ) :
    fsD (psi a (spArg a b c) z) ζ = psi a (spArg a b (fsD c ζ)) z := by
  obtain ⟨hX, hs, hf⟩ := h
  rw [fsD_psi hX hs, hf]

/-- The conditions along a whole context. -/
def FramesD : List (T × T) → T → T → Prop
  | [], _, _ => True
  | (a, b) :: fr, c, ζ => FrameD a b c ζ ∧ FramesD fr (psi a (spArg a b c) z) ζ

/-- **`fsD` goes down a context.** -/
theorem fillC_fsD : ∀ (ctx : List (T × T)) {c ζ : T}, FramesD ctx c ζ →
    fsD (fillC ctx c) ζ = fillC ctx (fsD c ζ)
  | [], _, _, _ => rfl
  | (a, b) :: fr, c, ζ, ⟨h1, h2⟩ => by
    simp only [fillC]
    rw [fillC_fsD fr h2, node_fsD h1]

end Ytosk
