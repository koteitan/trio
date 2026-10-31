/-
**WfQnH3 (2026-11-01): `OLocal` off the closure of the bad calls (the `hO` of `WfQnL3.t1_pathB`) from `TPLoSX`.**
- `olocal_ofB`: `olocal_of` (V3OLocal) with the low-part field asked only at calls `i ∉ DepXB M B` (for the
  counted child `c`).
- `hW_of_TP1_0`, `hLoB`: the persistence and low-part fields with the holes of `t1_hole0` (no `VLocal`), the
  low part only off the closure.
- `TPLB` (the low-part comparison at `ζ` off the closure) from `TPLoSX` and the measured closure claim
  `TPLoSXIn` (a `TPLoSX` witness at a failing call lies in the closure): `tplB_of_tpLoSX`.
- `olocal_t1B`: the `hO` of `t1_pathB`.
-/
import Ytosk.WfQnH2

namespace Ytosk.WfQnH3
open T Ytosk Ytosk.WfQnE2 Ytosk.WfBad

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ br vr ζ : T}

theorem olocal_ofB {B : Nat → Prop} (hC : Cons M ρ) (hG : Good3 M ρ) (hx : x + 1 = M.length)
    (hrx : r < x) (hAr : Anc0 M r x) (hro : ρ.o r = psi vr br z) (hqr : par M 0 x ≠ some r)
    (hF1 : ∀ i, r < i → i < x → DepX M x true i → ¬ DepX M x false i → lt μ (ρ.v i) = true)
    (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
    (hHole : ∀ b i, DepX M x b i → (i < x ∨ (i = x ∧ b = true)) →
      HoleT μ br vr (valB ρ b i) ∧ DiagLe μ br vr r i (valB ρ b i))
    (hζ : ∃ X, ζ = psi μ X z) (hox : fsD (ρ.o x) ζ = ζ)
    (hok : ∀ t, isOT t = true → HoleT μ br vr t → isOT (fsD t ζ) = true)
    (hW : ∀ i L c R, i < x → DepX M x true i → children M i = L ++ c :: R → Counted M i c → DepX M x true c →
      ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L) y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true → lt (preState M ρ i L) (fsD y ζ) = true)
    (hL : ∀ i L c R, i < x → DepX M x true i → ¬ WfQnE3.DepXB M B true i → children M i = L ++ c :: R →
      Counted M i c → DepX M x true c →
      ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L) y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      ((split y (psi (succ s) z z)).2 ≠ z → fsD (split y (psi (succ s) z z)).2 ζ ≠ z) ∧
      ((split y (psi (succ s) z z)).2 = z → (split (fsD y ζ) (psi (succ s) z z)).2 = z)) :
    ∀ i, i < x → DepX M x true i → ¬ WfQnE3.DepXB M B true i → OLocal M x ρ ζ μ vr br i := by
  intro i hi hd hnb
  have hiM : i < M.length := by omega
  rcases hOS i hi hd with ha | ⟨hv, L, c, R, hch, hcb, hcu, hR, hLnd⟩
  · exact Or.inl ha
  right
  -- `c` is in `D`
  have hcmem : c ∈ children M i := by rw [hch]; exact List.mem_append_right _ List.mem_cons_self
  have hdc : DepX M x true c := by
    cases hd with
    | leaf => omega
    | @ochild _ c' hc' hb' hu' hd' =>
      have : c' = c := by
        rw [hch] at hc'
        rcases List.mem_append.mp hc' with h | h
        · exact absurd hd' (hLnd c' h ⟨hb', hu'⟩)
        · rcases List.mem_cons.mp h with h | h
          · exact h
          · rcases hR c' h with h' | h'
            · exact absurd h' hb'
            · exact absurd h' hu'
      rw [← this]; exact hd'
    | ov hv' => exact absurd hv' hv
  have hcM := (mem_children hcmem).2
  have hic := (mem_children hcmem).1
  have hcx : c ≤ x := by omega
  have hcpos : c < x ∨ (c = x ∧ true = true) := by
    rcases Nat.lt_or_ge c x with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, rfl⟩
  obtain ⟨hHc, hDc⟩ := hHole true c hdc hcpos
  simp only [valB, cond_true] at hHc hDc
  have hframe := o_frame hC hG hiM hch hcb hcu hR hcM
  have hpar : r < c → r ≤ i := fun h => par0_ge_of_anc hAr h hcx (mem_children_iff.mp hcmem).2
  refine ⟨hv, L, c, R, hch, hcb, hcu, hR, hLnd, ?_, ?_, hW i L c R hi hd hch ⟨hcb, hcu⟩ hdc,
    hL i L c R hi hd hnb hch ⟨hcb, hcu⟩ hdc, ?_⟩
  · -- single
    obtain ⟨X, hX⟩ := hζ
    apply single_fsD (o_psi_form hC hcM) (holeT_not_succ hHc)
      (fun s y he hy => not_succ_arg_of_holeT hy (by rw [← he]; exact hHc)) ⟨μ, X, hX⟩
      (hok _ (hG.ot_o c hcM) hHc)
  · -- the leaf condition
    intro s y hcv hyz s' y' hmem
    subst hyz
    by_cases hsz : s = z
    · subst hsz
      have := holeT_not_succ hHc; rw [hcv] at this
      have h1 : isSucc (psi z z z) = true := rfl; rw [h1] at this; cases this
    by_cases hss : isSucc s = true
    · -- `c = x`
      have hcxe : c = x := by
        rcases Nat.lt_or_ge c x with h | h
        · exfalso
          rcases hOS c h hdc with ⟨hvc, hnc⟩ | ⟨_, L', c', R', hch', hcb', hcu', hR', _⟩
          · obtain ⟨hHv, _⟩ := hHole false c hvc (Or.inl h)
            simp only [valB, cond_false] at hHv
            have hoc := o_nocnt hC hG hcM hnc
            rw [hcv] at hoc
            have hs : s = ρ.v c := (T.psi.inj hoc).1
            rw [hs, holeT_not_succ hHv] at hss; cases hss
          · have hc'M := (mem_children (by rw [hch']; exact List.mem_append_right _ List.mem_cons_self :
              c' ∈ children M c)).2
            have hfr := o_frame hC hG hcM hch' hcb' hcu' hR' hc'M
            obtain ⟨s3, y3, hc3⟩ := o_psi_form hC hc'M
            rw [hc3, spArg_single, hcv] at hfr
            have h3 : isOT (psi s3 y3 z) = true := by rw [← hc3]; exact hG.ot_o c' hc'M
            exact step_ne_z h3 (T.psi.inj hfr).2.1.symm
        · omega
      subst hcxe
      have hix : par M 0 c = some i := (mem_children_iff.mp hcmem).2
      have hri : r < i := by
        rcases Nat.eq_or_lt_of_le (hpar hrx) with h | h
        · exact absurd (h ▸ hix) hqr
        · exact h
      right
      rw [← hcv, hox] at hmem
      obtain ⟨X, hX⟩ := hζ
      rw [hX] at hmem
      simp only [summands, List.mem_cons, List.mem_nil_iff, or_false, psi.injEq] at hmem
      obtain ⟨rfl, _, _⟩ := hmem
      exact hF1 i hri hi hd hv
    · left
      rw [fsD_sub hsz (by simpa using hss)] at hmem
      simp only [summands, List.mem_cons, List.mem_nil_iff, or_false, psi.injEq] at hmem
      obtain ⟨_, rfl, _⟩ := hmem
      exact z_le _
  · -- the passing condition
    intro s y hcv hcof
    have hrc : r < c := by
      by_contra h
      obtain ⟨a', _, hD⟩ := hDc (by omega)
      rw [hcv] at hD
      exact DiagAt.cof_ne hD hcof
    rcases Nat.eq_or_lt_of_le (hpar hrc) with h | h
    · right
      have h' := hframe
      rw [hcv, spArg_single, ← h, hro] at h'
      rw [← h]
      exact ⟨(T.psi.inj h').1.symm, (T.psi.inj h').2.1.symm⟩
    · exact Or.inl (hF1 i h hi hd hv)


end

/-- **The low-part comparison at `ζ`, asked only off the closure.** -/
def TPLB (M : Mat) (x : Nat) (ρ : Valn) (B : Nat → Prop) (μ ζ : T) : Prop :=
  ∀ c, c < M.length → DepX M x true c → ¬ WfQnE3.DepXB M B true c → ∀ s y, ρ.o c = psi s y z →
    (split y (psi (succ s) z z)).2 = z → ∀ a, last y = psi a z z → isSucc a = false →
    OHole a → holeLev y = μ → ¬ psi (fsD a ζ) z z < psi (succ s) z z

/-- **The closure claim** (measured, tmp/wf/WfQnH/meas.py `TZ`): a call `c` where the comparison fails at `ζ`
and a `TPLoSX` witness `i` exists lies in the closure of the bad calls at `ζ`. -/
def TPLoSXIn (M : Mat) (ρ : Valn) (r : Nat) (μ ζ : T) : Prop :=
  ∀ c i m s y a, c < M.length - 1 → DepX M (M.length - 1) true c → i < M.length - 1 →
    DepX M (M.length - 1) false i → BadShape1 M i → par M 0 i = some m → Anc0 M c m →
    ρ.o c = psi s y z → (split y (psi (succ s) z z)).2 = z → last y = psi a z z → isSucc a = false →
    OHole a → holeLev y = μ → a = bumpW M ρ i → bumpW M ρ i = ρ.o r → ¬ vOpt ρ (par M 1 i) < s →
    psi (fsD a ζ) z z < psi (succ s) z z →
    WfQnE3.DepXB M (BadSet M (M.length - 1) ρ r ζ) true c

/-- **`TPLB` from `TPLoSX`** and the closure claim. -/
theorem tplB_of_tpLoSX {M : Mat} {ρ : Valn} {rk : Bool → Nat → Nat} {r : Nat} {μ br ζ : T}
    (h : TPLoSX M ρ rk) (hin : TPLoSXIn M ρ r μ ζ)
    (h1 : par M 1 (M.length - 1) = some r) (h0 : par M 0 (M.length - 1) ≠ some r)
    (h2 : entry M 2 (M.length - 1) = 0) (hro : ρ.o r = psi μ br z)
    (hox : ρ.o (M.length - 1) = psi (succ μ) z z)
    (hζ : (drop1 M (M.length - 1) rk).o r ≤ ζ) :
    TPLB M (M.length - 1) ρ (BadSet M (M.length - 1) ρ r ζ) μ ζ := by
  intro c hc hd hnb s y ho hy a hla hns hO hl hlt
  by_cases hcx : c < M.length - 1
  · rcases h r μ br h1 h0 h2 hro c hcx hd s y ho hy a hla hns hO hl with hn | ⟨i, m, hi, hdi, hbs, hm, hcm, ha, hW, hv⟩
    · exact hn (lt_of_le_of_lt (le_psi_sub (fsD_mono_eta hO hζ)) hlt)
    · exact hnb (hin c i m s y a hcx hd hi hdi hbs hm hcm ho hy hla hns hO hl ha hW hv hlt)
  · have he : c = M.length - 1 := by omega
    subst he
    rw [hox] at ho
    cases ho
    simp [last] at hla

section
variable {M : Mat} {x r : Nat} {ρ : Valn} {μ br vr ζ : T} (hx : x + 1 = M.length)
  (hR0 : R0P M) (hZ2 : Z2 M) (hSD : SibDec M) (hZ1 : Z1C M) (hUAT : UAT M) (hUAB : UAB M)
  (hx2 : entry M 2 x = 0) {q : Nat} (hq : par M 0 x = some q)
  (hC : Cons M ρ) (hG : Good3 M ρ) (hKD : BumpKidsDec M ρ) (hTD : BumpTermDec M ρ)
  (hrx : r < x) (hAr : Anc0 M r x) (hro : ρ.o r = psi vr br z)
  (hcb : cof br = .big μ) (hμr : μ = vr) (hbr : br ≠ z)
  (hox : ρ.o x = psi (succ μ) z z)
  (hF1 : ∀ i, r < i → i < x → DepX M x true i → ¬ DepX M x false i → lt μ (ρ.v i) = true)
  (hOS : ∀ i, i < x → DepX M x true i → OShape M x i)
  (hS2 : ∀ i k, i ≤ r → DepX M x false i → entry M 2 i = 0 → upg M i = some k → k ≤ r)
  (hS3 : ∀ i j k, i ≤ r → j ∈ children M i → col M j = bump M i → k ∈ children M j →
    DepX M x true k → k ≤ r)
include hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hrx hAr hro hcb hμr hbr hox hF1 hOS hS2 hS3

/-- Holes and positions without `VLocal` (`t1_hole0`), in the form read by `olocal_of`. -/
theorem hole0 : ∀ b i, DepX M x b i → (i < x ∨ (i = x ∧ b = true)) →
    HoleT μ br vr (valB ρ b i) ∧ DiagLe μ br vr r i (valB ρ b i) := by
  intro b i hD hp
  have h := t1_hole0 hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hrx hAr hro hcb hμr hbr
    (Or.inl (by rw [hox]; exact cof_omega_succ μ)) hF1 hOS hS2 hS3 b i hD hp
  exact ⟨h.1, h.2.1⟩

/-- **(W) from TP1 without `VLocal`** (`hW_of_TP1` with `t1_hole0`). -/
theorem hW_of_TP1_0 {seed : T} (hTP : TP1C M ρ) (hseed : psi μ one z ≤ seed) :
    ∀ m i L' c R, i < x → DepX M x true i → children M i = L' ++ c :: R → Counted M i c →
      DepX M x true c → ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L') y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      lt (preState M ρ i L') (fsD y (gamS μ br seed m)) = true := by
  have hH := hole0 hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hrx hAr hro hcb hμr hbr hox hF1 hOS hS2 hS3
  intro m i L' c R hi _ hch hcnt hdc s y hcv hlt1 hlt2
  have hcM : c ∈ children M i := by rw [hch]; simp
  have hcl := (mem_children hcM).2
  obtain ⟨hHc, _⟩ := hH true c hdc (by
    rcases Nat.lt_or_ge c x with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, rfl⟩)
  simp only [valB, cond_true] at hHc
  rw [hcv] at hHc
  have hy : y ≠ z := by
    intro h; rw [h] at hlt1; exact T.not_lt_z _ hlt1
  have hHy := holeT_arg hy hHc hcb
  have hOy := ohole_of_holeT hHy
  have h0 := hTP i L' c R hch hcnt s y hcv hlt1 hlt2 hOy
  rw [holeLev_holeT hHy] at h0
  exact persist_of_tp1 hOy (gamS_ge_one hcb hseed m) h0

/-- **(L) off the closure** (`hLo_of_TPLS` with `t1_hole0` and `TPLB`). -/
theorem hLoB {B : Nat → Prop} (hTPL : TPLB M x ρ B μ ζ) (hbrl : last br ≠ psi (succ μ) z z) (hζz : ζ ≠ z) :
    ∀ i L' c R, i < x → DepX M x true i → ¬ WfQnE3.DepXB M B true i → children M i = L' ++ c :: R →
      Counted M i c → DepX M x true c → ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L') y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true →
      ((split y (psi (succ s) z z)).2 ≠ z → fsD (split y (psi (succ s) z z)).2 ζ ≠ z) ∧
      ((split y (psi (succ s) z z)).2 = z → (split (fsD y ζ) (psi (succ s) z z)).2 = z) := by
  have hH := hole0 hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hrx hAr hro hcb hμr hbr hox hF1 hOS hS2 hS3
  intro i L' c R hi hd hnb hch hcnt hdc s y hcv hlt1 _
  have hcM : c ∈ children M i := by rw [hch]; simp
  have hy : y ≠ z := by
    intro h; rw [h] at hlt1; exact T.not_lt_z _ hlt1
  have hcx : c < x := by
    by_contra hn
    have he : c = x := by have := (mem_children hcM).2; omega
    subst c
    rw [hox] at hcv
    cases hcv
    exact hy rfl
  obtain ⟨hHc, _⟩ := hH true c hdc (Or.inl hcx)
  simp only [valB, cond_true] at hHc
  rw [hcv] at hHc
  have hHy := holeT_arg hy hHc hcb
  refine ⟨lo_ne_z_of_holeT hζz hHy, fun hl => ?_⟩
  have hTPLf : (split y (psi (succ s) z z)).2 = z →
      ∀ a, last y = psi a z z → isSucc a = false → OHole a →
        ¬ psi (fsD a ζ) z z < psi (succ s) z z := by
    intro hs a ha hns hO
    exact hTPL c (by omega) hdc (fun hd' => hnb (WfQnE3.DepXB.ochild hcM hcnt.1 hcnt.2 hd')) s y hcv hs a ha
      hns hO (holeLev_holeT hHy)
  exact lo_keep_of_TPLη hTPLf hy hHc hcb hbrl (le_refl ζ) hl

/-- **`OLocal` off the closure** (the `hO` of `WfQnL3.t1_pathB`) from (W), `TPLB`, and the holes of `t1_hole0`. -/
theorem olocal_t1B {B : Nat → Prop} (hqr : par M 0 x ≠ some r) (hTPL : TPLB M x ρ B μ ζ)
    (hbrl : last br ≠ psi (succ μ) z z) (hζ : ∃ X, ζ = psi μ X z)
    (hok : ∀ t, isOT t = true → HoleT μ br vr t → isOT (fsD t ζ) = true)
    (hW : ∀ i L c R, i < x → DepX M x true i → children M i = L ++ c :: R → Counted M i c → DepX M x true c →
      ∀ s y, ρ.o c = psi s y z → lt (preState M ρ i L) y = true →
      lt (psi (ρ.v i) z z) (psi s y z) = true → lt (preState M ρ i L) (fsD y ζ) = true) :
    ∀ i, i < x → DepX M x true i → ¬ WfQnE3.DepXB M B true i → OLocal M x ρ ζ μ vr br i := by
  have hζz : ζ ≠ z := by obtain ⟨X, hX⟩ := hζ; rw [hX]; simp
  have hoxζ : fsD (ρ.o x) ζ = ζ := by
    rw [hox]; exact fsD_leaf (isSucc_succ μ) (succ_ne_z μ)
  exact olocal_ofB hC hG hx hrx hAr hro hqr hF1 hOS
    (hole0 hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hrx hAr hro hcb hμr hbr hox hF1 hOS hS2 hS3)
    hζ hoxζ hok hW
    (hLoB hx hR0 hZ2 hSD hZ1 hUAT hUAB hx2 hq hC hG hKD hTD hrx hAr hro hcb hμr hbr hox hF1 hOS hS2 hS3
      hTPL hbrl hζz)

end

end Ytosk.WfQnH3
