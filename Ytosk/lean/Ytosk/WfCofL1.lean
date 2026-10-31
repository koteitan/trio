/-
**EvalFSNZ の項の側: 基本列 s[k] と fsD の比較。**

- `DiagAt.fs_eq_fsD_gam`: 対角化の点の上では s[k] = fsD(s, γ_k)（γ_0 = 0, γ_{k+1} = ψ_μ(b[γ_k])）。
- `DiagAt.fs_le_fsD`: γ_k ≤ ζ ⇒ s[k] ≤ fsD(s, ζ)。
- `SuccAt`: ω 型の基本列が後続の引数 ψ_a(b)（b 後続）から来る場合。s[k] = fsD(s, k) で、
  k ≤ count ζ ⇒ s[k] ≤ fsD(s, ζ)。
- `fs_eq_fsD_of_cof_succ`: 後続なら s[η] = fsD(s, η′)（どちらも前者）。
- `omega_path`: cof s = ω なら対角化の点か後続の引数の点がある。
- `IdxLB s k ζ`（ζ が k 番目の添字以上）と `fs_le_fsD_of_idxLB`。
- `EngLB c`（展開の値は fsD(tA, ζ) 以上で ζ は k 番目の添字以上）から `EvalFSNZ c`（`evalFSNZ_of_engLB`）。
-/
import Ytosk.WfCof
import Ytosk.V3FrameT1

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-! ## 枠の単調性（≤） -/

theorem psi_rest_le {a b x y : T} (h : x ≤ y) : psi a b x ≤ psi a b y := by
  rcases (le_iff _ _).mp h with h | rfl
  · exact Or.inl (T.psi_lt_psi.mpr (Or.inr (Or.inr ⟨rfl, rfl, h⟩)))
  · exact Or.inr rfl

theorem psi_arg_le {a x y : T} (h : x ≤ y) : psi a x z ≤ psi a y z := by
  rcases (le_iff _ _).mp h with h | rfl
  · exact Or.inl (psi_lt_psi_z_iff.mpr (Or.inr ⟨rfl, h⟩))
  · exact Or.inr rfl

theorem psi_sub_le {x y : T} (h : x ≤ y) : psi x z z ≤ psi y z z := by
  rcases (le_iff _ _).mp h with h | rfl
  · exact Or.inl (psi_lt_psi_z_iff.mpr (Or.inl h))
  · exact Or.inr rfl

theorem mulT_lt_succL (a c : T) : ∀ k, mulT (psi a c z) k < mulT (psi a c z) (k + 1)
  | 0 => by simp only [mulT, app_psi, app_z]; exact T.z_lt_psi _ _ _
  | k + 1 => by
    show app (psi a c z) (mulT (psi a c z) k) < app (psi a c z) (mulT (psi a c z) (k + 1))
    simp only [app_psi, app_z]
    exact T.psi_lt_psi.mpr (Or.inr (Or.inr ⟨rfl, rfl, mulT_lt_succL a c k⟩))

theorem mulT_le_of_le (a c : T) {k k' : Nat} (h : k ≤ k') :
    mulT (psi a c z) k ≤ mulT (psi a c z) k' := by
  induction h with
  | refl => exact Or.inr rfl
  | step _ ih => exact le_trans ih (Or.inl (mulT_lt_succL a c _))

/-! ## 対角化の点 -/

/-- **At a diagonal point, `s[k] = fsD(s, γ_k)`.** -/
theorem DiagAt.fs_eq_fsD_gam {a b μ : T} {t : T} (h : DiagAt a b μ t) (k : Nat) :
    fs t (natT k) = fsD t (gam μ b k) := by
  induction h with
  | here hb hc hμ => rw [fs_psi_diag hb hc hμ, fsD_here hb hc]
  | @rest a' b' c d e _ ih =>
    show psi a' b' (fs (psi c d e) _) = psi a' b' (fsD (psi c d e) _)
    rw [ih]
  | @arg a' b' hb hs hD ih =>
    rw [fsD_psi hb hs]
    have hc := hD.cof_omega
    conv => lhs; unfold fs
    rw [if_neg hb, if_neg (by rw [hs]; simp), hc]
    simp only
    rw [ih]
  | @sub a' ha hs _ ih =>
    rw [fsD_sub ha hs]
    conv => lhs; unfold fs
    rw [if_pos rfl, if_neg ha, if_neg (by rw [hs]; simp), ih]

/-- **The term lemma**: `γ_k ≤ ζ ⇒ s[k] ≤ fsD(s, ζ)` at a diagonal point. -/
theorem DiagAt.fs_le_fsD {a b μ t : T} (h : DiagAt a b μ t) {k : Nat} {ζ : T}
    (hle : gam μ b k ≤ ζ) : fs t (natT k) ≤ fsD t ζ := by
  rw [h.fs_eq_fsD_gam k]
  rcases (le_iff _ _).mp hle with hlt | heq
  · exact Or.inl (h.fsD_mono hlt)
  · rw [heq]

/-! ## 後続の引数の点 -/

/-- The `ω`-type fundamental sequence comes from `ψ_a(b)` with `b` a successor. -/
inductive SuccAt (a b : T) : T → Prop
  | here : b ≠ z → isSucc b = true → SuccAt a b (psi a b z)
  | rest {a' b' c d e : T} : SuccAt a b (psi c d e) → SuccAt a b (psi a' b' (psi c d e))
  | arg {a' b' : T} : b' ≠ z → isSucc b' = false → SuccAt a b b' → SuccAt a b (psi a' b' z)
  | sub {a' : T} : a' ≠ z → isSucc a' = false → SuccAt a b a' → SuccAt a b (psi a' z z)

theorem SuccAt.cof_omega {a b t : T} (h : SuccAt a b t) : cof t = .omega := by
  induction h with
  | here hb hs =>
    unfold cof; rw [if_neg hb, if_pos hs]
  | rest _ ih => simpa [cof] using ih
  | arg hb hs _ ih =>
    unfold cof; rw [if_neg hb, if_neg (by rw [hs]; simp), ih]
  | sub ha hs _ ih =>
    unfold cof; rw [if_pos rfl, if_neg ha, if_neg (by rw [hs]; simp), ih]

theorem SuccAt.fs_eq_fsD {a b t : T} (h : SuccAt a b t) (η : T) : fs t η = fsD t η := by
  induction h with
  | here hb hs =>
    unfold fs fsD; rw [if_neg hb, if_pos hs, if_neg hb, if_pos hs]
  | @rest a' b' c d e _ ih =>
    show psi a' b' (fs (psi c d e) _) = psi a' b' (fsD (psi c d e) _)
    rw [ih]
  | @arg a' b' hb hs hS ih =>
    rw [fsD_psi hb hs]
    have hc := hS.cof_omega
    conv => lhs; unfold fs
    rw [if_neg hb, if_neg (by rw [hs]; simp), hc]
    simp only
    rw [ih]
  | @sub a' ha hs _ ih =>
    rw [fsD_sub ha hs]
    conv => lhs; unfold fs
    rw [if_pos rfl, if_neg ha, if_neg (by rw [hs]; simp), ih]

theorem SuccAt.fsD_le {a b t : T} (h : SuccAt a b t) {η η' : T} (hc : count η ≤ count η') :
    fsD t η ≤ fsD t η' := by
  induction h with
  | here hb hs =>
    unfold fsD; rw [if_neg hb, if_pos hs, if_neg hb, if_pos hs]
    exact mulT_le_of_le _ _ hc
  | @rest a' b' c d e _ ih =>
    show psi a' b' (fsD (psi c d e) _) ≤ psi a' b' (fsD (psi c d e) _)
    exact psi_rest_le ih
  | @arg a' b' hb hs _ ih =>
    rw [fsD_psi hb hs, fsD_psi hb hs]; exact psi_arg_le ih
  | @sub a' ha hs _ ih =>
    rw [fsD_sub ha hs, fsD_sub ha hs]; exact psi_sub_le ih

/-! ## 後続 -/

/-- **Successor**: every fundamental sequence member is the predecessor. -/
theorem fs_eq_fsD_of_cof_succ : ∀ (t : T), cof t = .succ → ∀ η η', fs t η = fsD t η'
  | z, h, _, _ => by simp [cof] at h
  | psi a b (psi c d e), h, η, η' => by
    have h' : cof (psi c d e) = .succ := by simpa [cof] using h
    show psi a b (fs (psi c d e) η) = psi a b (fsD (psi c d e) η')
    rw [fs_eq_fsD_of_cof_succ _ h' η η']
  | psi a b z, h, η, η' => by
    by_cases hb : b = z
    · subst hb
      by_cases ha : a = z
      · subst ha; simp [fs, fsD]
      · exfalso
        by_cases hsa : isSucc a = true
        · simp [cof, ha, hsa] at h
        · have : cof a = .succ := by simpa [cof, ha, hsa] using h
          exact fs_succ_eq.cof_succ_isSucc a this hsa
    · exfalso
      by_cases hsb : isSucc b = true
      · simp [cof, hb, hsb] at h
      · have hsb' : isSucc b = false := by simpa using hsb
        rcases hcb : cof b with _ | _ | _ | μ
        · simp [cof, hb, hsb', hcb] at h
        · exact fs_succ_eq.cof_succ_isSucc b hcb hsb
        · simp [cof, hb, hsb', hcb] at h
        · by_cases hl : lt μ a = true
          · simp [cof, hb, hsb', hcb, hl] at h
          · simp [cof, hb, hsb', hcb, hl] at h

/-! ## ω 型の分類 -/

/-- **Cofinality `ω` has a diagonal point or a successor-argument point.** -/
theorem omega_path : ∀ (t : T), cof t = .omega →
    (∃ a b μ, DiagAt a b μ t) ∨ (∃ a b, SuccAt a b t)
  | z, h => by simp [cof] at h
  | psi a b (psi c d e), h => by
    have h' : cof (psi c d e) = .omega := by simpa [cof] using h
    rcases omega_path _ h' with ⟨a0, b0, μ, hD⟩ | ⟨a0, b0, hS⟩
    · exact Or.inl ⟨a0, b0, μ, DiagAt.rest hD⟩
    · exact Or.inr ⟨a0, b0, SuccAt.rest hS⟩
  | psi a b z, h => by
    by_cases hb : b = z
    · subst hb
      by_cases ha : a = z
      · subst ha; simp [cof] at h
      · by_cases hsa : isSucc a = true
        · simp [cof, ha, hsa] at h
        · have hsa' : isSucc a = false := by simpa using hsa
          have h' : cof a = .omega := by simpa [cof, ha, hsa] using h
          rcases omega_path a h' with ⟨a0, b0, μ, hD⟩ | ⟨a0, b0, hS⟩
          · exact Or.inl ⟨a0, b0, μ, DiagAt.sub ha hsa' hD⟩
          · exact Or.inr ⟨a0, b0, SuccAt.sub ha hsa' hS⟩
    · by_cases hsb : isSucc b = true
      · exact Or.inr ⟨a, b, SuccAt.here hb hsb⟩
      · have hsb' : isSucc b = false := by simpa using hsb
        rcases hcb : cof b with _ | _ | _ | μ
        · simp [cof, hb, hsb', hcb] at h
        · simp [cof, hb, hsb', hcb] at h
        · rcases omega_path b hcb with ⟨a0, b0, μ, hD⟩ | ⟨a0, b0, hS⟩
          · exact Or.inl ⟨a0, b0, μ, DiagAt.arg hb hsb' hD⟩
          · exact Or.inr ⟨a0, b0, SuccAt.arg hb hsb' hS⟩
        · by_cases hl : lt μ a = true
          · simp [cof, hb, hsb', hcb, hl] at h
          · exact Or.inl ⟨a, b, μ, DiagAt.here hb hcb hl⟩

/-! ## 添字の下限 -/

/-- `ζ` is at least the `k`-th index of the fundamental sequence of `t`: `γ_k ≤ ζ` at a diagonal point,
`k ≤ count ζ` at a successor-argument point. -/
def IdxLB (t : T) (k : Nat) (ζ : T) : Prop :=
  (∀ a b μ, DiagAt a b μ t → gam μ b k ≤ ζ) ∧ (∀ a b, SuccAt a b t → k ≤ count ζ)

theorem fs_le_fsD_of_idxLB {t : T} (hc : ∀ μ, cof t ≠ .big μ) {k : Nat} {ζ : T}
    (h : IdxLB t k ζ) : fs t (natT k) ≤ fsD t ζ := by
  rcases hct : cof t with _ | _ | _ | μ
  · have ht : t = z := by
      by_contra hne; exact cof_ne_zero t hne hct
    subst ht; simp only [fs, fsD]; exact Or.inr rfl
  · rw [fs_eq_fsD_of_cof_succ t hct _ ζ]
  · rcases omega_path t hct with ⟨a, b, μ, hD⟩ | ⟨a, b, hS⟩
    · exact hD.fs_le_fsD (h.1 a b μ hD)
    · rw [hS.fs_eq_fsD]
      exact hS.fsD_le (by rw [count_natT]; exact h.2 a b hS)
  · exact absurd hct (hc μ)

/-- Below `Ω_1` the cofinality is not big. -/
theorem cof_not_big_of_lt_Om1 {t : T} (hot : isOT t = true) (hlt : t < psi one z z) :
    ∀ μ, cof t ≠ .big μ := by
  intro μ h
  by_cases ht : t = z
  · subst ht; simp [cof] at h
  · rcases cof_of_lt_Om1 t hot hlt ht with h' | h' <;> rw [h] at h' <;> cases h'

/-! ## 帰着: 展開側の下限 `EngLB` から `EvalFSNZ` -/

/-- **The engine-side lower bound**: the value of `A[k + c]` is at least `fsD(tA, ζ)` for some `ζ`
that is at least the `k`-th index of `tA`. -/
def EngLB (c : Nat) : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) →
    ∀ tA, Val A tA → ∀ k tN, Val (expand A (k + c)) tN → ∃ ζ, IdxLB tA k ζ ∧ fsD tA ζ ≤ tN

theorem evalFSNZ_of_engLB {c : Nat} (hD : Desc3) (h : EngLB c) : EvalFSNZ c := by
  intro A hA hS hE hz tA hv k tN hvN
  obtain ⟨tA', _, hv', _, hot, _⟩ := hD A 0 hA hS hE
  cases val_unique hv hv'
  obtain ⟨ζ, hI, hle⟩ := h A hA hS hE hz tA hv k tN hvN
  exact le_trans (fs_le_fsD_of_idxLB (cof_not_big_of_lt_Om1 hot (val_lt_Om1 hv)) hI) hle

/-- **Surjectivity from step 1 and the engine-side lower bound.** -/
theorem surj_of_engLB {c : Nat} (hD : Desc3) (hF : EngLB c) {t : T}
    (hot : isOT t = true) {n : Nat} {tN : T} (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  surj_of_evalFSNZ hD (evalFSNZ_of_engLB hD hF) hot hvN hlt

end Ytosk
