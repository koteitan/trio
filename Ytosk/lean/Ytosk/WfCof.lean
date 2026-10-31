/-
**目標 5（全射）: 評価側の共終性 `EvalCof` を基本列の比較 `EvalFS` に帰着する。**

- `fs_cof_omega`（項だけ、無条件）: 標準形 s の共終数が ω なら、s より小さい標準形 t には t < s[k] となる k がある
  （s[k] = `fs s (natT k)`、対角化の始点 γ_0 = 0）。対角化の点は `cof_gam`。
- `le_fs_of_cof_succ`: 共終数が後続なら t < s ⇒ t ≤ s[k]（どの k でも）。
- `EvalFS c`: 標準形 A の値 tA について、どの k でも tA[k] ≤ (A[k + c] の値)。
  実測（tmp/wf/WfCof/fsprobe.py）では c = 2 で全集合・全族で成立（不足 n − L(n) の最大は 2）。
- `evalCof_of`: Desc3（値の存在）、`EvalFS c`、値が Ω_1 未満（`ValCtbl`）から `EvalCof`。
-/
import Ytosk.V3Surj
import Ytosk.V3SeedTop
import Ytosk.V3N0T1

namespace Ytosk

open T

/-! ## 項の側の共終性 -/

/-- Below a successor: `t < P + 1 → t ≤ P`. -/
theorem le_of_lt_app_one : ∀ (P : T) {t : T}, t < app P one → t ≤ P
  | z, t, h => by
    cases t with
    | z => exact z_le _
    | psi a b c =>
      exfalso
      simp only [app_z, one] at h
      rcases T.psi_lt_psi.mp h with h | ⟨_, h⟩ | ⟨_, _, h⟩ <;> exact T.not_lt_z _ h
  | psi a b c, t, h => by
    cases t with
    | z => exact z_le _
    | psi a' b' c' =>
      simp only [app_psi] at h
      rcases T.psi_lt_psi.mp h with h1 | ⟨h1, h2⟩ | ⟨rfl, rfl, h3⟩
      · exact Or.inl (T.psi_lt_psi.mpr (Or.inl h1))
      · exact Or.inl (T.psi_lt_psi.mpr (Or.inr (Or.inl ⟨h1, h2⟩)))
      · rcases le_of_lt_app_one c h3 with h4 | h4
        · exact Or.inl (T.psi_lt_psi.mpr (Or.inr (Or.inr ⟨rfl, rfl, h4⟩)))
        · exact Or.inr (by rw [h4])

/-- A standard term whose summands are at most `ψ_a(b)` is below `ψ_a(b) · (count + 1)`. -/
theorem lt_mulT_count {a b : T} : ∀ {x : T}, isOT x = true → head x ≤ psi a b z →
    x < mulT (psi a b z) (count x + 1)
  | z, _, _ => by simp [mulT, app]
  | psi a1 b1 x1, hx, hh => by
    show psi a1 b1 x1 < app (psi a b z) (mulT (psi a b z) (count x1 + 1))
    simp only [app_psi, app_z]
    rcases hh with hh | hh
    · rcases (psi_lt_psi_z_iff).mp hh with h | ⟨h1, h2⟩
      · exact T.psi_lt_psi.mpr (Or.inl h)
      · exact T.psi_lt_psi.mpr (Or.inr (Or.inl ⟨h1, h2⟩))
    · simp only [head] at hh
      injection hh with h1 h2
      subst h1; subst h2
      have hot := isOT_psi_iff.mp hx
      exact T.psi_lt_psi.mpr (Or.inr (Or.inr ⟨rfl, rfl, lt_mulT_count hot.2.2.1 hot.2.2.2.1⟩))

theorem mulT_one (h : T) (hh : ∃ a b, h = psi a b z) : mulT h 1 = h := by
  obtain ⟨a, b, rfl⟩ := hh; simp [mulT, app]

theorem gam_eq_gamS (μ b : T) : ∀ k, gam μ b k = gamS μ b z k
  | 0 => rfl
  | k + 1 => by simp only [gam, gamS, gam_eq_gamS μ b k]

/-- **Cofinality of the fundamental sequence** (`ω` type): below a standard `s` of cofinality `ω`,
every standard `t` is below some `s[k]`. -/
theorem fs_cof_omega : ∀ (s : T), isOT s = true → cof s = .omega →
    ∀ t, isOT t = true → t < s → ∃ k, t < fs s (natT k)
  | z, _, h, _, _, _ => by simp [cof] at h
  | psi a b (psi c d e), hs, hc, t, ht, hlt => by
    have hc' : cof (psi c d e) = .omega := by simpa [cof] using hc
    have hfs : ∀ k, fs (psi a b (psi c d e)) (natT k) = psi a b (fs (psi c d e) (natT k)) :=
      fun k => by simp [fs]
    cases t with
    | z => exact ⟨0, by rw [hfs]; exact T.z_lt_psi _ _ _⟩
    | psi a' b' c' =>
      rcases T.psi_lt_psi.mp hlt with h1 | ⟨h1, h2⟩ | ⟨rfl, rfl, h3⟩
      · exact ⟨0, by rw [hfs]; exact T.psi_lt_psi.mpr (Or.inl h1)⟩
      · exact ⟨0, by rw [hfs]; exact T.psi_lt_psi.mpr (Or.inr (Or.inl ⟨h1, h2⟩))⟩
      · obtain ⟨k, hk⟩ := fs_cof_omega (psi c d e) (isOT_rest hs) hc' c' (isOT_rest ht) h3
        exact ⟨k, by rw [hfs]; exact T.psi_lt_psi.mpr (Or.inr (Or.inr ⟨rfl, rfl, hk⟩))⟩
  | psi a b z, hs, hc, t, ht, hlt => by
    have hsot := isOT_psi_iff.mp hs
    cases t with
    | z =>
      refine ⟨1, ?_⟩
      -- every `s[1]` of a nonzero `ψ`-term with cofinality `ω` is nonzero
      by_cases hb : b = z
      · subst hb
        have ha : a ≠ z := by rintro rfl; simp [cof] at hc
        have hfs : fs (psi a z z) (natT 1) = psi (fs a (natT 1)) z z := by
          have hsa : isSucc a = false := by
            by_contra h'
            simp only [Bool.not_eq_false] at h'
            simp [cof, ha, h'] at hc
          conv => lhs; unfold fs
          simp [ha, hsa]
        rw [hfs]; exact T.z_lt_psi _ _ _
      · by_cases hsb : isSucc b = true
        · have hfs : fs (psi a b z) (natT 1) = mulT (psi a (init b) z) 1 := by
            conv => lhs; unfold fs
            simp [hb, hsb, count_natT]
          rw [hfs, mulT_one _ ⟨_, _, rfl⟩]; exact T.z_lt_psi _ _ _
        · have hfs : ∃ y, fs (psi a b z) (natT 1) = psi a y z := by
            conv => arg 1; ext y; lhs; unfold fs
            simp only [if_neg hb, hsb, Bool.false_eq_true, if_false]
            split
            · split
              · exact ⟨_, rfl⟩
              · exact ⟨_, rfl⟩
            · exact ⟨_, rfl⟩
          obtain ⟨y, hy⟩ := hfs
          rw [hy]; exact T.z_lt_psi _ _ _
    | psi a' b' c' =>
      have htot := isOT_psi_iff.mp ht
      by_cases hb : b = z
      · subst hb
        have ha : a ≠ z := by rintro rfl; simp [cof] at hc
        have hsa : isSucc a = false := by
          by_contra h'
          simp only [Bool.not_eq_false] at h'
          simp [cof, ha, h'] at hc
        have hca : cof a = .omega := by simpa [cof, ha, hsa] using hc
        have hfs : ∀ k, fs (psi a z z) (natT k) = psi (fs a (natT k)) z z := fun k => by
          conv => lhs; unfold fs
          simp [ha, hsa]
        have ha' : a' < a := by
          rcases T.psi_lt_psi.mp hlt with h1 | ⟨_, h2⟩ | ⟨_, _, h2⟩
          · exact h1
          · exact absurd h2 (T.not_lt_z _)
          · exact absurd h2 (T.not_lt_z _)
        obtain ⟨k, hk⟩ := fs_cof_omega a hsot.1 hca a' htot.1 ha'
        exact ⟨k, by rw [hfs]; exact T.psi_lt_psi.mpr (Or.inl hk)⟩
      · by_cases hsb : isSucc b = true
        · have hfs : ∀ k, fs (psi a b z) (natT k) = mulT (psi a (init b) z) k := fun k => by
            conv => lhs; unfold fs
            simp [hb, hsb, count_natT]
          rcases T.psi_lt_psi.mp hlt with h1 | ⟨rfl, h2⟩ | ⟨_, _, h3⟩
          · exact ⟨1, by rw [hfs, mulT_one _ ⟨_, _, rfl⟩]; exact T.psi_lt_psi.mpr (Or.inl h1)⟩
          · have hb0 : b' ≤ init b := by
              rw [← init_app_one hsb] at h2; exact le_of_lt_app_one _ h2
            rcases hb0 with hb0 | rfl
            · refine ⟨1, ?_⟩
              rw [hfs, mulT_one _ ⟨_, _, rfl⟩]
              exact T.psi_lt_psi.mpr (Or.inr (Or.inl ⟨rfl, hb0⟩))
            · refine ⟨count c' + 1 + 1, ?_⟩
              rw [hfs]
              show psi a' (init b) c' < app (psi a' (init b) z) (mulT (psi a' (init b) z) (count c' + 1))
              simp only [app_psi, app_z]
              exact T.psi_lt_psi.mpr (Or.inr (Or.inr ⟨rfl, rfl, lt_mulT_count htot.2.2.1 htot.2.2.2.1⟩))
          · exact absurd h3 (T.not_lt_z _)
        · have hsb' : isSucc b = false := by simpa using hsb
          -- the cofinality of the argument
          rcases hcb : cof b with _ | _ | _ | μ
          · simp [cof, hb, hsb', hcb] at hc
          · simp [cof, hb, hsb', hcb] at hc
          · -- `cof b = ω`: pass to the argument
            have hfs : ∀ k, fs (psi a b z) (natT k) = psi a (fs b (natT k)) z := fun k => by
              conv => lhs; unfold fs
              simp [hb, hsb', hcb]
            rcases T.psi_lt_psi.mp hlt with h1 | ⟨rfl, h2⟩ | ⟨_, _, h3⟩
            · exact ⟨0, by rw [hfs]; exact T.psi_lt_psi.mpr (Or.inl h1)⟩
            · obtain ⟨k, hk⟩ := fs_cof_omega b hsot.2.1 hcb b' htot.2.1 h2
              exact ⟨k, by rw [hfs]; exact T.psi_lt_psi.mpr (Or.inr (Or.inl ⟨rfl, hk⟩))⟩
            · exact absurd h3 (T.not_lt_z _)
          · -- `cof b = Ω_{μ+1}`: a diagonal point (else `cof s` is big)
            have hμ : ¬ lt μ a = true := by
              intro h; simp [cof, hb, hsb', hcb, h] at hc
            rcases T.psi_lt_psi.mp hlt with h1 | ⟨rfl, h2⟩ | ⟨_, _, h3⟩
            · exact ⟨0, by rw [fs_psi_diag hb hcb hμ]; exact T.psi_lt_psi.mpr (Or.inl h1)⟩
            · have haμ : a' ≤ μ := le_of_not_gt hμ
              have hcm : ∀ g ∈ comps μ b', g < b := fun g hg =>
                lt_trans (htot.2.2.2.2 g (comps_mono haμ hg)) h2
              obtain ⟨k, hk⟩ := cof_gam hs hcb hμ (size b') b' rfl h2 hcm
              refine ⟨k, ?_⟩
              rw [fs_psi_diag hb hcb hμ, gam_eq_gamS]
              exact T.psi_lt_psi.mpr (Or.inr (Or.inl ⟨rfl, hk⟩))
            · exact absurd h3 (T.not_lt_z _)

/-- The fundamental sequence of a successor is its predecessor (any index). -/
theorem fs_succ_eq : ∀ (s : T), cof s = .succ → ∀ η, app (fs s η) one = s
  | z, h, _ => by simp [cof] at h
  | psi a b (psi c d e), h, η => by
    have h' : cof (psi c d e) = .succ := by simpa [cof] using h
    show app (psi a b (fs (psi c d e) η)) one = psi a b (psi c d e)
    rw [app_psi, fs_succ_eq _ h' η]
  | psi a b z, h, η => by
    by_cases hb : b = z
    · subst hb
      by_cases ha : a = z
      · subst ha; simp [fs, one]
      · exfalso
        by_cases hsa : isSucc a = true
        · simp [cof, ha, hsa] at h
        · simp only [cof, if_neg ha, hsa, Bool.false_eq_true, if_false] at h
          exact absurd h (by
            intro h2
            -- `cof a = succ` with `a` not a successor is impossible
            exact cof_succ_isSucc a h2 hsa)
    · exfalso
      by_cases hsb : isSucc b = true
      · simp [cof, hb, hsb] at h
      · have hsb' : isSucc b = false := by simpa using hsb
        rcases hcb : cof b with _ | _ | _ | μ
        · simp [cof, hb, hsb', hcb] at h
        · exact cof_succ_isSucc b (by rw [hcb]) hsb
        · simp [cof, hb, hsb', hcb] at h
        · by_cases hl : lt μ a = true
          · simp [cof, hb, hsb', hcb, hl] at h
          · simp [cof, hb, hsb', hcb, hl] at h
where
  /-- `cof x = succ` only for successors. -/
  cof_succ_isSucc : ∀ (x : T), cof x = .succ → ¬ isSucc x = true → False
    | z, h, _ => by simp [cof] at h
    | psi a b (psi c d e), h, hs => by
      have h' : cof (psi c d e) = .succ := by simpa [cof] using h
      exact cof_succ_isSucc _ h' (by rwa [isSucc_psi_rest a b _ (by simp)] at hs)
    | psi a b z, h, hs => by
      by_cases hb : b = z
      · subst hb
        by_cases ha : a = z
        · subst ha; exact hs (by decide)
        · by_cases hsa : isSucc a = true
          · simp [cof, ha, hsa] at h
          · have h2 : cof a = .succ := by simpa [cof, ha, hsa] using h
            exact cof_succ_isSucc a h2 hsa
      · by_cases hsb : isSucc b = true
        · simp [cof, hb, hsb] at h
        · have hsb' : isSucc b = false := by simpa using hsb
          rcases hcb : cof b with _ | _ | _ | μ
          · simp [cof, hb, hsb', hcb] at h
          · exact cof_succ_isSucc b hcb hsb
          · simp [cof, hb, hsb', hcb] at h
          · by_cases hl : lt μ a = true
            · simp [cof, hb, hsb', hcb, hl] at h
            · simp [cof, hb, hsb', hcb, hl] at h

/-- Below a successor every term is at most each `s[k]`. -/
theorem le_fs_of_cof_succ {s t : T} (hc : cof s = .succ) (hlt : t < s) (η : T) : t ≤ fs s η := by
  have h := fs_succ_eq s hc η
  rw [← h] at hlt
  exact le_of_lt_app_one _ hlt

/-! ## 共終数は ω か後続（Ω_1 より下） -/

theorem cof_ne_zero : ∀ (x : T), x ≠ z → cof x ≠ .zero
  | z, h, _ => h rfl
  | psi a b (psi c d e), _, h => cof_ne_zero (psi c d e) (by simp) (by simpa [cof] using h)
  | psi a b z, _, h => by
    by_cases hb : b = z
    · subst hb
      by_cases ha : a = z
      · subst ha; simp [cof] at h
      · by_cases hsa : isSucc a = true
        · simp [cof, ha, hsa] at h
        · exact cof_ne_zero a ha (by simpa [cof, ha, hsa] using h)
    · by_cases hsb : isSucc b = true
      · simp [cof, hb, hsb] at h
      · have hsb' : isSucc b = false := by simpa using hsb
        rcases hcb : cof b with _ | _ | _ | μ
        · exact cof_ne_zero b hb hcb
        · simp [cof, hb, hsb', hcb] at h
        · simp [cof, hb, hsb', hcb] at h
        · by_cases hl : lt μ a = true
          · simp [cof, hb, hsb', hcb, hl] at h
          · simp [cof, hb, hsb', hcb, hl] at h

/-- Below `Ω_1`, a standard term has only index-`0` summands, hence a countable cofinality. -/
theorem cof_of_lt_Om1 : ∀ (s : T), isOT s = true → s < psi one z z → s ≠ z →
    cof s = .succ ∨ cof s = .omega
  | z, _, _, h => absurd rfl h
  | psi a b c, hs, hlt, _ => by
    have ha : a = z := by
      rcases T.psi_lt_psi.mp hlt with h | ⟨_, h⟩ | ⟨_, _, h⟩
      · cases a with
        | z => rfl
        | psi a1 b1 c1 =>
          exfalso; simp only [one] at h
          rcases T.psi_lt_psi.mp h with h | ⟨_, h⟩ | ⟨_, _, h⟩ <;> exact T.not_lt_z _ h
      · exact absurd h (T.not_lt_z _)
      · exact absurd h (T.not_lt_z _)
    subst ha
    cases c with
    | psi c1 d1 e1 =>
      have hsot := isOT_psi_iff.mp hs
      have hh : head (psi c1 d1 e1) ≤ psi z b z := hsot.2.2.2.1
      have hlt' : psi c1 d1 e1 < psi one z z := by
        have : psi c1 d1 z ≤ psi z b z := by simpa [head] using hh
        have h2 : psi z b z < psi one z z := T.psi_lt_psi.mpr (Or.inl (by
          simp only [one]; exact T.z_lt_psi _ _ _))
        rcases this with h3 | h3
        · have h4 := lt_trans h3 h2
          rcases (psi_lt_psi_z_iff).mp h4 with h5 | ⟨h5, h6⟩
          · exact T.psi_lt_psi.mpr (Or.inl h5)
          · exact absurd h6 (T.not_lt_z _)
        · injection h3 with h5 h6
          subst h5
          exact T.psi_lt_psi.mpr (Or.inl (by simp only [one]; exact T.z_lt_psi _ _ _))
      have := cof_of_lt_Om1 (psi c1 d1 e1) hsot.2.2.1 hlt' (by simp)
      simpa [cof] using this
    | z =>
      by_cases hb : b = z
      · subst hb; left; simp [cof]
      · by_cases hsb : isSucc b = true
        · right; simp [cof, hb, hsb]
        · have hsb' : isSucc b = false := by simpa using hsb
          rcases hcb : cof b with _ | _ | _ | μ
          · exact absurd hcb (cof_ne_zero b hb)
          · exact absurd (fs_succ_eq.cof_succ_isSucc b hcb hsb) id
          · right; simp [cof, hb, hsb', hcb]
          · right; simp [cof, hb, hsb', hcb, lt]

/-! ## 評価側の共終性への帰着 -/

/-- **The evaluation follows the fundamental sequence** with an index shift `c`: for a standard `A`
other than SRO and `[]`, `tA[k] ≤ (value of A[k + c])` for every `k`. Measured with `c = 2`. -/
def EvalFS (c : Nat) : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → ∀ tA, Val A tA → ∀ k tN, Val (expand A (k + c)) tN →
    fs tA (natT k) ≤ tN

/-- The values of standard forms are countable (below `Ω_1`). -/
def ValCtbl : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → ∀ tA, Val A tA → tA < psi one z z

/-! ## 値は Ω_1 未満（無条件） -/

/-- Every summand has index `0`. -/
def I0 : T → Prop
  | z => True
  | psi a _ c => a = z ∧ I0 c

theorem I0_add : ∀ {x y : T}, I0 x → I0 y → I0 (add x y)
  | z, _, _, hy => by simpa [add] using hy
  | psi a b c, y, hx, hy => by
    cases y with
    | z => simpa [add] using hx
    | psi d e f =>
      simp only [add]
      split
      · exact hy
      · exact ⟨hx.1, I0_add hx.2 hy⟩

theorem sp_z_form : ∀ (c b : T), ∃ y, sp z b c = psi z y z
  | z, b => ⟨b, by simp [sp]⟩
  | psi s y c, b => by
    simp only [sp]
    split
    · exact sp_z_form c _
    · exact sp_z_form c _

theorem I0_sf : ∀ {x : T}, I0 x → I0 (sf x)
  | z, _ => by simp [sf, I0]
  | psi a b c, hx => by
    obtain ⟨rfl, hc⟩ := hx
    simp only [sf]
    obtain ⟨y, hy⟩ := sp_z_form (sf b) (sf z)
    have hsz : sf z = z := by simp [sf]
    rw [hsz] at hy
    rw [hy]
    exact I0_add ⟨rfl, trivial⟩ (I0_sf hc)

theorem I0_sumN_aux : ∀ (l : List T) (acc : T), I0 acc → (∀ x ∈ l, I0 x) →
    I0 (l.foldl (fun a b => sf (add a b)) acc)
  | [], _, h, _ => h
  | x :: l, acc, h, hl => by
    simp only [List.foldl_cons]
    exact I0_sumN_aux l _ (I0_sf (I0_add h (hl x List.mem_cons_self)))
      (fun y hy => hl y (List.mem_cons_of_mem _ hy))

theorem I0_sumN (l : List T) (hl : ∀ x ∈ l, I0 x) : I0 (sumN l) :=
  I0_sumN_aux l z trivial hl

theorem I0_lt_Om1 : ∀ {x : T}, I0 x → x < psi one z z
  | z, _ => T.z_lt_psi _ _ _
  | psi a b c, h => by
    obtain ⟨rfl, _⟩ := h
    exact T.psi_lt_psi.mpr (Or.inl (by simp only [one]; exact T.z_lt_psi _ _ _))

/-- **The value of any evaluated matrix is below `Ω_1`.** -/
theorem val_lt_Om1 {M : Mat} {t : T} (h : Val M t) : t < psi one z z := by
  obtain ⟨ρ, _, hC, _, rfl⟩ := h
  apply I0_lt_Om1
  apply I0_sumN
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  have hi' := List.mem_range.mp hi
  split
  · rename_i hcol
    have he : entry M 1 i = 0 := by
      have : col M i = M.getD i (0, 0, 0) := rfl
      simp only [entry]
      rw [← this, hcol]; rfl
    obtain ⟨ho, hv⟩ := hC i hi'
    have hvz : ρ.v i = z := by rw [hv]; simp [vRhs, he]
    rw [ho]
    simp only [oRhs, hvz, sf]
    obtain ⟨y, hy⟩ := sp_z_form (sf (sumN ((children M i).map (cnt M ρ i)))) (sf z)
    have hsz : sf z = z := by simp [sf]
    rw [hsz] at hy
    rw [hy]
    exact I0_add ⟨rfl, trivial⟩ trivial
  · trivial

theorem valCtbl : ValCtbl := fun _ _ _ _ _ h => val_lt_Om1 h

/-- **EvalCof from the fundamental sequences.** -/
theorem evalCof_of {c : Nat} (hD : Desc3) (hF : EvalFS c) (hW : ValCtbl) : EvalCof := by
  intro A hA hAS hAE tA t hv hot hlt
  obtain ⟨tA', tN0, hv', _, hAot, _⟩ := hD A 0 hA hAS hAE
  cases val_unique hv hv'
  have hne : tA ≠ z := by rintro rfl; exact T.not_lt_z _ hlt
  have hle : ∃ k, t ≤ fs tA (natT k) := by
    rcases cof_of_lt_Om1 tA hAot (hW A hA hAS hAE tA hv) hne with hc | hc
    · exact ⟨0, le_fs_of_cof_succ hc hlt _⟩
    · obtain ⟨k, hk⟩ := fs_cof_omega tA hAot hc t hot hlt
      exact ⟨k, Or.inl hk⟩
  obtain ⟨k, hk⟩ := hle
  obtain ⟨_, tN, _, hvN, _, _⟩ := hD A (k + c) hA hAS hAE
  exact ⟨k + c, tN, hvN, le_trans hk (hF A hA hAS hAE tA hv k tN hvN)⟩

/-- `EvalCof` from step 1 and `EvalFS c` alone. -/
theorem evalCof_of_evalFS {c : Nat} (hD : Desc3) (hF : EvalFS c) : EvalCof :=
  evalCof_of hD hF valCtbl

/-! ## 最後の列が 0 の場合（無条件）: 値は前者 + 1 -/

/-- **A zero last column adds `1`**: the value of `M` is the value of `M.take x` plus one. -/
theorem val_zero_last {M : Mat} (hne : M ≠ []) (hz : col M (M.length - 1) = (0, 0, 0)) {tA tN : T}
    (hA : Val M tA) (hN : Val (M.take (M.length - 1)) tN) (hot : isOT tN = true) : tA = app tN one := by
  classical
  obtain ⟨ρ, rk, hC, hR, rfl⟩ := hA
  obtain ⟨ρ', rk', hC', hR', rfl⟩ := hN
  have hpos : 0 < M.length := List.length_pos_of_ne_nil hne
  set x := M.length - 1 with hxdef
  have hkl : x < M.length := by omega
  have hlen : (M.take x).length = x := by rw [List.length_take]; omega
  have hag := take_root_agree hz hkl hC hC' hR'
  set f : Nat → T := fun i => if col M i = (0, 0, 0) then ρ.o i else z with hf
  have hroot' : root (M.take x) ρ' = sumN ((List.range x).map f) := by
    unfold root
    rw [hlen]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hik := List.mem_range.mp hi
    rw [col_take M hik, (hag i hik).1]
  have hroot : root M ρ = sumN ((List.range (x + 1)).map f) := by
    unfold root; rw [show M.length = x + 1 by omega]
  have hox : ρ.o x = one := by
    obtain ⟨ho, hv⟩ := hC x hkl
    have he : entry M 1 x = 0 := by
      have : col M x = M.getD x (0, 0, 0) := rfl
      simp only [entry]
      rw [← this, hz]; rfl
    have hvz : ρ.v x = z := by rw [hv]; simp [vRhs, he]
    rw [ho]
    unfold oRhs
    rw [hvz, children_last (show x + 1 = M.length by omega)]
    rfl
  have hfx : f x = one := by simp only [hf]; rw [if_pos hz, hox]
  rw [hroot, List.range_succ, List.map_append, List.map_singleton, sumN_snoc, hfx,
    add_one_eq_app, ← hroot']
  exact sf_ot (isOT_succ hot)

/-- `EvalFS` restricted to a nonzero last column (the zero case is `val_zero_last`). -/
def EvalFSNZ (c : Nat) : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) →
    ∀ tA, Val A tA → ∀ k tN, Val (expand A (k + c)) tN → fs tA (natT k) ≤ tN

theorem evalFSNZ_of {c : Nat} (h : EvalFS c) : EvalFSNZ c :=
  fun A hA hS hE _ => h A hA hS hE

/-- The weakest form: every `tA[k]` is reached by some expansion (nonzero last column). -/
def EvalFSE : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) →
    ∀ tA, Val A tA → ∀ k, ∃ n tN, Val (expand A n) tN ∧ fs tA (natT k) ≤ tN

theorem evalFSE_of_NZ {c : Nat} (hD : Desc3) (hF : EvalFSNZ c) : EvalFSE := by
  intro A hA hAS hAE hz tA hv k
  obtain ⟨_, tN, _, hvN, _, _⟩ := hD A (k + c) hA hAS hAE
  exact ⟨k + c, tN, hvN, hF A hA hAS hAE hz tA hv k tN hvN⟩

/-- **EvalCof from step 1 and `EvalFSE`.** -/
theorem evalCof_of_E (hD : Desc3) (hF : EvalFSE) : EvalCof := by
  intro A hA hAS hAE tA t hv hot hlt
  obtain ⟨tA', tN0, hv', hvN0, hAot, _⟩ := hD A 0 hA hAS hAE
  cases val_unique hv hv'
  by_cases hz : col A (A.length - 1) = (0, 0, 0)
  · -- the value is `tN0 + 1`
    have hN0ot : isOT tN0 = true := by
      by_cases hE : expand A 0 = []
      · rw [hE] at hvN0; rw [val_unique hvN0 val_nil]; rfl
      · have hst : Step' (expand A 0) A := ⟨hA, hAE, 0, rfl⟩
        obtain ⟨t1, _, h1, _, hot1, _⟩ := hD (expand A 0) 0 (Std.exp 0 hA) (step_ne_sro hD hst) hE
        rw [val_unique hvN0 h1]; exact hot1
    have hvN0' : Val (A.take (A.length - 1)) tN0 := by
      rw [← expand_zero_last hAE hz 0]; exact hvN0
    have heq := val_zero_last hAE hz hv hvN0' hN0ot
    rw [heq] at hlt
    exact ⟨0, tN0, hvN0, le_of_lt_app_one _ hlt⟩
  · have hne : tA ≠ z := by rintro rfl; exact T.not_lt_z _ hlt
    have hle : ∃ k, t ≤ fs tA (natT k) := by
      rcases cof_of_lt_Om1 tA hAot (val_lt_Om1 hv) hne with hc | hc
      · exact ⟨0, le_fs_of_cof_succ hc hlt _⟩
      · obtain ⟨k, hk⟩ := fs_cof_omega tA hAot hc t hot hlt
        exact ⟨k, Or.inl hk⟩
    obtain ⟨k, hk⟩ := hle
    obtain ⟨n, tN, hvN, hkN⟩ := hF A hA hAS hAE hz tA hv k
    exact ⟨n, tN, hvN, le_trans hk hkN⟩

/-- **EvalCof from step 1 and `EvalFSNZ c`** (nonzero last column only). -/
theorem evalCof_of_NZ {c : Nat} (hD : Desc3) (hF : EvalFSNZ c) : EvalCof :=
  evalCof_of_E hD (evalFSE_of_NZ hD hF)

/-- **Surjectivity** from step 1 and `EvalFSNZ c`. -/
theorem surj_of_evalFSNZ {c : Nat} (hD : Desc3) (hF : EvalFSNZ c) {t : T}
    (hot : isOT t = true) {n : Nat} {tN : T} (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  surj hD (evalCof_of_NZ hD hF) hot hvN hlt

/-- **Surjectivity** from step 1 and `EvalFS c`. -/
theorem surj_of_evalFS {c : Nat} (hD : Desc3) (hF : EvalFS c) {t : T}
    (hot : isOT t = true) {n : Nat} {tN : T} (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  surj hD (evalCof_of_evalFS hD hF) hot hvN hlt

end Ytosk
