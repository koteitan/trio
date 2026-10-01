/-
**拡張 Buchholz の項の基本列（Denis 氏の規則、対角化の始点 γ[0] = 0）。**

googology wiki "Extended Buchholz's function" の基本列。共終数は 0・後続・ω・Ω_{μ+1} の 4 種類。
対角化（ψ_ν(β)、β の共終数が Ω_{μ+1}、μ ≥ ν）は γ[0] = 0、γ[k+1] = ψ_μ(β[γ[k]]) から始める（BM4 の展開に合う版、
`tools/ebocf_fs.py` の `G0 = "zero"`）。

目標: 標準形 t について t[η] は標準形で t[η] < t（乱択の 22,460 項・61,791 回で例外なし）。
-/
import Ytosk.SP

namespace Ytosk

open T

/-- All summands but the last. -/
def init : T → T
  | z => z
  | psi _ _ z => z
  | psi a b c => psi a b (init c)

/-- The number of summands. -/
def count : T → Nat
  | z => 0
  | psi _ _ c => count c + 1

/-- The finite ordinal `n = 1 + ... + 1`. -/
def natT : Nat → T
  | 0 => z
  | n + 1 => psi z z (natT n)

/-- `t` is a successor: its last summand is `1`. -/
def isSucc (t : T) : Bool := last t == one

/-- Cofinality: `0`, successor, `ω`, or `Ω_{μ+1}` (stored as `μ`). -/
inductive Cof where
  | zero | succ | omega | big (μ : T)
  deriving DecidableEq

/-- The cofinality of a term (by its last summand). -/
def cof : T → Cof
  | z => .zero
  | psi a b (psi c d e) => cof (psi c d e)
  | psi a b z =>
    if b = z then
      (if a = z then .succ else if isSucc a then .big (init a) else cof a)
    else if isSucc b then .omega
    else match cof b with
      | .big μ => if lt μ a then .big μ else .omega
      | c => c

/-- `ψ_ν(β) · n`. -/
def mulT (t : T) : Nat → T
  | 0 => z
  | n + 1 => app t (mulT t n)

/-- The fundamental sequence `t[η]` (for cofinality `ω` the index is `count η`). -/
def fs : T → T → T
  | z, _ => z
  | psi a b (psi c d e), η => psi a b (fs (psi c d e) η)
  | psi a b z, η =>
    if b = z then
      (if a = z then z else if isSucc a then η else psi (fs a η) z z)
    else if isSucc b then mulT (psi a (init b) z) (count η)
    else match cof b with
      | .big μ =>
        if lt μ a then psi a (fs b η) z
        else psi a (fs b (Nat.rec z (fun _ g => psi μ (fs b g) z) (count η))) z
      | _ => psi a (fs b η) z

/-! ## Buchholz の関係 ◁ -/

/-- Every element of `X` is at most some element of `Y`. -/
def Dom (X Y : List T) : Prop := ∀ x ∈ X, ∃ y ∈ Y, x ≤ y

/-- `G°_u η`: `0` and the components of the index. -/
def Gc (u η : T) : List T := z :: comps u η

/-- `b ◁_η a` (Buchholz 1986, before Lemma 3.4). -/
def Lhd (η b a : T) : Prop :=
  b < a ∧ ∀ u c, b < c → c ≤ a → Dom (comps u b) (comps u c ++ Gc u η)

theorem size_comps : ∀ {u t g : T}, g ∈ comps u t → size g < size t
  | _, z, _, h => by simp [comps] at h
  | u, psi v x c, g, h => by
    simp only [comps, List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp at h
      · simp only [List.mem_cons, List.mem_append] at h
        rcases h with rfl | h | h
        · exact size_arg_lt _ _ _
        · exact Nat.lt_trans (size_comps h) (size_arg_lt _ _ _)
        · exact Nat.lt_trans (size_comps h) (size_sub_lt _ _ _)
    · exact Nat.lt_trans (size_comps h) (size_rest_lt _ _ _)

/-- Components of a component are components. -/
theorem comps_trans : ∀ {u t g : T}, g ∈ comps u t → ∀ h ∈ comps u g, h ∈ comps u t
  | _, z, _, hg => by simp [comps] at hg
  | u, psi v x c, g, hg => by
    intro h hh
    simp only [comps, List.mem_append] at hg ⊢
    rcases hg with hg | hg
    · left
      split at hg
      · simp at hg
      · rename_i hvu
        rw [if_neg hvu]
        simp only [List.mem_cons, List.mem_append] at hg ⊢
        rcases hg with rfl | hg | hg
        · exact Or.inr (Or.inl hh)
        · exact Or.inr (Or.inl (comps_trans hg h hh))
        · exact Or.inr (Or.inr (comps_trans hg h hh))
    · exact Or.inr (comps_trans hg h hh)

/-- **Lemma 3.4.** -/
theorem lhd_comps {η b a u : T} (hl : Lhd η b a) (ha : ∀ g ∈ comps u a, g < a)
    (hη : ∀ g ∈ Gc u η, g < b) : ∀ g ∈ comps u b, g < b := by
  have key : ∀ n, ∀ g, size g = n → g ∈ comps u b → g < b := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro g hgn hg
      rcases lt_or_ge g b with hlt | hge
      · exact hlt
      · exfalso
        have hga : g < a := by
          obtain ⟨y, hy, hgy⟩ := hl.2 u a hl.1 (le_refl _) g hg
          rcases List.mem_append.mp hy with hy | hy
          · exact lt_of_le_of_lt hgy (ha y hy)
          · exact lt_of_le_of_lt hgy (lt_trans (hη y hy) hl.1)
        have hne : g ≠ b := by
          intro h; have := size_comps hg; rw [h] at this; exact Nat.lt_irrefl _ this
        have hbg : b < g := lt_of_le_of_ne hge (Ne.symm hne)
        obtain ⟨y, hy, hgy⟩ := hl.2 u g hbg (le_of_lt hga) g hg
        rcases List.mem_append.mp hy with hy | hy
        · have hsz : size y < n := hgn ▸ size_comps hy
          have := ih (size y) hsz y rfl (comps_trans hg y hy)
          exact absurd (lt_of_le_of_lt hgy this) (not_lt_of_ge hge)
        · exact absurd (lt_of_le_of_lt hgy (hη y hy)) (not_lt_of_ge hge)
  intro g hg
  exact key (size g) g rfl hg

theorem app_lt_app_left_iff : ∀ (p : T) {y y' : T}, app p y < app p y' ↔ y < y'
  | z, _, _ => by simp
  | psi a b c, y, y' => by
    simp only [app_psi]
    rw [T.psi_lt_psi, app_lt_app_left_iff c]
    constructor
    · rintro (h | ⟨_, h⟩ | ⟨_, _, h⟩)
      · exact absurd h (lt_irrefl _)
      · exact absurd h (lt_irrefl _)
      · exact h
    · intro h; exact Or.inr (Or.inr ⟨rfl, rfl, h⟩)

/-- A term between `A ++ x` and `A ++ y` starts with `A`. -/
theorem between_app : ∀ {A x y c : T}, app A x < c → c ≤ app A y →
    ∃ c0, c = app A c0 ∧ x < c0 ∧ c0 ≤ y
  | z, x, y, c, h1, h2 => ⟨c, by simp, by simpa using h1, by simpa using h2⟩
  | psi a1 b1 A', x, y, c, h1, h2 => by
    simp only [app_psi] at h1 h2
    cases c with
    | z => exact absurd h1 (T.not_lt_z _)
    | psi a2 b2 c' =>
      rw [T.psi_lt_psi] at h1
      rcases (le_iff _ _).mp h2 with h2 | h2
      · rw [T.psi_lt_psi] at h2
        rcases h1 with h1 | ⟨rfl, h1⟩ | ⟨rfl, rfl, h1⟩
        · rcases h2 with h2 | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
          · exact absurd (lt_trans h1 h2) (lt_irrefl _)
          · exact absurd h1 (lt_irrefl _)
          · exact absurd h1 (lt_irrefl _)
        · rcases h2 with h2 | ⟨_, h2⟩ | ⟨_, rfl, _⟩
          · exact absurd h2 (lt_irrefl _)
          · exact absurd (lt_trans h1 h2) (lt_irrefl _)
          · exact absurd h1 (lt_irrefl _)
        · rcases h2 with h2 | ⟨_, h2⟩ | ⟨_, _, h2⟩
          · exact absurd h2 (lt_irrefl _)
          · exact absurd h2 (lt_irrefl _)
          · obtain ⟨c0, hc, hx, hy⟩ := between_app h1 (le_of_lt h2)
            exact ⟨c0, by rw [hc]; rfl, hx, hy⟩
      · simp only [psi.injEq] at h2
        obtain ⟨rfl, rfl, rfl⟩ := h2
        exact ⟨y, rfl, by
          rcases h1 with h1 | ⟨_, h1⟩ | ⟨_, _, h1⟩
          · exact absurd h1 (lt_irrefl _)
          · exact absurd h1 (lt_irrefl _)
          · exact (app_lt_app_left_iff A').mp h1, le_refl _⟩

theorem between_psi {v b0 b c : T} (h1 : psi v b0 z < c) (h2 : c ≤ psi v b z) :
    ∃ c0 c1, c = psi v c0 c1 ∧ b0 ≤ c0 ∧ c0 ≤ b := by
  cases c with
  | z => exact absurd h1 (T.not_lt_z _)
  | psi a2 b2 c' =>
    rw [T.psi_lt_psi] at h1
    rcases (le_iff _ _).mp h2 with h2 | h2
    · rw [T.psi_lt_psi] at h2
      rcases h1 with h1 | ⟨rfl, h1⟩ | ⟨rfl, rfl, _⟩
      · rcases h2 with h2 | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
        · exact absurd (lt_trans h1 h2) (lt_irrefl _)
        · exact absurd h1 (lt_irrefl _)
        · exact absurd h1 (lt_irrefl _)
      · rcases h2 with h2 | ⟨_, h2⟩ | ⟨_, rfl, _⟩
        · exact absurd h2 (lt_irrefl _)
        · exact ⟨b2, c', rfl, le_of_lt h1, le_of_lt h2⟩
        · exact ⟨_, c', rfl, le_of_lt h1, le_refl _⟩
      · rcases h2 with h2 | ⟨_, h2⟩ | ⟨_, _, h2⟩
        · exact absurd h2 (lt_irrefl _)
        · exact ⟨b0, c', rfl, le_refl _, le_of_lt h2⟩
        · exact absurd h2 (T.not_lt_z _)
    · simp only [psi.injEq] at h2
      obtain ⟨rfl, rfl, rfl⟩ := h2
      exact ⟨_, z, rfl, by
        rcases h1 with h1 | ⟨_, h1⟩ | ⟨_, _, h1⟩
        · exact absurd h1 (lt_irrefl _)
        · exact le_of_lt h1
        · exact absurd h1 (T.not_lt_z _), le_refl _⟩

/-- **Lemma 3.5** (sum). -/
theorem lhd_app {η b0 b : T} (A : T) (h : Lhd η b0 b) : Lhd η (app A b0) (app A b) := by
  refine ⟨app_lt_app_left A h.1, fun u c h1 h2 => ?_⟩
  obtain ⟨c0, rfl, hc1, hc2⟩ := between_app h1 h2
  intro x hx
  rw [comps_app] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact ⟨x, List.mem_append_left _ (by rw [comps_app]; exact List.mem_append_left _ hx), le_refl _⟩
  · obtain ⟨y, hy, hxy⟩ := h.2 u c0 hc1 hc2 x hx
    refine ⟨y, ?_, hxy⟩
    rcases List.mem_append.mp hy with hy | hy
    · exact List.mem_append_left _ (by rw [comps_app]; exact List.mem_append_right _ hy)
    · exact List.mem_append_right _ hy

/-- **Lemma 3.5** (collapse). -/
theorem lhd_psi {η b0 b : T} (v : T) (h : Lhd η b0 b) : Lhd η (psi v b0 z) (psi v b z) := by
  refine ⟨by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h.1⟩, fun u c h1 h2 => ?_⟩
  obtain ⟨c0, c1, rfl, hc1, hc2⟩ := between_psi h1 h2
  intro x hx
  have hsub : ∀ w ∈ comps u (psi v c0 z), w ∈ comps u (psi v c0 c1) := by
    intro w hw; simp only [comps, List.mem_append] at hw ⊢; left; simpa using hw
  rcases (le_iff _ _).mp hc1 with hc1 | rfl
  · simp only [comps, List.mem_append] at hx
    rcases hx with hx | hx
    · split at hx
      · simp at hx
      · rename_i hvu
        simp only [List.mem_cons, List.mem_append] at hx
        rcases hx with rfl | hx | hx
        · exact ⟨c0, List.mem_append_left _ (by simp [comps, hvu]), le_of_lt hc1⟩
        · obtain ⟨y, hy, hxy⟩ := h.2 u c0 hc1 hc2 x hx
          refine ⟨y, ?_, hxy⟩
          rcases List.mem_append.mp hy with hy | hy
          · exact List.mem_append_left _ (by simp [comps, hvu, hy])
          · exact List.mem_append_right _ hy
        · exact ⟨x, List.mem_append_left _ (by simp [comps, hvu, hx]), le_refl _⟩
    · simp [comps] at hx
  · exact ⟨x, List.mem_append_left _ (hsub x hx), le_refl _⟩

/-! ## 補題 3.2: t[η] < t -/

theorem init_app_one : ∀ {a : T}, isSucc a = true → app (init a) one = a
  | z, h => by simp [isSucc, last, one] at h
  | psi x y z, h => by
    simp only [isSucc, last, beq_iff_eq] at h
    rw [h]; rfl
  | psi x y (psi c d e), h => by
    have h' : isSucc (psi c d e) = true := by simpa [isSucc, last] using h
    show psi x y (app (init (psi c d e)) one) = _
    rw [init_app_one h']

theorem init_lt : ∀ {b : T}, b ≠ z → init b < b
  | z, h => absurd rfl h
  | psi x y z, _ => T.z_lt_psi _ _ _
  | psi x y (psi c d e), _ => by
    show psi x y (init (psi c d e)) < psi x y (psi c d e)
    rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, init_lt (by simp)⟩)

theorem mulT_lt {x w : T} (h : head x < head w) (hx : ∃ s y, x = psi s y z) (hw : w ≠ z) :
    ∀ n, mulT x n < w
  | 0 => by cases w with | z => exact absurd rfl hw | psi => exact T.z_lt_psi _ _ _
  | n + 1 => by
    obtain ⟨s, y, rfl⟩ := hx
    cases w with
    | z => exact absurd rfl hw
    | psi a b c =>
      simp only [mulT, app_psi, app_z]
      have h' : psi s y z < psi a b z := by simpa [head] using h
      exact lt_of_head_lt (r := psi s y (mulT (psi s y z) n)) h'

/-- The index is in range, without the standard form. -/
def ValidLt (t η : T) : Prop :=
  match cof t with
  | .zero => False
  | .succ => η = z
  | .omega => True
  | .big μ => η < psi (succ μ) z z

theorem fs_lt : ∀ {t η : T}, ValidLt t η → fs t η < t
  | z, η, h => by simp [ValidLt, cof] at h
  | psi a b (psi c d e), η, h => by
    have h' : ValidLt (psi c d e) η := by simpa [ValidLt, cof] using h
    show psi a b (fs (psi c d e) η) < psi a b (psi c d e)
    rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, fs_lt h'⟩)
  | psi a b z, η, h => by
    unfold ValidLt at h
    unfold fs
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl]
      by_cases ha : a = z
      · subst ha; exact T.z_lt_psi _ _ _
      · rw [if_neg ha]
        have hc : cof (psi a z z) = (if isSucc a then Cof.big (init a) else cof a) := by
          simp [cof, ha]
        rw [hc] at h
        by_cases hs : isSucc a = true
        · rw [if_pos hs]
          rw [if_pos hs] at h
          have h' : η < psi (succ (init a)) z z := h
          unfold succ at h'
          rwa [init_app_one hs] at h'
        · rw [if_neg hs]
          rw [if_neg hs] at h
          rw [psi_lt_psi_z_iff]; exact Or.inl (fs_lt (t := a) h)
    · rw [if_neg hb]
      by_cases hs : isSucc b = true
      · rw [if_pos hs]
        apply mulT_lt _ ⟨a, init b, rfl⟩ (by simp)
        simp only [head]
        rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, init_lt hb⟩
      · rw [if_neg hs]
        have hc : cof (psi a b z) = (match cof b with
            | .big μ => if lt μ a = true then Cof.big μ else Cof.omega
            | c => c) := by simp [cof, hb, hs]
        rw [hc] at h
        cases hcb : cof b with
        | big μ =>
          rw [hcb] at h
          simp only at h ⊢
          by_cases hμ : lt μ a = true
          · rw [if_pos hμ]; rw [if_pos hμ] at h
            have h' : ValidLt b η := by unfold ValidLt; rw [hcb]; exact h
            rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, fs_lt h'⟩
          · rw [if_neg hμ]
            have h' : ValidLt b (Nat.rec z (fun _ g => psi μ (fs b g) z) (count η)) := by
              unfold ValidLt; rw [hcb]
              show _ < psi (succ μ) z z
              cases count η with
              | zero => exact T.z_lt_psi _ _ _
              | succ k =>
                show psi μ _ z < _
                rw [psi_lt_psi_z_iff]; exact Or.inl (lt_succ_self μ)
            rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, fs_lt h'⟩
        | zero =>
          rw [hcb] at h; exact absurd h (by simp)
        | succ =>
          have h' : ValidLt b η := by unfold ValidLt; rw [hcb]; rw [hcb] at h; exact h
          simp only
          rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, fs_lt h'⟩
        | omega =>
          have h' : ValidLt b η := by unfold ValidLt; rw [hcb]; trivial
          simp only
          rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, fs_lt h'⟩

/-- A subscript is below the term. -/
theorem sub_lt_psi : ∀ (s y c : T), s < psi s y c
  | z, _, _ => T.z_lt_psi _ _ _
  | psi s' y' c', y, c => by
    rw [T.psi_lt_psi]; exact Or.inl (sub_lt_psi s' y' c')

theorem lt_Om_self (x : T) : x < psi x z z := by
  cases x with
  | z => exact T.z_lt_psi _ _ _
  | psi s y c => rw [T.psi_lt_psi]; exact Or.inl (sub_lt_psi s y c)

/-- **Lemma 3.2(b)**: for cofinality `Ω_{μ+1}` the fundamental sequence is strictly increasing. -/
theorem fs_mono : ∀ {t : T} {μ : T}, cof t = .big μ → ∀ {η η' : T}, η < η' → fs t η < fs t η'
  | z, _, h, _, _, _ => by simp [cof] at h
  | psi a b (psi c d e), μ, h, η, η', hl => by
    have h' : cof (psi c d e) = .big μ := by simpa [cof] using h
    show psi a b (fs (psi c d e) η) < psi a b (fs (psi c d e) η')
    rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, fs_mono h' hl⟩)
  | psi a b z, μ, h, η, η', hl => by
    unfold fs
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl, if_pos rfl]
      by_cases ha : a = z
      · subst ha; simp [cof] at h
      · rw [if_neg ha, if_neg ha]
        have hc : cof (psi a z z) = (if isSucc a then Cof.big (init a) else cof a) := by
          simp [cof, ha]
        rw [hc] at h
        by_cases hs : isSucc a = true
        · rw [if_pos hs, if_pos hs]; exact hl
        · rw [if_neg hs, if_neg hs]; rw [if_neg hs] at h
          rw [psi_lt_psi_z_iff]; exact Or.inl (fs_mono h hl)
    · rw [if_neg hb, if_neg hb]
      have hc0 : cof (psi a b z) = (if isSucc b then Cof.omega else match cof b with
            | .big μ => if lt μ a = true then Cof.big μ else Cof.omega
            | c => c) := by simp [cof, hb]
      rw [hc0] at h
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; cases h
      · rw [if_neg hs] at h
        rw [if_neg hs, if_neg hs]
        cases hcb : cof b with
        | big ν =>
          rw [hcb] at h; simp only at h ⊢
          by_cases hν : lt ν a = true
          · rw [if_pos hν] at h ⊢; rw [if_pos hν]
            rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, fs_mono hcb hl⟩
          · rw [if_neg hν] at h; cases h
        | zero => rw [hcb] at h; cases h
        | succ => rw [hcb] at h; cases h
        | omega => rw [hcb] at h; cases h

#eval [psi z (psi z one z) z, psi z (psi (psi one z z) z z) z].map fun t =>
  ((List.range 3).map fun n => str (fs t (natT n)))

end Ytosk
