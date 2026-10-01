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

/-! ## 補題 3.6: t[η] ◁_η t -/

theorem between_sub {a' a c : T} (h1 : psi a' z z < c) (h2 : c ≤ psi a z z) :
    ∃ v c0 c1, c = psi v c0 c1 ∧ a' ≤ v ∧ v ≤ a := by
  cases c with
  | z => exact absurd h1 (T.not_lt_z _)
  | psi v c0 c1 =>
    refine ⟨v, c0, c1, rfl, ?_, ?_⟩
    · rw [T.psi_lt_psi] at h1
      rcases h1 with h | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
      · exact le_of_lt h
      · exact le_refl _
      · exact le_refl _
    · rcases (le_iff _ _).mp h2 with h | h
      · rw [T.psi_lt_psi] at h
        rcases h with h | ⟨rfl, h⟩ | ⟨rfl, _, h⟩
        · exact le_of_lt h
        · exact absurd h (T.not_lt_z _)
        · exact absurd h (T.not_lt_z _)
      · simp only [psi.injEq] at h; rw [h.1]

theorem comps_mulT {u x : T} : ∀ n, ∀ g ∈ comps u (mulT x n), g ∈ comps u x
  | 0, g, h => by simp [mulT, comps] at h
  | n + 1, g, h => by
    simp only [mulT] at h
    rw [comps_app, List.mem_append] at h
    rcases h with h | h
    · exact h
    · exact comps_mulT n g h

theorem lhd_zero {η a : T} (ha : a ≠ z) : Lhd η z a := by
  refine ⟨?_, fun u c _ _ x hx => by simp [comps] at hx⟩
  cases a with | z => exact absurd rfl ha | psi => exact T.z_lt_psi _ _ _

theorem lhd_mulT {η a b' : T} : ∀ n, Lhd η (mulT (psi a b' z) n) (psi a (app b' one) z)
  | 0 => lhd_zero (by simp)
  | k + 1 => by
    have hb' : b' < app b' one := by
      have := app_lt_app_left b' (T.z_lt_psi z z z : z < one); simpa using this
    refine ⟨mulT_lt (by simp only [head]; rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, hb'⟩)
      ⟨a, b', rfl⟩ (by simp) (k + 1), fun u c h1 h2 => ?_⟩
    -- the term `c` is `ψ_a(c0) + c1` with `c0 = b'` or `c0 = b' + 1`
    obtain ⟨v, c0, c1, rfl⟩ : ∃ v c0 c1, c = psi v c0 c1 := by
      cases c with
      | z => exact absurd h1 (T.not_lt_z _)
      | psi v c0 c1 => exact ⟨v, c0, c1, rfl⟩
    simp only [mulT, app_psi, app_z] at h1
    rw [T.psi_lt_psi] at h1
    have hva : v = a ∧ b' ≤ c0 ∧ c0 ≤ app b' one := by
      rcases (le_iff _ _).mp h2 with h2 | h2
      · rw [T.psi_lt_psi] at h2
        rcases h1 with h1 | ⟨rfl, h1⟩ | ⟨rfl, rfl, _⟩
        · rcases h2 with h2 | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
          · exact absurd (lt_trans h1 h2) (lt_irrefl _)
          · exact absurd h1 (lt_irrefl _)
          · exact absurd h1 (lt_irrefl _)
        · rcases h2 with h2 | ⟨_, h2⟩ | ⟨_, rfl, _⟩
          · exact absurd h2 (lt_irrefl _)
          · exact ⟨rfl, le_of_lt h1, le_of_lt h2⟩
          · exact ⟨rfl, le_of_lt h1, le_refl _⟩
        · rcases h2 with h2 | ⟨_, h2⟩ | ⟨_, _, h2⟩
          · exact absurd h2 (lt_irrefl _)
          · exact ⟨rfl, le_refl _, le_of_lt h2⟩
          · exact absurd h2 (T.not_lt_z _)
      · simp only [psi.injEq] at h2
        obtain ⟨rfl, rfl, rfl⟩ := h2
        exact ⟨rfl, le_of_lt hb', le_refl _⟩
    obtain ⟨rfl, hc1, hc2⟩ := hva
    have hc0 : c0 = b' ∨ c0 = app b' one := by
      rcases (le_iff _ _).mp hc1 with hc1 | hc1
      · rcases (le_iff _ _).mp hc2 with hc2 | hc2
        · exfalso
          obtain ⟨c0', rfl, h3, h4⟩ := between_app (A := b') (x := z) (y := one) (by simpa using hc1)
            (le_of_lt hc2)
          have h5 : c0' < one := (app_lt_app_left_iff b').mp hc2
          rw [lt_one_iff] at h5; subst h5; exact absurd h3 (lt_irrefl _)
        · exact Or.inr hc2
      · exact Or.inl hc1.symm
    intro x hx
    have hx' := comps_mulT (k + 1) x hx
    simp only [comps, List.mem_append] at hx'
    rcases hx' with hx' | hx'
    · split at hx'
      · simp at hx'
      · rename_i hau
        simp only [List.mem_cons, List.mem_append] at hx'
        rcases hx' with rfl | hx' | hx'
        · exact ⟨c0, List.mem_append_left _ (by simp [comps, hau]), hc1⟩
        · rcases hc0 with rfl | rfl
          · exact ⟨x, List.mem_append_left _ (by simp [comps, hau, hx']), le_refl _⟩
          · exact ⟨x, List.mem_append_left _ (by simp [comps, hau, comps_app, hx']), le_refl _⟩
        · exact ⟨x, List.mem_append_left _ (by simp [comps, hau, hx']), le_refl _⟩
    · simp at hx'

/-! ### 対角化のための補題 -/

theorem prin_le_head {s y : T} (h : psi s z z ≤ y) : psi s z z ≤ head y := by
  cases y with
  | z => exact absurd (lt_of_lt_of_le (T.z_lt_psi s z z) h) (lt_irrefl _)
  | psi s' y' c' =>
    simp only [head]
    rcases (le_iff _ _).mp h with h1 | h1
    · rw [T.psi_lt_psi] at h1
      rw [le_iff, psi_lt_psi_z_iff]
      rcases h1 with h2 | ⟨rfl, h2⟩ | ⟨rfl, rfl, _⟩
      · exact Or.inl (Or.inl h2)
      · exact Or.inl (Or.inr ⟨rfl, h2⟩)
      · exact Or.inr rfl
    · simp only [psi.injEq] at h1; rw [h1.1, ← h1.2.1]

/-- A term of cofinality `Ω_{μ+1}` is at least `Ω_{μ+1}`. -/
theorem om_le : ∀ {t μ : T}, isOT t = true → cof t = .big μ → psi (succ μ) z z ≤ t
  | z, _, _, h => by simp [cof] at h
  | psi a b (psi c d e), μ, hot, h => by
    have h' : cof (psi c d e) = .big μ := by simpa [cof] using h
    exact le_of_lt (lt_of_le_of_lt (om_le (isOT_rest hot) h') (rest_lt hot))
  | psi a b z, μ, hot, h => by
    by_cases hb : b = z
    · subst hb
      by_cases ha : a = z
      · subst ha; simp [cof] at h
      · have hc : cof (psi a z z) = (if isSucc a then Cof.big (init a) else cof a) := by
          simp [cof, ha]
        rw [hc] at h
        by_cases hs : isSucc a = true
        · rw [if_pos hs] at h; cases h
          unfold succ; rw [init_app_one hs]
        · rw [if_neg hs] at h
          have ih := om_le (isOT_sub hot) h
          have h1 : succ μ < a := lt_of_lt_of_le (lt_Om_self _) ih
          exact le_of_lt (by rw [psi_lt_psi_z_iff]; exact Or.inl h1)
    · have hc0 : cof (psi a b z) = (if isSucc b then Cof.omega else match cof b with
            | .big μ => if lt μ a = true then Cof.big μ else Cof.omega
            | c => c) := by simp [cof, hb]
      rw [hc0] at h
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; cases h
      · rw [if_neg hs] at h
        cases hcb : cof b with
        | big ν =>
          rw [hcb] at h; simp only at h
          by_cases hν : lt ν a = true
          · rw [if_pos hν] at h; cases h
            have h1 := succ_le_of_lt hν
            rcases (le_iff _ _).mp h1 with h1 | h1
            · exact le_of_lt (by rw [psi_lt_psi_z_iff]; exact Or.inl h1)
            · rw [h1, le_iff]; left; rw [psi_lt_psi_z_iff]
              exact Or.inr ⟨rfl, lt_of_le_of_ne (z_le b) (Ne.symm hb)⟩
          · rw [if_neg hν] at h; cases h
        | zero => rw [hcb] at h; cases h
        | succ => rw [hcb] at h; cases h
        | omega => rw [hcb] at h; cases h

/-- `η ≤ t[η]` for cofinality `Ω_{μ+1}`. -/
theorem le_fs : ∀ {t μ g : T}, isOT t = true → cof t = .big μ → g < psi (succ μ) z z → g ≤ fs t g
  | z, _, _, _, h, _ => by simp [cof] at h
  | psi a b (psi c d e), μ, g, hot, h, hg => by
    have h' : cof (psi c d e) = .big μ := by simpa [cof] using h
    have h1 := prin_le_head (om_le (isOT_rest hot) h')
    have h2 : head (psi c d e) ≤ psi a b z := (isOT_psi_iff.mp hot).2.2.2.1
    have h3 : g < psi a b z := lt_of_lt_of_le hg (le_trans h1 h2)
    show g ≤ psi a b (fs (psi c d e) g)
    exact le_of_lt (lt_of_lt_of_le h3 (psi_le_psi_rest (z_le _)))
  | psi a b z, μ, g, hot, h, hg => by
    unfold fs
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl]
      by_cases ha : a = z
      · subst ha; simp [cof] at h
      · rw [if_neg ha]
        have hc : cof (psi a z z) = (if isSucc a then Cof.big (init a) else cof a) := by
          simp [cof, ha]
        rw [hc] at h
        by_cases hs : isSucc a = true
        · rw [if_pos hs]
        · rw [if_neg hs]; rw [if_neg hs] at h
          exact le_of_lt (lt_of_le_of_lt (le_fs (isOT_sub hot) h hg) (lt_Om_self _))
    · rw [if_neg hb]
      have hc0 : cof (psi a b z) = (if isSucc b then Cof.omega else match cof b with
            | .big μ => if lt μ a = true then Cof.big μ else Cof.omega
            | c => c) := by simp [cof, hb]
      rw [hc0] at h
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; cases h
      · rw [if_neg hs] at h
        rw [if_neg hs]
        cases hcb : cof b with
        | big ν =>
          rw [hcb] at h; simp only at h ⊢
          by_cases hν : lt ν a = true
          · rw [if_pos hν] at h ⊢; cases h
            have h1 := succ_le_of_lt hν
            have h2 : psi (succ μ) z z ≤ psi a z z := by
              rcases (le_iff _ _).mp h1 with h1 | h1
              · exact le_of_lt (by rw [psi_lt_psi_z_iff]; exact Or.inl h1)
              · rw [h1]
            have h3 : psi a z z ≤ psi a (fs b g) z := by
              rcases (le_iff _ _).mp (z_le (fs b g)) with h4 | h4
              · exact le_of_lt (by rw [psi_lt_psi_z_iff]; exact Or.inr ⟨rfl, h4⟩)
              · rw [← h4]
            exact le_of_lt (lt_of_lt_of_le hg (le_trans h2 h3))
          · rw [if_neg hν] at h; cases h
        | zero => rw [hcb] at h; cases h
        | succ => rw [hcb] at h; cases h
        | omega => rw [hcb] at h; cases h

theorem le_between_app {A x y c : T} (h1 : app A x ≤ c) (h2 : c ≤ app A y) :
    ∃ c0, c = app A c0 ∧ x ≤ c0 ∧ c0 ≤ y := by
  rcases (le_iff _ _).mp h1 with h1 | rfl
  · obtain ⟨c0, h, hx, hy⟩ := between_app h1 h2
    exact ⟨c0, h, le_of_lt hx, hy⟩
  · refine ⟨x, rfl, le_refl _, ?_⟩
    rcases (le_iff _ _).mp h2 with h2 | h2
    · exact le_of_lt ((app_lt_app_left_iff A).mp h2)
    · rcases lt_trichotomy x y with h | rfl | h
      · exact le_of_lt h
      · exact le_refl _
      · have := app_lt_app_left A h; rw [h2] at this; exact absurd this (lt_irrefl _)

theorem le_between_psi {v b0 b c : T} (h1 : psi v b0 z ≤ c) (h2 : c ≤ psi v b z) :
    ∃ c0 c1, c = psi v c0 c1 ∧ b0 ≤ c0 ∧ c0 ≤ b := by
  rcases (le_iff _ _).mp h1 with h1 | rfl
  · exact between_psi h1 h2
  · refine ⟨b0, z, rfl, le_refl _, ?_⟩
    rcases (le_iff _ _).mp h2 with h2 | h2
    · rw [psi_lt_psi_z_iff] at h2
      rcases h2 with h2 | ⟨_, h2⟩
      · exact absurd h2 (lt_irrefl _)
      · exact le_of_lt h2
    · simp only [psi.injEq] at h2; rw [h2.2.1]

theorem le_between_sub {a' a c : T} (h1 : psi a' z z ≤ c) (h2 : c ≤ psi a z z) :
    ∃ v c0 c1, c = psi v c0 c1 ∧ a' ≤ v ∧ v ≤ a := by
  rcases (le_iff _ _).mp h1 with h1 | rfl
  · exact between_sub h1 h2
  · refine ⟨a', z, z, rfl, le_refl _, ?_⟩
    rcases (le_iff _ _).mp h2 with h2 | h2
    · rw [psi_lt_psi_z_iff] at h2
      rcases h2 with h2 | ⟨_, h2⟩
      · exact le_of_lt h2
      · exact absurd h2 (T.not_lt_z _)
    · simp only [psi.injEq] at h2; rw [h2.1]

theorem mem_comps_psi_of {u v w r y : T} (hv : ¬ lt v u = true) (hy : y ∈ comps u v) :
    y ∈ comps u (psi v w r) := by
  simp [comps, hv, hy]

theorem mem_comps_psi_arg {u v w r y : T} (hv : ¬ lt v u = true) (hy : y ∈ comps u w) :
    y ∈ comps u (psi v w r) := by
  simp [comps, hv, hy]

/-- **The subscript of the cofinality** stays among the components between `b[g]` and `b`. -/
theorem comps_mu {u : T} : ∀ {b μ g c0 : T}, isOT b = true → cof b = .big μ →
    psi μ z z ≤ g → g < psi (succ μ) z z → fs b g ≤ c0 → c0 ≤ b → ¬ lt μ u = true →
    ∀ y ∈ comps u μ, y ∈ comps u c0
  | z, _, _, _, _, h, _, _, _, _, _ => by simp [cof] at h
  | psi a b (psi c d e), μ, g, c0, hot, h, hg1, hg2, hfs, hc0, hμ => by
    have h' : cof (psi c d e) = .big μ := by simpa [cof] using h
    have hfs' : app (psi a b z) (fs (psi c d e) g) ≤ c0 := by simpa [fs] using hfs
    have hc0' : c0 ≤ app (psi a b z) (psi c d e) := by simpa using hc0
    obtain ⟨c0', rfl, h1, h2⟩ := le_between_app hfs' hc0'
    intro y hy
    have := comps_mu (isOT_rest hot) h' hg1 hg2 h1 h2 hμ y hy
    rw [comps_app]; exact List.mem_append_right _ this
  | psi a b z, μ, g, c0, hot, h, hg1, hg2, hfs, hc0, hμ => by
    unfold fs at hfs
    have hμg : μ < g := lt_of_lt_of_le (lt_Om_self μ) hg1
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl] at hfs
      by_cases ha : a = z
      · subst ha; simp [cof] at h
      · rw [if_neg ha] at hfs
        have hc : cof (psi a z z) = (if isSucc a then Cof.big (init a) else cof a) := by
          simp [cof, ha]
        rw [hc] at h
        by_cases hs : isSucc a = true
        · rw [if_pos hs] at hfs h; cases h
          have hsa : app (init a) one = a := init_app_one hs
          obtain ⟨v, w, r, rfl, hv1, hv2⟩ := le_between_sub (le_trans hg1 hfs) hc0
          have hvu : ¬ lt v u = true := fun hv => hμ (lt_of_le_of_lt hv1 hv)
          have hv : v = init a ∨ v = a := by
            rcases (le_iff _ _).mp hv1 with hv1 | hv1
            · rcases (le_iff _ _).mp hv2 with hv2 | hv2
              · exfalso
                rw [← hsa] at hv2
                obtain ⟨c0', rfl, h3, h4⟩ := between_app (A := init a) (x := z) (y := one)
                  (by simpa using hv1) (le_of_lt hv2)
                have h5 : c0' < one := (app_lt_app_left_iff _).mp hv2
                rw [lt_one_iff] at h5; subst h5; exact absurd h3 (lt_irrefl _)
              · exact Or.inr hv2
            · exact Or.inl hv1.symm
          intro y hy
          apply mem_comps_psi_of hvu
          rcases hv with rfl | rfl
          · exact hy
          · rw [← hsa, comps_app]; exact List.mem_append_left _ hy
        · rw [if_neg hs] at hfs h
          obtain ⟨v, w, r, rfl, hv1, hv2⟩ := le_between_sub hfs hc0
          have hgv : g ≤ v := le_trans (le_fs (isOT_sub hot) h hg2) hv1
          have hvu : ¬ lt v u = true := fun hv => hμ (lt_trans (lt_of_lt_of_le hμg hgv) hv)
          intro y hy
          exact mem_comps_psi_of hvu (comps_mu (isOT_sub hot) h hg1 hg2 hv1 hv2 hμ y hy)
    · rw [if_neg hb] at hfs
      have hc0' : cof (psi a b z) = (if isSucc b then Cof.omega else match cof b with
            | .big μ => if lt μ a = true then Cof.big μ else Cof.omega
            | c => c) := by simp [cof, hb]
      rw [hc0'] at h
      by_cases hs : isSucc b = true
      · rw [if_pos hs] at h; cases h
      · rw [if_neg hs] at h hfs
        cases hcb : cof b with
        | big ν =>
          rw [hcb] at h hfs; simp only at h hfs
          by_cases hν : lt ν a = true
          · rw [if_pos hν] at h hfs; cases h
            obtain ⟨w, r, rfl, hw1, hw2⟩ := le_between_psi hfs hc0
            have hau : ¬ lt a u = true := fun hau => hμ (show μ < u from lt_trans (show μ < a from hν) hau)
            intro y hy
            exact mem_comps_psi_arg hau (comps_mu (isOT_arg hot) hcb hg1 hg2 hw1 hw2 hμ y hy)
          · rw [if_neg hν] at h; cases h
        | zero => rw [hcb] at h; cases h
        | succ => rw [hcb] at h; cases h
        | omega => rw [hcb] at h; cases h

/-- **Lemma 3.6.** -/
theorem lhd_fs : ∀ {t η : T}, ValidLt t η → Lhd η (fs t η) t
  | z, η, h => by simp [ValidLt, cof] at h
  | psi a b (psi c d e), η, h => by
    have h' : ValidLt (psi c d e) η := by simpa [ValidLt, cof] using h
    have := lhd_app (psi a b z) (lhd_fs h')
    simpa using this
  | psi a b z, η, h => by
    unfold ValidLt at h
    unfold fs
    by_cases hb : b = z
    · subst hb
      rw [if_pos rfl]
      by_cases ha : a = z
      · subst ha; exact lhd_zero (by simp)
      · rw [if_neg ha]
        have hc : cof (psi a z z) = (if isSucc a then Cof.big (init a) else cof a) := by
          simp [cof, ha]
        rw [hc] at h
        by_cases hs : isSucc a = true
        · rw [if_pos hs]
          rw [if_pos hs] at h
          have h' : η < psi (succ (init a)) z z := h
          unfold succ at h'
          rw [init_app_one hs] at h'
          refine ⟨h', fun u c _ _ x hx => ⟨x, List.mem_append_right _ (List.mem_cons_of_mem _ hx), le_refl _⟩⟩
        · rw [if_neg hs]
          rw [if_neg hs] at h
          have ih := lhd_fs (t := a) h
          refine ⟨by rw [psi_lt_psi_z_iff]; exact Or.inl ih.1, fun u c h1 h2 => ?_⟩
          obtain ⟨v, c0, c1, rfl, hv1, hv2⟩ := between_sub h1 h2
          intro x hx
          simp only [comps, List.mem_append] at hx
          rcases hx with hx | hx
          · split at hx
            · simp at hx
            · rename_i hau
              have hvu : ¬ lt v u = true := fun h => hau (lt_of_le_of_lt hv1 h)
              simp only [List.mem_cons, List.mem_append] at hx
              rcases hx with rfl | hx | hx
              · exact ⟨z, List.mem_append_right _ (List.mem_cons_self), le_refl _⟩
              · simp [comps] at hx
              · rcases (le_iff _ _).mp hv1 with hv1 | rfl
                · obtain ⟨y, hy, hxy⟩ := ih.2 u v hv1 hv2 x hx
                  refine ⟨y, ?_, hxy⟩
                  rcases List.mem_append.mp hy with hy | hy
                  · exact List.mem_append_left _ (by simp [comps, hvu, hy])
                  · exact List.mem_append_right _ hy
                · exact ⟨x, List.mem_append_left _ (by simp [comps, hvu, hx]), le_refl _⟩
          · simp [comps] at hx
    · rw [if_neg hb]
      by_cases hs : isSucc b = true
      · rw [if_pos hs]
        have := lhd_mulT (η := η) (a := a) (b' := init b) (count η)
        rwa [init_app_one hs] at this
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
            exact lhd_psi a (lhd_fs h')
          · rw [if_neg hμ]
            sorry
        | zero =>
          rw [hcb] at h; exact absurd h (by simp)
        | succ =>
          have h' : ValidLt b η := by unfold ValidLt; rw [hcb]; rw [hcb] at h; exact h
          simp only
          exact lhd_psi a (lhd_fs h')
        | omega =>
          have h' : ValidLt b η := by unfold ValidLt; rw [hcb]; trivial
          simp only
          exact lhd_psi a (lhd_fs h')

#eval [psi z (psi z one z) z, psi z (psi (psi one z z) z z) z].map fun t =>
  ((List.range 3).map fun n => str (fs t (natT n)))

end Ytosk
