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

/-- `G°_u η`: the index and its components. -/
def Gc (u η : T) : List T := η :: comps u η

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

#eval [psi z (psi z one z) z, psi z (psi (psi one z z) z z) z].map fun t =>
  ((List.range 3).map fun n => str (fs t (natT n)))

end Ytosk
