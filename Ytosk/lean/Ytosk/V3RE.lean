/-
**右端の変化 `RE`（closure、2026-10-11）。**

`RE R new old`: new は old と、右端の道（後ろが 0 でなければ後ろへ、後ろが 0 で引数が 0 でなければ引数へ、
どちらも 0 なら添字へ）の上でだけ違い、道の終わりで old の部分項 b が new の部分項 a に替わる（`R a b`）。
道の上の節点の残りの部分（前の項、添字、引数）は同じ。

使い道:
- t = 2 の種の列の基底: 1 列落とし M → M.take x で、悪い部分の値は M の値の右端の v(x−1) の最後の加数 λ を
  1 に替えたもの（実測 1.4 万件、例外 0）。
- t0 の T0Shape (i): D の連鎖の変化が右端にあること（R は ◁ の下げ）。

この形の主な補題:
- `re_le`: R が `≤` なら new ≤ old。
- `re_app`: 前に項を足しても RE。
-/
import Ytosk.V3PKind
import Ytosk.V3DropV
import Ytosk.TwoRowF

namespace Ytosk

open T

/-- **Change only at the right end**: `RE R new old`. -/
inductive RE (R : T → T → Prop) : T → T → Prop
  | base {a b : T} : R a b → RE R a b
  | rest {s y c c' : T} : c ≠ z → RE R c' c → RE R (psi s y c') (psi s y c)
  | arg {s y y' : T} : y ≠ z → RE R y' y → RE R (psi s y' z) (psi s y z)
  | sub {s s' : T} : RE R s' s → RE R (psi s' z z) (psi s z z)

namespace RE

variable {R : T → T → Prop}

theorem refl_of (hR : ∀ t, R t t) (t : T) : RE R t t := base (hR t)

/-- **The new value is at most the old** when the base change lowers. -/
theorem le (hR : ∀ a b, R a b → a ≤ b) : ∀ {a b : T}, RE R a b → a ≤ b
  | _, _, base h => hR _ _ h
  | _, _, rest (s := s) (y := y) _ h => by
    rcases (le_iff _ _).mp (RE.le hR h) with h' | h'
    · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inr ⟨rfl, rfl, h'⟩))
    · rw [h']
  | _, _, arg (s := s) _ h => by
    rcases (le_iff _ _).mp (RE.le hR h) with h' | h'
    · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inr (Or.inl ⟨rfl, h'⟩))
    · rw [h']
  | _, _, sub h => by
    rcases (le_iff _ _).mp (RE.le hR h) with h' | h'
    · exact le_of_lt (by rw [T.psi_lt_psi]; exact Or.inl h')
    · rw [h']

/-- **Summands in front.** -/
theorem app_left (P : T) : ∀ {a b : T}, b ≠ z → RE R a b → RE R (app P a) (app P b) := by
  intro a b hb h
  induction P with
  | z => simpa using h
  | psi s y P _ _ ih =>
    simp only [app_psi]
    exact rest (by cases P <;> simp [app, hb]) ih

end RE

/-! ## sp の 1 段 -/

section
variable {R : T → T → Prop}

/-- **A child whose argument is `0` changes its subscript**: no rewrite either way, the step appends. -/
theorem re_step_leaf (a B : T) {s s' : T} (h : RE R s' s)
    (hB : ∀ q ∈ summands B, psi s z z ≤ q) (hB' : ∀ q ∈ summands B, psi s' z z ≤ q) :
    RE R (step a B s' z z) (step a B s z z) := by
  rw [step_leaf, step_leaf, add_eq_app_of_ge ⟨s, z, rfl⟩ B hB, add_eq_app_of_ge ⟨s', z, rfl⟩ B hB']
  exact RE.app_left B (by simp) (RE.sub h)

/-- **No rewrite on either side**: the step appends the child. -/
theorem re_step_norw (a B s : T) {y y' : T} (hy : y ≠ z) (h : RE R y' y)
    (hn : ¬ (lt B y = true ∧ lt (psi a z z) (psi s y z) = true))
    (hn' : ¬ (lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true))
    (hB : ∀ q ∈ summands B, psi s y z ≤ q) (hB' : ∀ q ∈ summands B, psi s y' z ≤ q) :
    RE R (step a B s y' z) (step a B s y z) := by
  unfold step
  rw [if_neg hn, if_neg hn', add_eq_app_of_ge ⟨s, y, rfl⟩ B hB, add_eq_app_of_ge ⟨s, y', rfl⟩ B hB']
  exact RE.app_left B (by simp) (RE.arg hy h)

/-- **`H` keeps `RE`** when the change stays in the low part (the high part is the same and both low parts are
nonzero) or both arguments are all high. -/
theorem re_H {s y y' : T} (hc : isOT (psi s y z) = true) (hc' : isOT (psi s y' z) = true) (hy : y ≠ z)
    (h : RE R y' y)
    (hcls : ((split y (psi (succ s) z z)).2 = z ∧ (split y' (psi (succ s) z z)).2 = z) ∨
      ((split y' (psi (succ s) z z)).1 = (split y (psi (succ s) z z)).1 ∧
        (split y (psi (succ s) z z)).2 ≠ z ∧ (split y' (psi (succ s) z z)).2 ≠ z)) :
    RE R (H s y') (H s y) := by
  rw [H_eq hc, H_eq hc']
  rcases hcls with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · rw [if_pos h1, if_pos h2, app_z_right, app_z_right]
    have e := split_app (psi (succ s) z z) y
    have e' := split_app (psi (succ s) z z) y'
    rw [h1, app_z_right] at e; rw [h2, app_z_right] at e'
    rw [e, e']; exact h
  · rw [if_neg h2, if_neg h3, h1]
    exact RE.app_left _ (by simp) (RE.arg hy h)

/-- **Both rewrite**: the step is `H`. -/
theorem re_step_rw (a B s : T) {y y' : T} (hc : isOT (psi s y z) = true) (hc' : isOT (psi s y' z) = true)
    (hy : y ≠ z) (h : RE R y' y)
    (ht : lt B y = true ∧ lt (psi a z z) (psi s y z) = true)
    (ht' : lt B y' = true ∧ lt (psi a z z) (psi s y' z) = true)
    (hcls : ((split y (psi (succ s) z z)).2 = z ∧ (split y' (psi (succ s) z z)).2 = z) ∨
      ((split y' (psi (succ s) z z)).1 = (split y (psi (succ s) z z)).1 ∧
        (split y (psi (succ s) z z)).2 ≠ z ∧ (split y' (psi (succ s) z z)).2 ≠ z)) :
    RE R (step a B s y' z) (step a B s y z) := by
  unfold step
  rw [if_pos ht, if_pos ht']
  exact re_H hc hc' hy h hcls

end

end Ytosk
