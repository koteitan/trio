/-
**標準形 OT（拡張 Buchholz の項の正規形）。**

ψ_a(b) が標準形なのは、b の「段 a 以上の成分」がすべて b より小さいとき（Buchholz の G_u(b) < b を、
添字が項である拡張版に合わせたもの）。成分 `comps u t` は、t の中の崩壊 ψ_v(x) のうち v ≥ u のものについて、
引数 x とその成分、添字 v の成分を集めたもの。拡張 Buchholz の C_u(α) は ψ_v(ξ) を入れるのに
v, ξ ∈ C_u(α) と ξ < α を要求するので、添字 v の成分も入る。

和は左から大きい順（非増加）に並べる。
-/
import Ytosk.Term

namespace Ytosk

open T

/-- `x ≤ y`. -/
def le (x y : T) : Bool := x == y || lt x y

/-- The components `G_u(t)` of `t` relative to level `u`. -/
def comps (u : T) : T → List T
  | z => []
  | psi v x c => (if lt v u then [] else x :: (comps u x ++ comps u v)) ++ comps u c

/-- Standard form. -/
def isOT : T → Bool
  | z => true
  | psi a b c =>
    isOT a && isOT b && isOT c &&
    (match c with
     | z => true
     | psi a' b' _ => le (psi a' b' z) (psi a b z)) &&
    (comps a b).all (fun g => lt g b)

/-! ## 例 -/

/-- `ψ_0(Ω_1)`（= ε_0）は標準形。 -/
example : isOT (psi z (psi one z z) z) = true := by decide

/-- `ψ_0(ψ_0(Ω_1))` は標準形でない（成分 Ω_1 が引数 ψ_0(Ω_1) より大きい）。 -/
example : isOT (psi z (psi z (psi one z z) z) z) = false := by decide

/-- `ψ_0(Ω_v)` で添字 v = ψ_0(Ω_{Ω_1}) は標準形でない（添字の成分 Ω_{Ω_1} が引数 Ω_v より大きい）。 -/
example : isOT (psi z (psi (psi z (psi (psi one z z) z z) z) z z) z) = false := by decide

end Ytosk
