/-
**t = 0 の弱い吸収 T0AbsW を、落とし側の AbsWN と bumpW の単調性に分ける（2026-10-17、t0）。**

AbsWN M N bnd ρ σ の前件「q は bumpW N σ i に吸収されない」は、bumpW N′ σ′ i ≤ bumpW N σ i なら N′ でも立つ
（`absWN_mono`）。t = 0 では N′ = M.take x（落とし）、N = M[n]（展開）。
- 落とし側: AbsWN M (M.take x) r ρ τ（drop の BumpAbsW の筋）。
- 展開側: i < r で bumpW (M.take x) τ i ≤ bumpW M[n] σ i（`T0BumpMono`）。測定（tools/probe_abswn_t0.py の mono、
  t0ext の 2 万行列、n = 2, 3）で 154034 件例外 0。なお bumpW M ρ i ≤ bumpW M[n] σ i は偽（18470 件で
  M[n] の方が小さい。x が i ののりしろの子の子のとき）。
-/
import Ytosk.V3T0Inv2S

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- **AbsWN is monotone in the bump term of `N`.** -/
theorem absWN_mono {M N N' : Mat} {bnd : Nat} {ρ σ σ' : Valn} (h : AbsWN M N' bnd ρ σ')
    (hm : ∀ i, i < bnd → bumpW N' σ' i ≤ bumpW N σ i) : AbsWN M N bnd ρ σ := by
  intro i hi h1 h2 q hq hq2 hn hlt
  exact h i hi h1 h2 q hq hq2 (fun h' => hn (lt_of_lt_of_le h' (hm i hi))) hlt

/-- **The monotonicity of the bump term** from `M.take x` to `M[n]` (`t = 0`, columns below `r`). -/
def T0BumpMono (M : Mat) (r L : Nat) : Prop :=
  ∀ τ, Cons (M.take (r + L)) τ → ∀ n, 2 ≤ n → ∀ σ, Cons (TRIO.gexp M r L 0 0 n) σ →
    ∀ i, i < r → bumpW (M.take (r + L)) τ i ≤ bumpW (TRIO.gexp M r L 0 0 n) σ i

/-- **`T0AbsW` from the drop side and the monotonicity.** -/
theorem t0AbsW_of {M : Mat} {r L : Nat} {ρ τ : Valn} (hτ : Cons (M.take (r + L)) τ)
    (hD : AbsWN M (M.take (r + L)) r ρ τ) (hm : T0BumpMono M r L) : T0AbsW M r L ρ :=
  fun n hn σ hσ => absWN_mono hD (hm τ hτ n hn σ hσ)

end Ytosk
