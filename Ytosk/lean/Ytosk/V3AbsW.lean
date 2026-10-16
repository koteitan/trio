/-
**弱い吸収の仮定 AbsWN（のりしろの v の枠）。**

v(P_1 i) の加数 q のうち、N の新しいのりしろの項 bumpW N σ i に吸収されないもの（¬ q < W′）だけについて
q ◁ bumpW M ρ i を求める。強い形（すべての q ≥ ω²、BumpAbsS）は標準形で偽（drop-fix、ext1 の 22 件）。
`v_bump_lhdW` は V3T0D の v_bump_lhd を弱い仮定にした写し（使うのは v_strong の吸収されない加数だけ）。
落とし（N = M.take x）では drop-fix の BumpAbsC がこの形、展開（N = M[n]）では N 側の残り。
-/
import Ytosk.V3T0D

namespace Ytosk

open T

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! `AbsWN`・`AbsWN.of_strong`・`v_bump_lhdW` は V3T0D に移した（2026-10-17、t0: V3T0D の中の t = 0 の
エンジンで使うため）。名前は変えていない。 -/

end Ytosk
