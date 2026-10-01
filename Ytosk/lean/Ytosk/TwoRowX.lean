/-
**1 列落とす補題の道具: 部分項の置き換え。**

落とした行列 M.take x の経路上の値は、o(h) のある位置の部分項 W を W′ に置き換えたものになる
（q では W = x の値・W′ = 0、枠が崩れると W はその枠の子の値）。
W′ が標準形で W′ ◁ W なら、置き換えた全体も標準形で ◁（`posR_ot`、`fsD_seed` と同じ帰納法）。
-/
import Ytosk.TwoRowI

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- `t'` is `t` with the subterm `W` replaced by `W'` at a position reached through sums (`rest`) and
arguments (`arg`). -/
inductive PosR (W W' : T) : T → T → Prop
  | here : PosR W W' W W'
  | rest {a b c d e u : T} : PosR W W' (psi c d e) u → PosR W W' (psi a b (psi c d e)) (psi a b u)
  | arg {a b u : T} : PosR W W' b u → PosR W W' (psi a b z) (psi a u z)

/-- **Replacing a subterm by a standard one below it keeps the term standard and below.** -/
theorem posR_ot {W W' : T} (hW' : isOT W' = true) (hl : Lhd z W' W) :
    ∀ {t t' : T}, PosR W W' t t' → isOT t = true → isOT t' = true ∧ Lhd z t' t := by
  intro t t' hP
  induction hP with
  | here => intro _; exact ⟨hW', hl⟩
  | @rest a b c d e u _ ih =>
    intro hot
    obtain ⟨hu, hlu⟩ := ih (isOT_rest hot)
    refine ⟨?_, by simpa using lhd_app (psi a b z) hlu⟩
    obtain ⟨h1, h2, _, h4, h5⟩ := isOT_psi_iff.mp hot
    rw [isOT_psi_iff]
    exact ⟨h1, h2, hu, le_trans (head_le_of_lt hlu.1) h4, h5⟩
  | @arg a b u _ ih =>
    intro hot
    obtain ⟨hu, hlu⟩ := ih (isOT_arg hot)
    refine ⟨?_, lhd_psi a hlu⟩
    apply psi_ot_of_lhd (isOT_sub hot) hu hlu (comps_lt hot)
    intro _ g hg; simp [comps] at hg

theorem PosR.trans {W W' t t' s : T} (h1 : PosR W W' t t') (h2 : PosR t t' s s')
    : PosR W W' s s' := by
  induction h2 with
  | here => exact h1
  | rest _ ih => exact PosR.rest ih
  | arg _ ih => exact PosR.arg ih

end Ytosk
