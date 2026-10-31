/-
**H7WSib を Bad2 のない構造の主張に（2026-10-31, WfH7W2）。**

H7WSib（t = 0 の Bad2 の消える尾の枠で、x − 1 の直前の兄弟 c は x − 1 と同じ列・同じ上げ先）は、Bad2 なしでは偽
（接ぎ木の標準形）。偽の枠はすべて m = P₁(x − 1) の行 1 が 0（v(m) = 0）だった。Bad2 はこれを除く:
Bad2 の枠では強い吸収 UpgAbsX が x で破れるので v(m) に加数があり、m の行 1 は 0 でない（`e1m_of_bad2`）。

残りは値を含まない構造の主張 `SibM`: bump 子 r の隣り合う子 c, n で、n が祖先 k < n へ上げ、
m = P₁ n の行 1 が 0 でないなら、col c = col n かつ upg c = upg n。

- `SibM`（残り、構造のみ、Bad2 なし・位置は任意）
- `e1m_of_bad2`: Bad2 の消える尾の枠で m の行 1 は 0 でない
- `h7wSib_of_sibM : SibM → WfH7W.H7WSib`
-/
import Ytosk.WfH7WSib

namespace Ytosk.WfH7W2

open T

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **Residual (structural, every standard matrix)**: adjacent children `c, n` of a bump child `r`, where `n`
upgrades to an ancestor `k < n` and `m = P₁ n` has row 1 nonzero, have the same column and the same upgrade. -/
def SibM : Prop :=
  ∀ M, Std M → M ≠ SRO → ∀ g r, r ∈ children M g → col M r = bump M g →
    ∀ K0 K1 c n, children M r = K0 ++ c :: n :: K1 → ∀ k, upg M n = some k → k < n →
    ∀ m, par M 1 n = some m → entry M 1 m ≠ 0 →
      col M c = col M n ∧ upg M c = upg M n

/-- In the `t = 0` lost-tail frame of a `Bad2` matrix (`x` a child of `r ≠ x − 1`), the row-1 parent `m` of
`x − 1` has row 1 nonzero: the strong absorption `UpgAbsX` fails at `x`, so `v(m)` has a summand. -/
theorem e1m_of_bad2 {M : Mat} (hB : Bad2 M) {x r : Nat} (hx : x + 1 = M.length) (hxr : par M 0 x = some r)
    (hr : r ≠ x - 1) {m : Nat} (hm : par M 1 (x - 1) = some m) : entry M 1 m ≠ 0 := by
  obtain ⟨_, p, g, _, _, _, hcase⟩ := hB
  have hx1 : M.length - 1 = x := by omega
  have hx2 : M.length - 2 = x - 1 := by omega
  rw [hx1, hx2] at hcase
  rcases hcase with ⟨_, ρ, hC, hU⟩ | ⟨hpx, _⟩
  · intro h0
    apply hU
    intro i k W hi _ _ _ s hs _
    have hi' : i = x - 1 := by omega
    subst hi'
    rw [hm] at hs
    have hmN : m < M.length := by have := par_lt M 1 (x - 1) m hm; omega
    simp only [vOpt] at hs
    rw [v_z_of_e1 hC hmN h0] at hs
    simp [summands] at hs
  · rw [hxr] at hpx
    exact absurd (Option.some.inj hpx) hr

/-- **`H7WSib` from the structural `SibM`.** -/
theorem h7wSib_of_sibM (h : SibM) : WfH7W.H7WSib := by
  intro M hM hS hB x hx he1 g r hr hrb h1g h2g hxr K0 c k hK hu hk
  have S := sInv_std hM hS
  have hfull : children M r = K0 ++ c :: (x - 1) :: [x] := by
    rw [children_split_x hx hxr, ← children_take, hK]
    simp
  obtain ⟨m, hm, _⟩ := upg_target_par0 S.r0p hu
  have hrn : r ≠ x - 1 := by
    intro hrn
    have hmem : x - 1 ∈ children M r := by rw [hfull]; simp
    have := (mem_children hmem).1
    omega
  exact h M hM hS g r hr hrb K0 [x] c (x - 1) hfull k hu hk m hm
    (e1m_of_bad2 hB hx (mem_children_iff.mp hxr).2 hrn hm)

end Ytosk.WfH7W2
