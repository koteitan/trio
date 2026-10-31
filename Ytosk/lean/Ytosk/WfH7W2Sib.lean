/-
**H7WSib を Bad2 のない構造の主張に（2026-10-31, WfH7W2）。**

H7WSib（t = 0 の Bad2 の消える尾の枠で、x − 1 の直前の兄弟 c は x − 1 と同じ列・同じ上げ先）は、Bad2 なしでは偽
（接ぎ木の標準形）。偽の枠はすべて m = P₁(x − 1) の行 1 が 0（v(m) = 0）だった。Bad2 はこれを除く:
Bad2 の枠では強い吸収 UpgAbsX が x で破れるので v(m) に加数があり、m の行 1 は 0 でない（`e1m_of_bad2`）。

残りは値を含まない構造の主張 `SibM`: bump 子 r の隣り合う子 c, n で、n が祖先 k < n へ上げ、
m = P₁ n の行 1 が 0 でないなら、col c = col n かつ upg c = upg n。

- `SibM`（構造のみ、Bad2 なし・位置は任意）、`h7wSib_of_sibM : SibM → WfH7W.H7WSib`
- `e1m_of_bad2`: Bad2 の消える尾の枠で m の行 1 は 0 でない
- 上げの一致は列の一致から出る（`upg_eq_of_sib_col`、`upg_of_anc_target` で）。残りは行だけの `SibMCol`
  （col c = col n）: `h7wSib_of_col : SibMCol → WfH7W.H7WSib`
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

/-- **Residual (structural, rows only)**: `SibM` without the upgrade, which follows (`sibM_of_col`). -/
def SibMCol : Prop :=
  ∀ M, Std M → M ≠ SRO → ∀ g r, r ∈ children M g → col M r = bump M g →
    ∀ K0 K1 c n, children M r = K0 ++ c :: n :: K1 → ∀ k, upg M n = some k → k < n →
    ∀ m, par M 1 n = some m → entry M 1 m ≠ 0 → col M c = col M n

/-- An earlier sibling with the same column upgrades to the same ancestor target. -/
theorem upg_eq_of_sib_col {M : Mat} (S : SInv M) {r c n k : Nat} (hpc : par M 0 c = some r)
    (hpn : par M 0 n = some r) (hcn : c < n) (hcol : col M c = col M n) (hu : upg M n = some k)
    (hk : k < n) : upg M c = some k := by
  have he1 : entry M 1 c = entry M 1 n := by
    have : (col M c).2.1 = (col M n).2.1 := by rw [hcol]
    simpa [entry, col] using this
  have he2 : entry M 2 c = entry M 2 n := by
    have : (col M c).2.2 = (col M n).2.2 := by rw [hcol]
    simpa [entry, col] using this
  obtain ⟨m, hm, hmk, hcolk, hcase⟩ := upg_spec hu
  have hAkn : Anc0 M k n := by rcases hcase with h | h; omega; exact h.1
  have hnN : n + 1 < M.length := upg_succ_lt hu
  have h12 := upg_e12 hu
  have h2n : entry M 2 n = 0 := by have := S.z2 n; omega
  have hp1 : par M 1 c = some m := by rw [WfH7W.par1_sib hpc hpn he1, hm]
  have hAkr : Anc0 M k r := by
    cases hAkn with
    | refl => omega
    | step hp ha => rw [hpn] at hp; cases hp; exact ha
  have hkr : k ≤ r := hAkr.le
  have hrc : r < c := par_lt M 0 c r hpc
  have hAkc : Anc0 M k c := Anc0.step hpc hAkr
  have hAkc1 : Anc0 M k (c + 1) := anc_between hAkn (c + 1) (by omega) (by omega)
  have hek : entry M 0 k = entry M 0 m + 1 := e0_of_col hcolk
  have hlt := anc0_e0_lt hAkc1 (by omega)
  exact upg_of_anc_target (by omega) (by rw [he1]; exact h12.1) (by rw [he2]; exact h2n) hp1 hmk
    (by rw [hcolk, he1]) hAkc (by omega) (by omega)

theorem sibM_of_col (h : SibMCol) : SibM := by
  intro M hM hS g r hr hrb K0 K1 c n hch k hu hk m hm he1
  have S := sInv_std hM hS
  have hcol := h M hM hS g r hr hrb K0 K1 c n hch k hu hk m hm he1
  have hcM : c ∈ children M r := by rw [hch]; simp
  have hnM : n ∈ children M r := by rw [hch]; simp
  have hcn : c < n := by
    have hs := children_sorted M r
    rw [hch] at hs
    exact (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).1 n (by simp)
  exact ⟨hcol, by rw [upg_eq_of_sib_col S (mem_children_iff.mp hcM).2 (mem_children_iff.mp hnM).2 hcn hcol hu hk, hu]⟩

/-- **`H7WSib` from the row-only `SibMCol`.** -/
theorem h7wSib_of_col (h : SibMCol) : WfH7W.H7WSib := h7wSib_of_sibM (sibM_of_col h)

end Ytosk.WfH7W2
