/-
**H7WTail を構造の残り H7WSib に（2026-10-31, WfH7W）。**

t0 の Bad2 の場面の「失われた最後の葉」の枠（r が g の bump 子、M.take x での r の子が K0 ++ [c, x − 1]、
x − 1 が祖先へ上げる）で、直前の兄弟 c は x − 1 と同じ列で同じ上げ先を持つ（測定: b2grow1 134・b2grow2 128 枠）。
そのとき P₁ c = P₁(x − 1)（祖先の列が同じで行 1 が同じ）なので v(c) = v(x − 1) で、H7WTail は HUACB2 そのもの。

- `H7WSib`（値を含まない構造の残り）: その枠で col c = col(x − 1) ∧ upg c = upg(x − 1)。
- `h7wTail_of : HUACB2 → H7WSib → H7WTail`
- `t0BadSeedsH7W_of_sib : HDropU → HUACB2 → H7WSib → T0BadSeedsH7W`
-/
import Ytosk.WfH7WB2

namespace Ytosk.WfH7W

open T

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **Residual (structural): the preceding sibling of a lost last leaf is a copy of it** (2026-10-31). -/
def H7WSib : Prop :=
  ∀ M, Std M → M ≠ SRO → Bad2 M → ∀ x, x + 1 = M.length → entry M 1 x = 0 →
    ∀ g r, r ∈ children M g → col M r = bump M g → entry M 1 g ≠ 0 → entry M 2 g ≠ 0 → x ∈ children M r →
    ∀ K0 c k, children (M.take x) r = K0 ++ [c, x - 1] → upg M (x - 1) = some k → k < x - 1 →
      col M c = col M (x - 1) ∧ upg M c = upg M (x - 1)

/-- Row-0 siblings with the same row-1 entry have the same row-1 parent. -/
theorem par1_sib {M : Mat} {c n r : Nat} (hpc : par M 0 c = some r) (hpn : par M 0 n = some r)
    (he1 : entry M 1 c = entry M 1 n) : par M 1 c = par M 1 n := by
  cases hm : par M 1 n with
  | none =>
    rw [par1_none_iff] at hm ⊢
    rw [ancL_eq hpc, he1]
    rw [ancL_eq hpn] at hm
    exact hm
  | some m =>
    rw [par1_some_iff] at hm ⊢
    rw [ancL_eq hpc, he1]
    rw [ancL_eq hpn] at hm
    exact hm

/-- Row-0 siblings with the same column and the same upgrade, of row-2 entry `0`, have the same `v`. -/
theorem v_eq_of_sib {M : Mat} {ρ : Valn} (hC : Cons M ρ) {c n r : Nat} (hc : c < M.length) (hn : n < M.length)
    (hpc : par M 0 c = some r) (hpn : par M 0 n = some r) (hcol : col M c = col M n)
    (hu : upg M c = upg M n) (h2 : entry M 2 n = 0) : ρ.v c = ρ.v n := by
  have he1 : entry M 1 c = entry M 1 n := by
    have : (col M c).2.1 = (col M n).2.1 := by rw [hcol]
    simpa [entry, col] using this
  have he2 : entry M 2 c = entry M 2 n := by
    have : (col M c).2.2 = (col M n).2.2 := by rw [hcol]
    simpa [entry, col] using this
  have hp1 := par1_sib hpc hpn he1
  rw [(hC c hc).2, (hC n hn).2]
  unfold vRhs
  rw [he1, he2, hp1, hu]
  simp only [h2, if_true]

theorem h7wTail_of (hB2 : HUACB2) (hSib : H7WSib) : H7WTail := by
  intro M ρ rk hM hS hB I x hx he1 g r hr hrb h1g h2g hxr K0 c m k hK hu hk hm u
  obtain ⟨hcol, hcu⟩ := hSib M hM hS hB x hx he1 g r hr hrb h1g h2g hxr K0 c k hK hu hk
  have S := sInv_std hM hS
  have hcT : c ∈ children (M.take x) r := by rw [hK]; simp
  have hnT : x - 1 ∈ children (M.take x) r := by rw [hK]; simp
  have hcM : c ∈ children M r := by rw [children_take, List.mem_filter] at hcT; exact hcT.1
  have hnM : x - 1 ∈ children M r := by rw [children_take, List.mem_filter] at hnT; exact hnT.1
  have h2n : entry M 2 (x - 1) = 0 := by
    have h1 := (upg_e12 hu).2
    have := S.z2 (x - 1)
    omega
  have hv : ρ.v c = ρ.v (x - 1) :=
    v_eq_of_sib I.cons (mem_children hcM).2 (mem_children hnM).2 (mem_children_iff.mp hcM).2
      (mem_children_iff.mp hnM).2 hcol hcu h2n
  have h := hB2 M ρ rk hM hS hB I (x - 1) (by omega) k hu hk u
  rw [hm] at h
  simp only [vOpt] at h
  rw [hv]
  exact h

/-- **`T0BadSeedsH7W` from `HDropU`, `HUACB2` and the structural `H7WSib`.** -/
theorem t0BadSeedsH7W_of_sib (hDU : HDropU) (hB2 : HUACB2) (hSib : H7WSib) : T0BadSeedsH7W :=
  t0BadSeedsH7W_of_B2 hDU hB2 (h7wTail_of hB2 hSib)

end Ytosk.WfH7W
