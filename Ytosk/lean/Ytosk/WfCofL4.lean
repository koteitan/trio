/-
**数え上げの部分 `HCount` の分解。** tA に対角化の点がないとき、cof tA = ω なら後続の引数の点
ψ_a(b)（b 後続）があり（`omega_path`）、fsD(tA, k) = 枠(ψ_a(init b) · k)。

- `HNotSucc` : 最後の列が 0 でなければ tA は後続でない（実測: 後続は最後の列が 0 のものだけ）
- `HCountS`  : 後続の引数の点 ψ_a(b) で fsD(tA, k) = 枠(ψ_a(init b) · k) ≤ val(A[k+2])

から `HCount`（`hCount_of`）。注意: 「コピーが 1 つ増えると加数が 1 つ増える」形の漸化式
（m_n = max{m : fsD(tA, m) ≤ val(A[n])} で m_{n+1} ≥ m_n + 1）は t = 2 で偽（n = 2 で 60 件余り、n = 3 で 6 件、
WfAbsW の graft36b/c）。小さい n では穴の外の大きい枝が値を決めるため。
-/
import Ytosk.WfCofL3

namespace Ytosk

open T

set_option linter.unusedSectionVars false

def HNotSucc : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) →
    ∀ tA, Val A tA → cof tA ≠ .succ

/-- **Counting, successor-argument form**: `fsD(tA, k) = frame(ψ_a(init b) · k) ≤ val(A[k+2])`. -/
def HCountS : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) →
    ∀ tA, Val A tA → ∀ a b, SuccAt a b tA → ∀ k tN, Val (expand A (k + 2)) tN → fsD tA (natT k) ≤ tN

theorem hCount_of (hD : Desc3) (hNS : HNotSucc) (hCS : HCountS) : HCount := by
  intro A hA hS hE hz tA hv hnd k tN hvN
  obtain ⟨tA', _, hv', _, hot, _⟩ := hD A 0 hA hS hE
  cases val_unique hv hv'
  rcases hct : cof tA with _ | _ | _ | μ
  · have ht : tA = z := by
      by_contra hne; exact cof_ne_zero tA hne hct
    subst ht; simp only [fs]; exact z_le _
  · exact absurd hct (hNS A hA hS hE hz tA hv)
  · rcases omega_path tA hct with ⟨a, b, μ, hDg⟩ | ⟨a, b, hSA⟩
    · exact absurd hDg (hnd a b μ)
    · rw [hSA.fs_eq_fsD]
      exact hCS A hA hS hE hz tA hv a b hSA k tN hvN
  · exact absurd hct (cof_not_big_of_lt_Om1 hot (val_lt_Om1 hv) μ)

/-- **`EvalFSNZ 2` from step 1 and the engine-side facts.** -/
theorem evalFSNZ2_of_facts (hD : Desc3) (hE : HEngD) (h0 : HRootD) (h1 : HShiftD) (h2 : HPathRD)
    (h3 : HCID) (hNS : HNotSucc) (hCS : HCountS) : EvalFSNZ 2 :=
  evalFSNZ2_of_path hD hE h0 h1 h2 h3 (hCount_of hD hNS hCS)

end Ytosk
