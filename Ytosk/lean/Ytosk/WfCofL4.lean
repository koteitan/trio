/-
**数え上げの部分 `HCount` の分解。** tA に対角化の点がないとき、cof tA = ω なら後続の引数の点
ψ_a(b)（b 後続）があり（`omega_path`）、fsD(tA, k) = 枠(ψ_a(init b) · k)。

- `HNotSucc` : 最後の列が 0 でなければ tA は後続でない（実測: 後続は最後の列が 0 のものだけ）
- `HCBase`   : fsD(tA, 0) ≤ val(A[2])
- `HCRec`    : n ≥ 2 で fsD(tA, m) ≤ val(A[n]) ⇒ fsD(tA, m + 1) ≤ val(A[n+1])（コピーが 1 つ増えると加数が 1 つ増える）

から `HCount`（`hCount_of`、k の帰納法）。
-/
import Ytosk.WfCofL3

namespace Ytosk

open T

set_option linter.unusedSectionVars false

def HNotSucc : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) →
    ∀ tA, Val A tA → cof tA ≠ .succ

def HCBase : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) →
    ∀ tA, Val A tA → ∀ a b, SuccAt a b tA → ∀ tN, Val (expand A 2) tN → fsD tA z ≤ tN

def HCRec : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) →
    ∀ tA, Val A tA → ∀ a b, SuccAt a b tA → ∀ n, 2 ≤ n → ∀ m tN tN',
      Val (expand A n) tN → Val (expand A (n + 1)) tN' →
      fsD tA (natT m) ≤ tN → fsD tA (natT (m + 1)) ≤ tN'

theorem hCount_of (hD : Desc3) (hNS : HNotSucc) (hB : HCBase) (hR : HCRec) : HCount := by
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
      -- induction on `k`, with the values of all expansions from step 1
      have key : ∀ k tN, Val (expand A (k + 2)) tN → fsD tA (natT k) ≤ tN := by
        intro k
        induction k with
        | zero => intro tN h; exact hB A hA hS hE hz tA hv a b hSA tN h
        | succ k ih =>
          intro tN' h'
          obtain ⟨_, tN, _, hvk, _, _⟩ := hD A (k + 2) hA hS hE
          exact hR A hA hS hE hz tA hv a b hSA (k + 2) (by omega) k tN tN' hvk h' (ih tN hvk)
      exact key k tN hvN
  · exact absurd hct (cof_not_big_of_lt_Om1 hot (val_lt_Om1 hv) μ)

/-- **`EvalFSNZ 2` from step 1 and the six engine-side facts.** -/
theorem evalFSNZ2_of_facts (hD : Desc3) (hE : HEngD) (h0 : HRootD) (h1 : HShiftD) (h2 : HPathRD)
    (h3 : HCID) (hNS : HNotSucc) (hB : HCBase) (hR : HCRec) : EvalFSNZ 2 :=
  evalFSNZ2_of_path hD hE h0 h1 h2 h3 (hCount_of hD hNS hB hR)

end Ytosk
