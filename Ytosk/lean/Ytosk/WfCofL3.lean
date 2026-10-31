/-
**種の漸化式 `HRecD` の分解。** r を悪い根（`BRoot`）、x = |A| − 1、Y_n = o_{A[n]}(x) とする。

- `HShiftD` : o_{A[n+1]}(x) = o_{A[n]}(r)（コピーのずらし、n ≥ 2）
- `HPathRD` : fsD(o_A(r), Y_n) ≤ o_{A[n]}(r)（経路上の r での一様な関係の下からの半分）
- `HCID`    : o_A(r) = ψ_μ(b)（tA の対角化の点の項は悪い根の値そのもの）
- `HRootD`  : 悪い根がある

から ψ_μ(b[Y_n]) = fsD(ψ_μ(b), Y_n) ≤ o_{A[n]}(r) = Y_{n+1}（`hRecD_of`）。
実測（tmp/wf/WfCofL/out）ではどれも例外 0 で、漸化式は等号。
-/
import Ytosk.WfCofL2

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- The row used to find the bad root of the last column. -/
def lastTy (A : Mat) : Nat :=
  if entry A 2 (A.length - 1) > 0 then 2 else if entry A 1 (A.length - 1) > 0 then 1 else 0

/-- `r` is the bad root of `A`. -/
def BRoot (A : Mat) (r : Nat) : Prop := par A (lastTy A) (A.length - 1) = some r

/-- The hypotheses common to the diagonal-type facts. -/
def DiagCase (A : Mat) (tA a b μ : T) : Prop :=
  Std A ∧ A ≠ SRO ∧ A ≠ [] ∧ col A (A.length - 1) ≠ (0, 0, 0) ∧ Val A tA ∧ DiagAt a b μ tA

def HRootD : Prop := ∀ A tA a b μ, DiagCase A tA a b μ → ∃ r, BRoot A r

/-- **Copy shift**: `o_{A[n+1]}(x) = o_{A[n]}(r)`. -/
def HShiftD : Prop :=
  ∀ A tA a b μ, DiagCase A tA a b μ → ∀ r, BRoot A r →
    ∀ n, 2 ≤ n → ∀ ρ rk ρ' rk', Cons (expand A n) ρ → Rk (expand A n) rk →
      Cons (expand A (n + 1)) ρ' → Rk (expand A (n + 1)) rk' →
      ρ'.o (A.length - 1) = ρ.o r

/-- **Path relation at the bad root** (lower half): `fsD(o_A(r), Y_n) ≤ o_{A[n]}(r)`. -/
def HPathRD : Prop :=
  ∀ A tA a b μ, DiagCase A tA a b μ → ∀ r, BRoot A r → ∀ ρA rkA, Cons A ρA → Rk A rkA →
    ∀ n, 2 ≤ n → ∀ ρ rk, Cons (expand A n) ρ → Rk (expand A n) rk →
      fsD (ρA.o r) (ρ.o (A.length - 1)) ≤ ρ.o r

/-- **The diagonal node is the value of the bad root**: `o_A(r) = ψ_μ(b)`. -/
def HCID : Prop :=
  ∀ A tA a b μ, DiagCase A tA a b μ → ∀ r, BRoot A r → ∀ ρA rkA, Cons A ρA → Rk A rkA →
    ρA.o r = psi μ b z

theorem hRecD_of (h0 : HRootD) (h1 : HShiftD) (h2 : HPathRD) (h3 : HCID) : HRecD := by
  intro A hA hS hE hz tA hv a b μ hDg n hn ρ rk ρ' rk' hC hR hC' hR'
  have hcase : DiagCase A tA a b μ := ⟨hA, hS, hE, hz, hv, hDg⟩
  obtain ⟨r, hr⟩ := h0 A tA a b μ hcase
  obtain ⟨ρA, rkA, hCA, hRA, _⟩ := hv
  have hci := h3 A tA a b μ hcase r hr ρA rkA hCA hRA
  have hp := h2 A tA a b μ hcase r hr ρA rkA hCA hRA n hn ρ rk hC hR
  have hsh := h1 A tA a b μ hcase r hr n hn ρ rk ρ' rk' hC hR hC' hR'
  rw [hci, fsD_here hDg.node.1 hDg.node.2] at hp
  rw [hsh]; exact hp

/-- **`EvalFSNZ 2` from the engine facts on the path** (diagonal type) and the counting part. -/
theorem evalFSNZ2_of_path (hD : Desc3) (hE : HEngD) (h0 : HRootD) (h1 : HShiftD) (h2 : HPathRD)
    (h3 : HCID) (hC : HCount) : EvalFSNZ 2 :=
  evalFSNZ2_of_parts hD hE (hRecD_of h0 h1 h2 h3) hC

end Ytosk
