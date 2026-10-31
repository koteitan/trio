/-
**EvalFSNZ 2 の帰着: 対角化型は「エンジンの下限」と「種の漸化式」に、それ以外は数え上げに。**

x = |A| − 1（A[n] では 2 番目のコピーの根）、Y_n = o_{A[n]}(x)（評価 ρ の値）とする。
tA の基本列が対角化の点 ψ_a(b)（cof b = Ω_{μ+1}、μ ≥ a）から来る場合（`DiagAt a b μ tA`）:

- `HEngD`  : n ≥ 2 で fsD(tA, Y_n) ≤ val(A[n])                （エンジン側、実測は tmp/wf/WfCofL）
- `HRecD`  : n ≥ 2 で ψ_μ(b[Y_n]) ≤ Y_{n+1}                    （種の漸化式。実測では等号）

から γ_k ≤ Y_{k+2}（`gam_le_Y`、帰納法。基底は γ_0 = 0）と項の補題 `DiagAt.fs_le_fsD` で
tA[k] ≤ val(A[k+2]) が出る。対角化の点がない場合（実測では全部 `SuccAt` 型、最後の列の型 t = 0, 2）は
`HCount`（ψ_a(init b) の個数を数える主張）として残す。

- `evalFSNZ2_of_parts : Desc3 → HEngD → HRecD → HCount → EvalFSNZ 2`
- `surj_of_parts`
-/
import Ytosk.WfCofL1

namespace Ytosk

open T

set_option linter.unusedSectionVars false

/-- The diagonal node has a big cofinality. -/
theorem DiagAt.node {a b μ t : T} (h : DiagAt a b μ t) : b ≠ z ∧ cof b = .big μ := by
  induction h with
  | here hb hc _ => exact ⟨hb, hc⟩
  | rest _ ih => exact ih
  | arg _ _ _ ih => exact ih
  | sub _ _ _ ih => exact ih

/-- `fs` with a big cofinality is monotone (`≤`). -/
theorem fs_le_of_le {t μ : T} (hc : cof t = .big μ) {η η' : T} (h : η ≤ η') : fs t η ≤ fs t η' := by
  rcases (le_iff _ _).mp h with h | rfl
  · exact Or.inl (fs_mono hc h)
  · exact Or.inr rfl

/-- **Engine side (diagonal type)**: the value of `A[n]` (`n ≥ 2`) is at least `fsD(tA, Y_n)`,
`Y_n = o_{A[n]}(x)`, `x = |A| − 1`. -/
def HEngD : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) →
    ∀ tA, Val A tA → ∀ a b μ, DiagAt a b μ tA →
    ∀ n, 2 ≤ n → ∀ ρ rk, Cons (expand A n) ρ → Rk (expand A n) rk →
      fsD tA (ρ.o (A.length - 1)) ≤ root (expand A n) ρ

/-- **Seed recurrence (diagonal type)**: `ψ_μ(b[Y_n]) ≤ Y_{n+1}` for `n ≥ 2`. -/
def HRecD : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) →
    ∀ tA, Val A tA → ∀ a b μ, DiagAt a b μ tA →
    ∀ n, 2 ≤ n → ∀ ρ rk ρ' rk', Cons (expand A n) ρ → Rk (expand A n) rk →
      Cons (expand A (n + 1)) ρ' → Rk (expand A (n + 1)) rk' →
      psi μ (fs b (ρ.o (A.length - 1))) z ≤ ρ'.o (A.length - 1)

/-- **The counting part**: `EvalFSNZ 2` when `tA` has no diagonal point. -/
def HCount : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → col A (A.length - 1) ≠ (0, 0, 0) →
    ∀ tA, Val A tA → (∀ a b μ, ¬ DiagAt a b μ tA) →
    ∀ k tN, Val (expand A (k + 2)) tN → fs tA (natT k) ≤ tN

/-- With a successor-argument point, `HCount` is the statement `fsD(tA, k) ≤ val(A[k+2])`. -/
theorem SuccAt.fs_le_iff {a b t : T} (h : SuccAt a b t) (k : Nat) (tN : T) :
    fs t (natT k) ≤ tN ↔ fsD t (natT k) ≤ tN := by
  rw [h.fs_eq_fsD]

/-- **The seed bound** `γ_k ≤ Y_{k+2}` from the recurrence. -/
theorem gam_le_Y (hD : Desc3) (hR : HRecD) {A : Mat} (hA : Std A) (hS : A ≠ SRO) (hE : A ≠ [])
    (hz : col A (A.length - 1) ≠ (0, 0, 0)) {tA : T} (hv : Val A tA) {a b μ : T}
    (hDg : DiagAt a b μ tA) :
    ∀ k ρ rk, Cons (expand A (k + 2)) ρ → Rk (expand A (k + 2)) rk →
      gam μ b k ≤ ρ.o (A.length - 1)
  | 0, _, _, _, _ => z_le _
  | k + 1, ρ', rk', hC', hR' => by
    obtain ⟨_, tN, _, hvN, _, _⟩ := hD A (k + 2) hA hS hE
    obtain ⟨ρ, rk, hC, hRk, _⟩ := hvN
    have ih := gam_le_Y hD hR hA hS hE hz hv hDg k ρ rk hC hRk
    have hstep := hR A hA hS hE hz tA hv a b μ hDg (k + 2) (by omega) ρ rk ρ' rk' hC hRk hC' hR'
    show psi μ (fs b (gam μ b k)) z ≤ _
    exact le_trans (psi_arg_le (fs_le_of_le hDg.node.2 ih)) hstep

/-- **`EvalFSNZ 2` from the engine bound, the seed recurrence and the counting part.** -/
theorem evalFSNZ2_of_parts (hD : Desc3) (hE : HEngD) (hR : HRecD) (hC : HCount) : EvalFSNZ 2 := by
  intro A hA hS hNE hz tA hv k tN hvN
  by_cases hdg : ∃ a b μ, DiagAt a b μ tA
  · obtain ⟨a, b, μ, hDg⟩ := hdg
    obtain ⟨ρ, rk, hCo, hRk, rfl⟩ := hvN
    have hg := gam_le_Y hD hR hA hS hNE hz hv hDg k ρ rk hCo hRk
    exact le_trans (hDg.fs_le_fsD hg)
      (hE A hA hS hNE hz tA hv a b μ hDg (k + 2) (by omega) ρ rk hCo hRk)
  · exact hC A hA hS hNE hz tA hv (fun a b μ h => hdg ⟨a, b, μ, h⟩) k tN hvN

/-- **Surjectivity** from step 1 and the three parts. -/
theorem surj_of_parts (hD : Desc3) (hE : HEngD) (hR : HRecD) (hC : HCount) {t : T}
    (hot : isOT t = true) {n : Nat} {tN : T} (hvN : Val (expand SRO n) tN) (hlt : t < tN) :
    ∃ B, Std B ∧ B ≠ SRO ∧ Val B t :=
  surj_of_evalFSNZ hD (evalFSNZ2_of_parts hD hE hR hC) hot hvN hlt

end Ytosk
