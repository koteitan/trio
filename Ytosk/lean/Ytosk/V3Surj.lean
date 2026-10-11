/-
**翻訳は全射（段 1 と評価側の共終性を仮定して）。**

評価側の共終性 `EvalCof`: SRO 以外の空でない標準形 A と、A の値より小さい標準形の項 t について、
ある n で t ≤ (A[n] の値)。これと段 1 `Desc3` を仮定すると、SRO のある展開の値より小さい標準形の項は、
どれも SRO 以外の標準形の値になる（`surj`）。

証明は A についての整礎帰納法（段 1 から `terminates_of_desc3`）: t = A の値なら A、t < A の値なら
共終性で t ≤ A[n] の値として A[n] へ進む。空の行列の値は 0（`val_nil`）。
-/
import Ytosk.V3Order

namespace Ytosk

open Relation T

/-- The value of the empty matrix is `0`. -/
theorem val_nil : Val [] z :=
  ⟨⟨fun _ => z, fun _ => z⟩, fun _ _ => 0, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _), by simp [root, sumN]⟩

/-- **Cofinality on the evaluation side**: below the value of a standard form `A`, every standard term
is at most the value of some expansion `A[n]`. -/
def EvalCof : Prop :=
  ∀ A, Std A → A ≠ SRO → A ≠ [] → ∀ tA t, Val A tA → isOT t = true → t < tA →
    ∃ n tN, Val (expand A n) tN ∧ t ≤ tN

/-- Every standard term at most the value of a standard form `A ≠ SRO` is a value. -/
theorem surj_below (hD : Desc3) (hC : EvalCof) :
    ∀ A, Std A → A ≠ SRO → ∀ tA t, Val A tA → isOT t = true → t ≤ tA →
      ∃ B, Std B ∧ B ≠ SRO ∧ Val B t := by
  intro A
  induction A using (terminates_of_desc3 hD).induction with
  | _ A ih =>
  intro hA hAS tA t hv hot hle
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact ⟨A, hA, hAS, hv⟩
  · have hAE : A ≠ [] := by
      rintro rfl
      rw [val_unique hv val_nil] at hlt
      exact not_lt_z _ hlt
    obtain ⟨n, tN, hvN, hleN⟩ := hC A hA hAS hAE tA t hv hot hlt
    have hst : Step' (expand A n) A := ⟨hA, hAE, n, rfl⟩
    exact ih _ hst (Std.exp n hA) (step_ne_sro hD hst) tN t hvN hot hleN

/-- **The translation is onto** (given step 1 and the evaluation-side cofinality): every standard term
below the value of some `SRO[n]` is the value of a standard form other than SRO. -/
theorem surj (hD : Desc3) (hC : EvalCof) {t : T} (hot : isOT t = true) {n : Nat} {tN : T}
    (hvN : Val (expand SRO n) tN) (hlt : t < tN) : ∃ B, Std B ∧ B ≠ SRO ∧ Val B t := by
  have hst : Step' (expand SRO n) SRO := ⟨Std.sro, by decide, n, rfl⟩
  exact surj_below hD hC _ (Std.exp n Std.sro) (step_ne_sro hD hst) tN t hvN hot hlt.le

end Ytosk
