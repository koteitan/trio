/-
**3 行・t = 2: FrameClosed を M[n] へ運ぶ（2026-10-16、t2）。**

FrameClosed は枠の性質（書き換える枠の FrameDom）なので、t = 2 の骨組み `clField_expand_t2S` で運ぶ。
- 写し: 枠の値は σ の像。書き換えの条件は σ で同値（`sh_lt_iff`・`shf_lt_iff`）、状態は σ と交換
  （`sh_spArg`）、新しい状態は `sh_H`。FrameDom そのものの σ 不変性は項だけの主張 `FDsh`（偽、`FDCut.not_FDsh`。写しの枠での形 `FDshAt`・`T2FDCopyRes` は V3T2VSFC）。
  FrameDom は区間 (max(B, Ω_s), H] のすべての C について述べるので、σ の像に入らない C（添字が (V, V′] の項を
  含む C）も動く。厳密な判定（`tmp/t2/probes/fdexact.py`、lhd_exact と同じ区間の分解）で、実際の枠と
  V′ ∈ {V + 1, V + ω, V + ω², 行列の v の値} で例外 0。
- x より前の種でない列: FrameShape で M の枠と同じか、最後の子だけが ◁ で下がる。下がった子の書き換えは元の子の
  書き換えで、H は単調（`frameDom_drop`）。
- 種の列の枠: 名前つきの残り `T2SeedFrames QFC M`。
-/
import Ytosk.V3T2VSF
import Ytosk.V3T0Frm
import Ytosk.V3T2SeedRes

namespace Ytosk

open T Classical

set_option linter.unusedSectionVars false

/-- `QFC`（t0 の V3T0Frm と同じ枠の性質）with the standard form of the child (so that lowering the child keeps it). -/
def QFCo (a : T) (Lv : List T) (cv : T) : Prop := isOT cv = true ∧ QFC a Lv cv

theorem frameClosed_iff {N : Mat} {σ : Valn} : FrameClosed N σ ↔ CLField QFC N σ := Iff.rfl

theorem clField_QFCo {N : Mat} {σ : Valn} (hG : Good3 N σ) (h : FrameClosed N σ) : CLField QFCo N σ := by
  intro i hi Lc c R hCL
  have hcN : c < N.length := (mem_children (cl_mem_children (show c ∈ CL N i by rw [hCL]; simp))).2
  exact ⟨hG.ot_o c hcN, h i hi Lc c R hCL⟩

theorem frameClosed_of_QFCo {N : Mat} {σ : Valn} (h : CLField QFCo N σ) : FrameClosed N σ :=
  fun i hi Lc c R hCL => (h i hi Lc c R hCL).2

/-- **`σ`-invariance of `FrameDom` at a rewriting frame**, a statement about terms only. **False**
(`FDCut.not_FDsh`, 2026-10-19); the expansion uses the frame-local `FDshAt` at the real copy frames instead
(`T2FDCopyRes`, V3T2VSFC).
`B` is the state before the child `ψ_s(y)` (its summands are at least the child), the child rewrites, and
`V < s`. -/
def FDsh : Prop :=
  ∀ V V' a B s y : T, isOT V = true → isOT V' = true → V < V' → isOT a = true → V ≤ a →
    isOT B = true → isOT (psi s y z) = true → V < s → (∀ q ∈ summands B, psi s y z ≤ q) →
    lt B y = true → lt (psi a z z) (psi s y z) = true →
    FrameDom a B s (H s y) →
    FrameDom (shf V V' a) (sh V V' B) (shf V V' s) (H (shf V V' s) (sh V V' y))

/-- **`QFCo` survives lowering the child** (`frameDom_drop`). -/
theorem qFCo_low : ∀ a Lv cv cv', QFCo a Lv cv → Lhd z cv' cv → isOT cv' = true → (∃ s y, cv = psi s y z) →
    (∀ s y s' y', cv = psi s y z → cv' = psi s' y' z → s' ≠ s → y' = z) → QFCo a Lv cv' := by
  intro a Lv cv cv' hQ hl hot' hcv hss
  refine ⟨hot', ?_⟩
  obtain ⟨s, y, rfl⟩ := hcv
  intro s' y' hcv' ht
  subst hcv'
  exact frameDom_drop hQ.1 hot' (le_of_lt hl.1)
    (fun hy => by
      by_contra hne
      exact hy (hss s y s' y' rfl rfl hne)) (hQ.2 s y rfl) ht

end Ytosk
