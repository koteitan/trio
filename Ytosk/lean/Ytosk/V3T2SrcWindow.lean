/-
A source absorption window can be checked by one comparison after a split.
No global matrix residual is introduced here. In the measured T2AbsNSrcW(a)
cases the window is empty; the structural proof of the resulting head bound
is still a separate obligation.
-/
import Ytosk.WfT2Src

namespace Ytosk.T2SrcWindow
open T

/-- A summand below the split threshold lies in the low part. -/
theorem mem_low_of_lt {A W q : T} (hq : q ∈ summands A) (hqw : q < W) :
    q ∈ summands (split A W).2 := by
  have happ := split_app W A
  rw [← happ, summands_app] at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact False.elim ((split_fst_ge W A q hq) hqw)
  · exact hq

/-- The low part contains only summands from the original input. -/
theorem mem_of_mem_low {A W q : T} (hq : q ∈ summands (split A W).2) :
    q ∈ summands A := by
  rw [← split_app W A, summands_app]
  exact List.mem_append_right _ hq

/-- No summand lies in [max(C, WT), W) exactly when the head of the low
part is below C or WT. This is an equivalence, not a stronger bound. -/
theorem window_iff_head {A W WT C : T} (hA : isOT A = true) (hC : z < C) :
    (∀ q ∈ summands A, ¬ q < C → q < W → q < WT) ↔
      head (split A W).2 < C ∨ head (split A W).2 < WT := by
  constructor
  · intro h
    by_cases hz : (split A W).2 = z
    · left; simpa only [hz, head] using hC
    · have hq : head (split A W).2 ∈ summands A :=
        mem_of_mem_low (head_mem_summands hz)
      have hqw : head (split A W).2 < W := by
        rcases split_snd_head W A with he | he
        · exact False.elim (hz he)
        · exact he
      by_cases hc : head (split A W).2 < C
      · exact Or.inl hc
      · exact Or.inr (h _ hq hc hqw)
  · intro hh q hq hqc hqw
    have hlo : isOT (split A W).2 = true :=
      isOT_app_right (by rw [split_app]; exact hA)
    have hle := summands_le_head hlo q (mem_low_of_lt hq hqw)
    rcases hh with hc | ht
    · exact False.elim (hqc (lt_of_le_of_lt hle hc))
    · exact lt_of_le_of_lt hle ht

/-- The measured head bound rules out DropFail without any Lhd argument. -/
theorem not_dropFail_of_head {M : Mat} {ρ τ : Valn} {x i : Nat}
    (hOT : isOT (vOpt ρ (par M 1 i)) = true)
    (hb : head (split (vOpt ρ (par M 1 i)) (bumpW M ρ i)).2 < psi z two z ∨
      head (split (vOpt ρ (par M 1 i)) (bumpW M ρ i)).2 < bumpW (M.take x) τ i) :
    ¬ WfT2Abs.DropFail M ρ τ x i := by
  intro hf
  apply hf
  intro q hq hq2 hnT hqW
  exact False.elim (hnT ((window_iff_head hOT (z_lt_psi _ _ _)).mpr hb q hq hq2 hqW))

end Ytosk.T2SrcWindow
