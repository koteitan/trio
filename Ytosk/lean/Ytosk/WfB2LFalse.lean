/-
**B2LevS は偽（2026-10-31, WfB2L）。** 40 列の標準形（SRO から 284 歩の `Std.exp` の道）。
n = x − 1 = 38 が祖先 k = 32 = (6,4,1) へ上げ、m = P₀ k = 28 = (5,3,0)、P₀ n = 37 = (9,5,1) は g = 36 = (8,5,1) の
bump 子。k の子は 33 = (7,4,1)（bump 子、子は 34 = (8,1,0) だけ）と 35 = (7,4,0)。
c = 34 の行 1 は 1 ≠ 0 で、e1 m = 3 > e1 c + 1 = 2（c の段は m の行 1 の鎖で 2 段下）。
`WfB2S.B2LevS` のどちらの選言も成り立たない。

これまでの測定（graft4・graft5 など）は bump の親を持つ枠で b = e1 k ∈ {2, 3} しかなく、b ≥ 4 で B2LevS は
空でない主張になる。b = 3 以下の枠の行列に最後の列を足して展開（2・3 個の写し）した集合 lift1
（tmp/wf/WfB2L/lift.py）で 1009 枠が偽。ただしそこで Bad2 かつ吸収のある枠はすべて a より上に上げがなく
（U0）、StepDom は空に成り立つ: `WfB2S.B2StepAb` 自身は偽でない。
-/
import Ytosk.WfB2S2

namespace Ytosk.WfB2LFalse
open T
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def M : Mat := [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (5, 2, 0), (3, 2, 1), (4, 2, 1), (5, 1, 0), (5, 0, 0), (4, 2, 0), (5, 3, 1), (6, 3, 1), (7, 3, 0), (5, 3, 1), (6, 3, 1), (7, 1, 0), (6, 3, 0), (7, 4, 1), (8, 4, 1), (9, 3, 0), (10, 4, 0), (5, 3, 0), (6, 4, 1), (7, 4, 1), (8, 4, 0), (6, 4, 1), (7, 4, 1), (8, 1, 0), (7, 4, 0), (8, 5, 1), (9, 5, 1), (10, 4, 0), (11, 5, 0)]

def trace : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 2, 0, 0, 1, 0, 0, 1, 1, 1, 1, 2, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 2, 0, 0, 1, 0, 0, 1, 1, 1, 1, 2, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 2, 0, 0, 1, 0, 0, 1, 1, 1, 1, 2, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 2, 0, 0, 1, 0, 0, 1, 1, 1, 1, 2, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 2, 0, 1, 1, 2, 0, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 2, 0, 0, 1, 0, 0, 1, 1, 1, 1, 2, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 2, 0, 0, 1, 0, 0, 1, 1, 1, 1, 2, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 0, 0, 1, 1, 2]

private theorem std_fold : ∀ (ns : List Nat) (N : Mat), Std N → Std (ns.foldl expand N)
  | [], _, h => h
  | n :: ns, N, h => std_fold ns (expand N n) (Std.exp n h)

theorem standard : Std M := by
  have h : trace.foldl expand SRO = M := by decide
  rw [← h]
  exact std_fold trace SRO Std.sro

theorem ne_sro : M ≠ SRO := by decide

theorem children32 : children M 32 = [33, 35] := by decide
theorem children33 : children M 33 = [34] := by decide

/-- **The structural residual `B2LevS` is false.** -/
theorem not_B2LevS : ¬ WfB2S.B2LevS := by
  intro h
  rcases h M standard ne_sro 38 rfl 32 28 37 36 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) with h0 | ⟨L, j, R, c, C, hL, hjb, hR, hC, hle⟩
  · have := h0 33 (by rw [children32]; simp) (by decide) 34 (by rw [children33]; simp)
    revert this; decide
  · rw [children32] at hL
    rcases L with _ | ⟨a, _ | ⟨b, L⟩⟩
    · simp only [List.nil_append, List.cons.injEq] at hL
      obtain ⟨rfl, rfl⟩ := hL
      rw [children33] at hC
      simp only [List.cons.injEq] at hC
      obtain ⟨rfl, rfl⟩ := hC
      revert hle; decide
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hL
      obtain ⟨_, rfl, rfl⟩ := hL
      revert hjb; decide
    · simp only [List.cons_append, List.cons.injEq] at hL
      obtain ⟨_, _, h⟩ := hL
      have := congrArg List.length h
      simp at this

#print axioms not_B2LevS

end Ytosk.WfB2LFalse
