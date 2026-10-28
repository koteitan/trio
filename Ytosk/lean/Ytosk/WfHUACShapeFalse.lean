/-
A kernel-checked standard counterexample to `HUACShapes.HUACShape`.
48 columns, reached from SRO by an explicit `Std.exp` trace.  The canonical
valuation is given as tables; `Cons`, `Rk` and `Good3` are checked by `decide`.
At n = 46, k = 43, m = 42 the absorption is dangerous (the summand ω of v(42) is
below W = bumpW 43), lev W ≠ 0, the only bump child 44 has the only child 45 with
row 1 = 2 ≠ 4 (no return copy), and the increment of 42 is ω, which is not a
summand of v(45) (no support witness).  HUAC itself still holds here
(the deep witness of `WfHUACDeep` returns to the row-1 ancestor 21 of 42).
-/
import Ytosk.WfHUACDeep

namespace Ytosk.WfHUACShapeFalse
open T
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def M : Mat := [(0,0,0),(1,1,1),(2,1,1),(3,1,0),(1,1,1),(2,1,1),(3,1,0),(1,1,1),(2,1,0),(3,2,1),(4,2,1),(5,2,0),(3,2,1),(4,2,1),(5,1,0),(6,2,1),(7,2,1),(8,2,0),(6,2,1),(7,2,1),(8,1,0),(4,2,0),(5,3,1),(6,3,1),(7,2,0),(6,3,0),(7,4,1),(8,4,1),(9,2,0),(8,4,0),(9,5,1),(10,5,1),(11,2,0),(5,3,0),(6,4,1),(7,4,1),(8,2,0),(7,4,0),(8,5,1),(9,5,1),(10,2,0),(6,4,1),(7,4,0),(8,5,1),(9,5,1),(10,2,0),(9,5,0),(10,6,1)]

def trace : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 2, 1, 0, 1, 1, 2, 1, 2, 2, 2, 1, 0, 1, 0, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 1, 0, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 1, 0, 1, 1, 1, 2, 1, 0, 1, 0, 1, 1, 1, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 0, 1, 1, 1, 2, 1, 0, 1, 0, 1, 1, 1, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 0, 1, 1, 1, 2, 1, 0, 1, 0, 1, 1, 1, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 1, 1, 2, 1, 0, 1, 1, 1, 2, 1, 0, 1, 1, 1, 2, 1, 0, 1, 0, 1, 1, 1, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 1, 1, 1, 2, 1, 0, 1, 0, 1, 1, 1, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 1, 0, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 0, 1, 1, 1, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 0, 1, 1, 1, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 0, 1, 1, 1, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 1, 2, 1, 1, 1]

private theorem std_fold : ∀ (ns : List Nat) (N : Mat), Std N → Std (ns.foldl expand N)
  | [], _, h => h
  | n :: ns, N, h => std_fold ns (expand N n) (Std.exp n h)

theorem standard : Std M := by
  have h : trace.foldl expand SRO = M := by decide
  rw [← h]
  exact std_fold trace SRO Std.sro

theorem ne_sro : M ≠ SRO := by decide

def oT : List T := [(psi z (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z))) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z z z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z)) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z (psi z z z) z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi z (psi z z z) z)) z z) z)) z)) z), (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z), (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z z) z) z z) z z) z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z))) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z z z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z)) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z (psi z z z) z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi z (psi z z z) z)) z z) z)) z)) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z))) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z z z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z)) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z (psi z z z) z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi z (psi z z z) z)) z z) z)) z)) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z))) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z z z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z)) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z (psi z z z) z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi z (psi z z z) z)) z z) z)) z)) z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z), (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) z z) z z) z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi z (psi z z z) z) z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z))) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z z z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z)) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z (psi z z z) z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi z (psi z z z) z)) z z) z)) z)) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z))) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z))) z z) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z))) z z) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z))) z z) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z))) z z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi z (psi z z z) z))) (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z z z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z)) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z (psi z z z) z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi z (psi z z z) z)) z z) z)) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z)) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z)) z z) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z)) z z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z (psi z z z) z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi z (psi z z z) z)) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z (psi z z z) z)) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi z (psi z z z) z)) z z) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi z (psi z z z) z)) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z (psi z z z) (psi z (psi z z z) z))) (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi z (psi z z z) z)) z z) z), (psi (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi z (psi z z z) z)) z z)]
def vT : List T := [z, (psi (psi (psi z (psi z z z) z) z z) z z), (psi z (psi z z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi z (psi z z z) z) z z), (psi z (psi z z z) z), (psi z (psi z z z) z), (psi z (psi z z z) z), (psi z (psi z z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi z (psi z z z) z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) z z), (psi (psi z (psi z z z) z) z z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi z (psi z z z) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z)), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z)), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z))), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi z (psi z z z) z))), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z z z)), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z)), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z (psi z z z) z)), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) (psi z (psi z z z) (psi z (psi z z z) z))), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z z), (psi (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z) z) z (psi z (psi z z z) z))]
def rkO : List Nat := [29, 9, 8, 7, 6, 5, 4, 28, 27, 15, 14, 13, 26, 11, 10, 9, 8, 7, 6, 5, 4, 25, 23, 14, 13, 22, 21, 17, 13, 20, 19, 19, 13, 24, 19, 15, 13, 18, 17, 17, 13, 23, 22, 21, 17, 13, 20, 19]
def rkV : List Nat := [1, 8, 2, 6, 5, 2, 3, 2, 3, 14, 4, 12, 11, 4, 3, 8, 4, 6, 5, 4, 3, 12, 14, 13, 12, 15, 16, 16, 12, 17, 18, 18, 12, 13, 14, 14, 12, 15, 16, 16, 12, 14, 15, 16, 16, 12, 17, 18]

def σ : Valn := ⟨fun i => oT.getD i z, fun i => vT.getD i z⟩

def rk : Bool → Nat → Nat := fun b i => if b then rkO.getD i 0 else rkV.getD i 0

theorem cons : Cons M σ := by
  unfold Cons
  decide

/-- Boolean form of `Rk`. -/
def rkB (M : Mat) (rk : Bool → Nat → Nat) : Bool :=
  (List.range M.length).all fun i =>
    decide (rk false i < rk true i) &&
    (children M i).all (fun c => decide (col M c = bump M i) || (isUpg M c && topped M c) ||
      decide (rk true c < rk true i)) &&
    (decide (entry M 1 i = 0) ||
      ((match par M 1 i with
        | none => true
        | some m => decide (rk false m < rk false i)) &&
       (decide (entry M 2 i ≠ 0) || (match upg M i with
        | none => true
        | some k => decide (rk false k < rk false i))) &&
       (decide (entry M 2 i = 0) || (children M i).all (fun j =>
          !decide (col M j = bump M i) || (children M j).all (fun k => decide (rk true k < rk false i))))))

theorem rk_of_rkB {M : Mat} {rk : Bool → Nat → Nat} (h : rkB M rk = true) : Rk M rk := by
  intro i hi
  unfold rkB at h
  have hi' := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at hi'
  obtain ⟨⟨h1, h2⟩, h3⟩ := hi'
  refine ⟨h1, ?_, ?_⟩
  · intro c hc hb hu
    rcases h2 c hc with (h | h) | h
    · exact absurd h hb
    · exact absurd h hu
    · exact h
  · intro he1
    rcases h3 with h | ⟨⟨hp, hu⟩, hb⟩
    · exact absurd h he1
    refine ⟨?_, ?_, ?_⟩
    · intro m hm
      rw [hm] at hp
      simpa using hp
    · intro he2 k hk
      rcases hu with h | h
      · exact absurd he2 h
      · rw [hk] at h; simpa using h
    · intro he2 j hj hjb k hk
      rcases hb with h | h
      · exact absurd h he2
      · have := h j hj
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
        rcases this with h' | h'
        · exact absurd hjb h'
        · exact h' k hk

theorem rank : Rk M rk := rk_of_rkB (by decide)

theorem good : Good3 M σ := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · unfold cvals nzs
    decide

theorem danger : HUACShapes.Danger (vOpt σ (par M 1 46)) (bumpW M σ 43) :=
  ⟨psi z one z, by decide, by decide, one, by decide, by decide⟩

theorem children43 : children M 43 = [44, 46] := by decide
theorem children44 : children M 44 = [45] := by decide

theorem not_zero : lev (bumpW M σ 43) ≠ z := by decide

theorem not_return : ¬ HUACCopy.ReturnWitness M 46 43 42 := by
  rintro ⟨L, j, R, K, c, hL, hjb, _, hK, _, hc1, _⟩
  have hj : j ∈ children M 43 := by rw [hL]; simp
  rw [children43] at hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  swap
  · exact absurd hjb (by decide)
  have hc : c ∈ children M 44 := by rw [hK]; simp
  rw [children44] at hc
  simp only [List.mem_singleton] at hc
  subst hc
  revert hc1
  decide

theorem not_support : ¬ HUACShapes.SupportWitness M σ 46 43 42 := by
  rintro ⟨L, j, R, c, C, hL, hjb, _, _, hC, _, _, _, htail⟩
  have hj : j ∈ children M 43 := by rw [hL]; simp
  rw [children43] at hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  swap
  · exact absurd hjb (by decide)
  have hc : c ∈ children M 44 := by rw [hC]; simp
  rw [children44] at hc
  simp only [List.mem_singleton] at hc
  subst hc
  have h := htail (psi z one z) (by decide)
  revert h
  decide

/-- **The residual `HUACShape` is false** (on a standard matrix below SRO). -/
theorem not_HUACShape : ¬ HUACShapes.HUACShape := by
  intro h
  rcases h M σ rk standard ne_sro cons rank good 46 43 42 (by decide) (by decide) (by decide) danger
    with h0 | hr | hs
  · exact not_zero h0
  · exact not_return hr
  · exact not_support hs

/-! ## The new residual `WfHUACDeep.HUACDeepShape` has a witness at this frame -/

theorem up1_cases {M : Mat} {a x : Nat} (h : WfHUACDeep.Up1 M a x) :
    a = x ∨ ∃ p, par M 1 x = some p ∧ WfHUACDeep.Up1 M a p := by
  cases h with
  | refl => exact Or.inl rfl
  | step hp h => exact Or.inr ⟨_, hp, h⟩

theorem deep_witness_here : WfHUACDeep.DeepWitness M σ 46 43 42 := by
  refine ⟨[], 44, [46], 45, 21, by decide, by decide, by decide, by decide, by decide, by decide,
    WfHUACDeep.Up1.step (y := 33) (by decide) (WfHUACDeep.Up1.step (y := 21) (by decide)
      (WfHUACDeep.Up1.refl 21)), by decide, by decide, ?_⟩
  intro y h1 h2 hne t ht
  have hy : y = 42 ∨ y = 33 := by
    have hle := WfHUACDeep.up1_le h1
    rcases up1_cases h2 with rfl | ⟨p, hp, h2⟩
    · exact Or.inl rfl
    have hp' : par M 1 42 = some 33 := by decide
    rw [hp'] at hp; cases hp
    rcases up1_cases h2 with rfl | ⟨p, hp, h2⟩
    · exact Or.inr rfl
    have hp' : par M 1 33 = some 21 := by decide
    rw [hp'] at hp; cases hp
    have := WfHUACDeep.up1_le h2
    omega
  rcases hy with rfl | rfl
  · have ht' : upg M 42 = some 41 := by decide
    rw [ht'] at ht; cases ht
    have hl : last (σ.v 41) = psi z one z := by decide
    rw [hl]
    exact WfHUACDeep.dom_omega_of_comp ⟨one, by decide, le_refl _⟩
  · have ht' : upg M 33 = none := by decide
    rw [ht'] at ht; cases ht

end Ytosk.WfHUACShapeFalse
