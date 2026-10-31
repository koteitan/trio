/-
**H7WSib は偽（2026-10-31, WfSib）。**

標準形の 31 列の行列 M で、t0 の Bad2 の消える尾の枠に入り、直前の兄弟 c は x − 1 と列が違う。

M = (0,0,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,1)(3,1,0)(1,1,1)(2,1,0)(3,2,1)(4,2,1)(5,2,0)(3,2,1)(4,2,1)(5,1,0)
    (4,2,0)(5,3,1)(6,3,1)(7,3,0)(5,3,1)(6,3,1)(7,1,0)(6,3,0)(7,4,1)(8,4,1)(9,3,0)(10,4,1)(11,4,1)(12,3,0)
    (12,2,0)(12,0,0)

- SRO から 120 手の展開（`trace`）で着く: `standard`。
- x = 30 = (12,0,0)、r = 27 = (11,4,1) = bump g（g = 26 = (10,4,1)）、children (M.take 30) 27 = [28, 29]、
  upg 29 = 12 < 29、m = P₁ 29 = 8 = (2,1,0)（行 1 ≠ 0）。
- c = 28 = (12,3,0) ≠ col 29 = (12,2,0)（upg 28 = 19 ≠ 12 も）。
- Bad2 は第 1 の選言: g は x の祖先、UpgAbsX が x で破れる（i = 29, k = 12, W = ψ_{ψ(1)}(0), 加数 q = ψ(1)、
  u = 0, c = ψ_1(0) で Dom が破れる）。
- 系: WfH7W2.SibMCol・SibM も偽（`h7wSib_of_col`・`h7wSib_of_sibM` の対偶）。
-/
import Ytosk.WfH7W2Sib
import Ytosk.ExpGexp

namespace Ytosk.WfSibCex
open T
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def M : Mat := [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (5, 2, 0), (3, 2, 1), (4, 2, 1), (5, 1, 0), (4, 2, 0), (5, 3, 1), (6, 3, 1), (7, 3, 0), (5, 3, 1), (6, 3, 1), (7, 1, 0), (6, 3, 0), (7, 4, 1), (8, 4, 1), (9, 3, 0), (10, 4, 1), (11, 4, 1), (12, 3, 0), (12, 2, 0), (12, 0, 0)]
def trace : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2, 1, 0, 0, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 2, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 1, 0, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 1, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1]
def ρO : List T := [(psi z (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z z) z (psi z z z)) z) z) z z) z) z z) z), (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z), (psi (psi z (psi z z z) z) (psi (psi (psi z (psi z z z) z) z z) z z) z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi z (psi z z z) z) (psi (psi z (psi z z z) z) z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z z) z (psi z z z)) z) z) z z) z) z z) z), (psi (psi z (psi z z z) z) (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z z) z (psi z z z)) z) z) z z) z) z z) z), (psi (psi (psi (psi z (psi z z z) z) z z) z z) z z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) z z) z z) z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi (psi (psi z (psi z z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z z) z (psi z z z)) z) z) z z) z) z z) z), (psi (psi z (psi z z z) (psi z (psi z z z) z)) (psi (psi z (psi z z z) z) z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi (psi z (psi z z z) z) z z) (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z z) z (psi z z z)) z) z) z z) z) z z) z), (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) z z) z z), (psi (psi (psi z (psi z z z) z) z (psi z (psi z z z) z)) (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) z z) z), (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) z z), (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z z) z (psi z z z)) z) z) z z) z) z z) z), (psi (psi (psi z (psi z z z) z) z (psi z (psi z z z) z)) (psi (psi z (psi z z z) z) z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z z) z (psi z z z)) z) z) z z) z) z z) z), (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z z) z (psi z z z)) z) z) z z) z) z z), (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z (psi z (psi z z z) z))) (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z z) z (psi z z z)) z) z) z z) z) z), (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z z) z (psi z z z)) z) z) z z) z), (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z z) z (psi z z z)) z) z) z z), (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z (psi z (psi z z z) z))) (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) z (psi (psi (psi z (psi z z z) z) z z) z (psi z z z))) z), (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) z z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi z z z)]
def ρV : List T := [z, (psi (psi (psi z (psi z z z) z) z z) z z), (psi z (psi z z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi z (psi z z z) z) z z), (psi z (psi z z z) z), (psi z (psi z z z) z), (psi z (psi z z z) z), (psi z (psi z z z) z), (psi (psi (psi z (psi z z z) z) z z) z z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) z z), (psi (psi z (psi z z z) z) z z), (psi z (psi z z z) (psi z (psi z z z) z)), (psi z (psi z z z) z), (psi (psi z (psi z z z) z) z z), (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) z z), (psi (psi z (psi z z z) z) z (psi z (psi z z z) z)), (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)), (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)), (psi (psi z (psi z z z) z) z (psi z (psi z z z) z)), (psi z (psi z z z) z), (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)), (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z z) z (psi z z z)) z) z) z z) z), (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z (psi z (psi z z z) z))), (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)), (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)) (psi (psi (psi z (psi z z z) z) z z) z (psi z z z)) z) z), (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z (psi z (psi z z z) z))), (psi (psi z (psi z z z) z) z (psi (psi z (psi z z z) z) z z)), (psi (psi z (psi z z z) z) z z), z]
def W : T := (psi (psi z (psi z z z) z) z z)
def q : T := (psi z (psi z z z) z)

private theorem std_fold : ∀ (ns : List Nat) (N : Mat), Std N → Std (ns.foldl expand N)
  | [], _, h => h
  | n :: ns, N, h => std_fold ns (expand N n) (Std.exp n h)

theorem standard : Std M := by
  have h : trace.foldl expand SRO = M := by decide
  rw [← h]
  exact std_fold trace SRO Std.sro

def ρ : Valn := ⟨fun i => ρO.getD i z, fun i => ρV.getD i z⟩

theorem cons : Cons M ρ := by unfold Cons; decide

theorem not_lhd : ¬ Lhd z q W := by
  intro h
  have hd := h.2 z (psi one z z) (by decide) (by decide)
  have hno : ¬ Dom (comps z q) (comps z (psi one z z) ++ Gc z z) := by unfold Dom; decide
  exact hno hd

theorem not_upgAbsX : ¬ UpgAbsX M 30 ρ := by
  intro h
  exact not_lhd (h 29 12 W rfl (by decide) (by decide) (by decide) q (by decide) (by decide))

theorem anc : Anc0 M 26 30 :=
  Anc0.step (by decide : par M 0 30 = some 27) (Anc0.step (by decide : par M 0 27 = some 26) (Anc0.refl 26))

theorem bad2 : Bad2 M :=
  ⟨⟨12, by decide⟩, 27, 26, by decide, by decide, by decide, Or.inl ⟨Or.inl anc, ρ, cons, not_upgAbsX⟩⟩

theorem ne_sro : M ≠ SRO := by decide

/-- **`H7WSib` is false.** -/
theorem not_h7wSib : ¬ WfH7W.H7WSib := by
  intro h
  have := h M standard ne_sro bad2 30 rfl (by decide) 26 27 (by decide) (by decide) (by decide) (by decide)
    (by decide) [] 28 12 (by decide) (by decide) (by decide)
  exact absurd this.1 (by decide)

/-- The structural residuals `SibMCol` and `SibM` (WfH7W2Sib) are false too. -/
theorem not_sibMCol : ¬ WfH7W2.SibMCol := fun h => not_h7wSib (WfH7W2.h7wSib_of_col h)

theorem not_sibM : ¬ WfH7W2.SibM := fun h => not_h7wSib (WfH7W2.h7wSib_of_sibM h)

/-- The upgrade part differs as well. -/
theorem upg_ne : upg M 28 ≠ upg M 29 := by decide

end Ytosk.WfSibCex
