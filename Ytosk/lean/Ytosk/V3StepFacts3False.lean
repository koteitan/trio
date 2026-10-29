/-
A standard counterexample to WfStepFacts3.StepFacts3.
A leaf bump child added to a former w-step target makes HasBump true, but
its increment is only omega squared, below the outer bump term.
The Std.exp trace and canonical Cons/Rk/Good3 tables are kernel checked.
-/
import Ytosk.WfStepFacts3
import Ytosk.WfHUACShapeFalse

namespace Ytosk.StepFacts3False
open T WfHUACDeep WfStepFacts WfStepFacts3
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def M : Mat := [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (5, 2, 0), (3, 2, 1), (4, 2, 1), (5, 1, 0), (6, 2, 1), (7, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (7, 2, 0), (7, 2, 0), (6, 3, 0), (7, 4, 1), (8, 4, 1), (9, 2, 0), (9, 2, 0), (8, 4, 0), (9, 5, 1), (10, 5, 1), (11, 2, 0), (7, 4, 1), (8, 4, 1), (8, 4, 0), (9, 5, 1), (10, 5, 1), (11, 2, 0), (11, 2, 0), (10, 5, 0), (11, 6, 1)]

def trace : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 0, 2, 0, 1, 1, 2, 1, 2, 2, 2, 1, 0, 0, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 0, 0, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 0, 1, 1, 1, 1, 2, 1, 0, 1, 1, 0, 1, 1, 1, 1, 2, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 0, 1, 1, 1, 1, 2, 1, 0, 1, 1, 0, 1, 1, 1, 1, 2, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 0, 1, 1, 1, 1, 2, 1, 0, 1, 1, 0, 1, 1, 1, 1, 2, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 1, 2, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1]

private theorem std_fold : ∀ (ns : List Nat) (N : Mat), Std N → Std (ns.foldl expand N)
  | [], _, h => h
  | n :: ns, N, h => std_fold ns (expand N n) (Std.exp n h)

theorem standard : Std M := by
  have h : trace.foldl expand SRO = M := by decide
  rw [← h]
  exact std_fold trace SRO Std.sro

theorem ne_sro : M ≠ SRO := by decide

private def t0 : T := psi z z z
private def t1 : T := psi z t0 z
private def t2 : T := psi z z t0
private def t3 : T := psi z t2 z
private def t4 : T := psi t3 z z
private def t5 : T := psi t1 t4 z
private def t6 : T := psi t5 z z
private def t7 : T := psi t5 t6 z
private def t8 : T := psi t5 t7 t6
private def t9 : T := psi t5 t7 t8
private def t10 : T := psi t5 t7 t3
private def t11 : T := psi t5 t7 t1
private def t12 : T := psi t5 t7 t11
private def t13 : T := psi t12 z z
private def t14 : T := psi t10 t13 z
private def t15 : T := psi t9 z t14
private def t16 : T := psi z t15 z
private def t17 : T := psi t1 z z
private def t18 : T := psi t17 z z
private def t19 : T := psi t18 z z
private def t20 : T := psi t1 t18 z
private def t21 : T := psi t1 t17 z
private def t22 : T := psi t1 t15 z
private def t23 : T := psi t6 z z
private def t24 : T := psi z t0 t1
private def t25 : T := psi t24 t6 z
private def t26 : T := psi t5 t15 z
private def t27 : T := psi t24 t5 z
private def t28 : T := psi t24 z z
private def t29 : T := psi t5 t7 z
private def t30 : T := psi t29 t15 z
private def t31 : T := psi t1 t4 t1
private def t32 : T := psi t5 z t6
private def t33 : T := psi t31 t32 z
private def t34 : T := psi t5 t7 t29
private def t35 : T := psi t9 z z
private def t36 : T := psi t34 t35 z
private def t37 : T := psi t11 t32 z
private def t38 : T := psi t12 t6 z
private def t39 : T := psi t11 z z
private def t40 : T := psi t34 t13 z
private def t41 : T := psi z t2 t1
private def t42 : T := psi t5 t7 t41
private def t43 : T := psi t42 t32 z

def oT : List T := [t16, t19, t20, t18, t18, t21, t17, t22, t22, t23, t25, t6, t26, t27, t5, t4, t28, t26, t30, t33, t6, t6, t30, t36, t37, t6, t6, t36, t35, t38, t6, t14, t39, t14, t40, t43, t6, t6, t40, t13]
def vT : List T := [z, t18, t1, t17, t17, t1, t1, t1, t1, t6, t24, t5, t5, t24, t1, t3, t24, t5, t29, t31, t5, t5, t29, t34, t11, t5, t5, t34, t9, t12, t5, t10, t11, t10, t34, t42, t5, t5, t34, t12]
def rkO : List Nat := [28, 9, 8, 7, 6, 5, 4, 27, 26, 11, 10, 9, 25, 7, 6, 5, 5, 24, 23, 10, 9, 9, 22, 17, 13, 9, 9, 16, 15, 15, 9, 21, 13, 20, 19, 15, 9, 9, 18, 17]
def rkV : List Nat := [1, 8, 2, 6, 5, 2, 3, 2, 3, 10, 4, 8, 7, 4, 3, 4, 4, 8, 10, 9, 8, 8, 11, 12, 12, 8, 8, 13, 14, 14, 8, 12, 12, 13, 14, 14, 8, 8, 15, 16]

def σ : Valn := ⟨fun i => oT.getD i z, fun i => vT.getD i z⟩
def rk : Bool → Nat → Nat := fun b i => if b then rkO.getD i 0 else rkV.getD i 0

theorem cons : Cons M σ := by unfold Cons; decide

theorem rank : Rk M rk := WfHUACShapeFalse.rk_of_rkB (by decide)

theorem good : Good3 M σ := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · unfold cvals nzs
    decide

theorem chain : Up1 M 17 33 :=
  Up1.step (y := 22) (by decide) (Up1.step (y := 17) (by decide) (Up1.refl 17))

theorem has_bump31 : HasBump M 31 := ⟨32, by decide, by decide⟩

theorem increment31 : last (σ.v 31) = psi z two z := by decide

theorem not_bound : ¬ bumpW M σ 34 ≤ last (σ.v 31) := by decide

theorem not_chain_facts : ¬ ChainFacts3 M σ 34 33 17 := by
  intro h
  exact not_bound (h.1 33 31 chain (Up1.refl 33) (by decide) (by decide) has_bump31)

theorem not_StepFacts3 : ¬ StepFacts3 := by
  intro h
  have hf := h M σ rk standard ne_sro cons rank good 38 34 33
    (by decide) (by decide) (by decide) (by decide)
    [] 35 [38] 36 [37] (by decide) (by decide)
    (by
      intro d hd hb
      have hd' : d = 38 := by simpa using hd
      subst d
      exact False.elim ((by decide : col M 38 ≠ bump M 34) hb))
    (by decide) 17 chain (by decide)
  exact not_chain_facts hf

end Ytosk.StepFacts3False
