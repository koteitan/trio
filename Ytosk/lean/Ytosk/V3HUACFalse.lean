/-
A standard counterexample to HUAC itself.
An omega-squared component is absorbed by Omega_(omega + omega),
whose components are only one and zero. The old retained head is the same Omega.
The Std.exp trace and canonical Cons/Rk/Good3 tables are kernel checked.
-/
import Ytosk.V3HUACZero
import Ytosk.WfHUACShapeFalse

namespace Ytosk.HUACFalse
open T
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def M : Mat := [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (5, 2, 0), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (7, 2, 0), (6, 3, 0), (7, 4, 1), (8, 4, 1), (9, 2, 0), (8, 4, 0), (9, 5, 1), (10, 5, 1), (7, 4, 1), (8, 4, 1), (8, 4, 0), (9, 5, 1), (10, 5, 1), (11, 2, 0), (10, 5, 0), (11, 6, 1)]

def trace : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 0, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 0, 1, 0, 1, 0, 1, 1, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 0, 1, 1, 1, 2, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 1, 0, 1, 1, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 0, 1, 1, 1, 2, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 1, 0, 1, 1, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 0, 1, 1, 1, 2, 0, 1, 0, 1, 1, 1, 2, 0, 1, 0, 1, 0, 1, 1, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 0, 2, 0, 1, 0, 1, 1, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1]

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
private def t2 : T := psi t1 z z
private def t3 : T := psi t2 z z
private def t4 : T := psi z t0 t1
private def t5 : T := psi z z t0
private def t6 : T := psi z t5 z
private def t7 : T := psi t4 z t6
private def t8 : T := psi t4 z t7
private def t9 : T := psi t4 z t1
private def t10 : T := psi t4 z t9
private def t11 : T := psi t10 z z
private def t12 : T := psi t7 t11 z
private def t13 : T := psi t8 z t12
private def t14 : T := psi t1 t13 z
private def t15 : T := psi t3 z t14
private def t16 : T := psi z t15 z
private def t17 : T := psi t3 z z
private def t18 : T := psi t1 t3 z
private def t19 : T := psi t1 t2 z
private def t20 : T := psi t4 z z
private def t21 : T := psi t20 z z
private def t22 : T := psi t4 t20 z
private def t23 : T := psi t4 t13 z
private def t24 : T := psi t20 t13 z
private def t25 : T := psi z t0 t4
private def t26 : T := psi t25 t20 z
private def t27 : T := psi t4 z t20
private def t28 : T := psi t8 z z
private def t29 : T := psi t27 t28 z
private def t30 : T := psi t9 t20 z
private def t31 : T := psi t9 z z
private def t32 : T := psi t27 t11 z
private def t33 : T := psi z t5 t1
private def t34 : T := psi t4 z t33
private def t35 : T := psi t34 t20 z

def oT : List T := [t16, t17, t18, t3, t3, t19, t2, t14, t14, t21, t22, t20, t23, t23, t24, t26, t20, t24, t29, t30, t20, t29, t28, t11, t12, t31, t12, t32, t35, t20, t32, t11]
def vT : List T := [z, t3, t1, t2, t2, t1, t1, t1, t1, t20, t4, t4, t4, t4, t20, t25, t4, t20, t27, t9, t4, t27, t8, t10, t7, t9, t7, t27, t34, t4, t27, t10]
def rkO : List Nat := [25, 9, 8, 7, 6, 5, 4, 24, 23, 8, 7, 6, 22, 21, 20, 7, 6, 19, 14, 10, 6, 13, 12, 12, 18, 10, 17, 16, 12, 6, 15, 14]
def rkV : List Nat := [1, 8, 2, 6, 5, 2, 3, 2, 3, 7, 4, 5, 4, 5, 7, 6, 5, 8, 9, 9, 5, 10, 11, 11, 9, 9, 10, 11, 11, 5, 12, 13]

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

theorem old_component : two ∈ comps z (vOpt σ (par M 1 30)) := by decide

theorem new_components_small :
    ∀ d ∈ comps z (σ.v 30) ++ [z], d ≤ one := by
  have h : (comps z (σ.v 30) ++ [z]).all (fun d => decide (d ≤ one)) = true := by decide
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem not_pointwise :
    ¬ (∀ u, Dom (comps u (vOpt σ (par M 1 30))) (comps u (σ.v 30) ++ [z])) := by
  intro h
  obtain ⟨d, hd, htd⟩ := h z two old_component
  exact (by decide : ¬ two ≤ one) (le_trans htd (new_components_small d hd))

theorem not_HUAC : ¬ HUAC := by
  intro h
  exact not_pointwise (h M σ rk standard ne_sro cons rank good 30 27 (by decide) (by decide))

theorem not_HUACPositive : ¬ HUACZero.HUACPositive := by
  intro h
  exact not_HUAC (HUACCopy.hUAC_of (HUACZero.hUAC'_of h))

end Ytosk.HUACFalse
