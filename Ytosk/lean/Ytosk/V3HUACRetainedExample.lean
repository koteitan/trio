/-
A standard example where a retained old head is needed in the HUAC certificate.
The small increment is not dominated by the anchor or by the new bump term.
Its components are dominated by the argument of the retained old head.
The Std.exp trace and canonical Cons/Rk/Good3 tables are kernel checked.
-/
import Ytosk.V3HUACIncrement
import Ytosk.WfHUACShapeFalse

namespace Ytosk.HUACRetainedExample
open T WfHUACDeep WfStepFacts WfStepFacts3
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def M : Mat := [(0, 0, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 1), (3, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (5, 2, 0), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (7, 2, 0), (7, 2, 0), (6, 3, 0), (7, 4, 1), (8, 4, 1), (9, 2, 0), (9, 2, 0), (8, 4, 0), (9, 5, 1), (10, 5, 1), (11, 2, 0), (7, 4, 1), (8, 4, 1), (8, 4, 0), (9, 5, 1), (10, 5, 1), (11, 2, 0), (10, 5, 0), (11, 6, 1)]

def trace : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 0, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 0, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 0, 1, 1, 1, 1, 2, 1, 0, 1, 1, 0, 1, 1, 1, 1, 2, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 0, 1, 1, 1, 1, 2, 1, 0, 1, 1, 0, 1, 1, 1, 1, 2, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 0, 1, 1, 1, 1, 2, 1, 0, 1, 1, 0, 1, 1, 1, 1, 2, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 0, 1, 2, 0, 1, 1, 0, 1, 1, 1, 1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 0, 2, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1]

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
private def t5 : T := psi t4 z z
private def t6 : T := psi t4 t5 z
private def t7 : T := psi t4 t6 t5
private def t8 : T := psi t4 t6 t7
private def t9 : T := psi z z t0
private def t10 : T := psi z t9 z
private def t11 : T := psi t4 t6 t10
private def t12 : T := psi t4 z t1
private def t13 : T := psi t4 t6 t12
private def t14 : T := psi t13 z z
private def t15 : T := psi t11 t14 z
private def t16 : T := psi t8 z t15
private def t17 : T := psi t1 t16 z
private def t18 : T := psi t3 z t17
private def t19 : T := psi z t18 z
private def t20 : T := psi t3 z z
private def t21 : T := psi t1 t3 z
private def t22 : T := psi t1 t2 z
private def t23 : T := psi t5 z z
private def t24 : T := psi t4 t16 z
private def t25 : T := psi t4 t6 z
private def t26 : T := psi t25 t16 z
private def t27 : T := psi z t0 t4
private def t28 : T := psi t4 z t5
private def t29 : T := psi t27 t28 z
private def t30 : T := psi t4 t6 t25
private def t31 : T := psi t8 z z
private def t32 : T := psi t30 t31 z
private def t33 : T := psi t4 t6 t1
private def t34 : T := psi t33 t28 z
private def t35 : T := psi t4 t6 t33
private def t36 : T := psi t35 t5 z
private def t37 : T := psi t33 z z
private def t38 : T := psi t7 t14 z
private def t39 : T := psi z t9 t1
private def t40 : T := psi t4 t6 t39
private def t41 : T := psi t40 t5 z

def oT : List T := [t19, t20, t21, t3, t3, t22, t2, t17, t17, t23, t6, t5, t24, t24, t26, t29, t5, t5, t26, t32, t34, t5, t5, t32, t31, t36, t5, t15, t37, t15, t38, t41, t5, t38, t14]
def vT : List T := [z, t3, t1, t2, t2, t1, t1, t1, t1, t5, t4, t4, t4, t4, t25, t27, t4, t4, t25, t30, t33, t4, t4, t30, t8, t35, t4, t11, t33, t11, t7, t40, t4, t7, t13]
def rkO : List Nat := [25, 9, 8, 7, 6, 5, 4, 24, 23, 8, 7, 6, 22, 21, 20, 7, 6, 6, 19, 14, 10, 6, 6, 13, 12, 12, 6, 18, 10, 17, 16, 12, 6, 15, 14]
def rkV : List Nat := [1, 8, 2, 6, 5, 2, 3, 2, 3, 7, 4, 5, 4, 5, 7, 6, 5, 5, 8, 9, 9, 5, 5, 10, 11, 11, 5, 9, 9, 10, 11, 11, 5, 12, 13]

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

def index : T := psi z one (psi z one z)
def argument : T := psi index (psi index z z) z

private theorem not_dom_of_small_components {A : T}
    (hA : (comps z A ++ [z]).all (fun d => decide (d ≤ one)) = true) :
    ¬ (∀ u, Dom (comps u (psi z two z)) (comps u A ++ [z])) := by
  intro h
  obtain ⟨d, hd, htd⟩ := h z two (by decide)
  have hdle : ∀ e ∈ comps z A ++ [z], e ≤ one := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hA
  exact (by decide : ¬ two ≤ one) (le_trans htd (hdle d hd))

theorem no_anchor_certificate :
    ¬ (∀ u, Dom (comps u (psi z two z)) (comps u (σ.v 13) ++ [z])) := by
  exact not_dom_of_small_components (by decide)

theorem no_bump_certificate :
    ¬ (∀ u, Dom (comps u (psi z two z)) (comps u (bumpW M σ 30) ++ [z])) := by
  exact not_dom_of_small_components (by decide)

theorem increment : last (σ.v 27) = psi z two z := by decide

theorem small_increment : last (σ.v 27) < bumpW M σ 30 := by decide

theorem upgrade : upg M 33 = some 30 := by decide

theorem chain : Up1 M 13 29 :=
  Up1.step (y := 18) (by decide) (Up1.step (y := 13) (by decide) (Up1.refl 13))

/-- HUAC still holds at this actual ancestor-upgrade frame. -/
theorem huac_at_33 :
    ∀ u, Dom (comps u (vOpt σ (par M 1 33))) (comps u (σ.v 33) ++ [z]) := by
  have hV : vOpt σ (par M 1 33) = psi index argument (psi z two z) := by decide
  have hVN : σ.v 33 = add (psi index argument (psi z two z)) (bumpW M σ 30) := by decide
  rw [hV, hVN]
  exact HUACIncrement.dom_add_zero_tail_of_retained_head (by decide) (by decide) (by decide)

end Ytosk.HUACRetainedExample
