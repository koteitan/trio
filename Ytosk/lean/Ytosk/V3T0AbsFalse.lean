/- A standard t=0 counterexample to the global T0AbsW input. -/
import Ytosk.V3T0CarrierV3
import Ytosk.ExpGexp
import Ytosk.WfAbsWEta

namespace Ytosk.T0AbsFalse
open T
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
private def t0 : T := psi z z z
private def t1 : T := psi z t0 z
private def t2 : T := psi z z t0
private def t3 : T := psi z z t2
private def t4 : T := psi z t3 z
private def t5 : T := psi t4 z z
private def t6 : T := psi z t5 z
private def t7 : T := psi t1 z t6
private def t8 : T := psi t1 z t7
private def t9 : T := psi t1 t8 z
private def t10 : T := psi t1 t9 z
private def t11 : T := psi t1 t10 z
private def t12 : T := psi t11 z z
private def t13 : T := psi t1 t0 z
private def t14 : T := psi t1 t13 z
private def t15 : T := psi t1 t14 z
private def t16 : T := psi t1 t15 z
private def t17 : T := psi t16 z z
private def t18 : T := psi t11 t17 z
private def t19 : T := psi t12 z t18
private def t20 : T := psi t1 t19 z
private def t21 : T := psi t20 z z
private def t22 : T := psi t21 z z
private def t23 : T := psi t1 t22 z
private def t24 : T := psi t23 z z
private def t25 : T := psi t24 z z
private def t26 : T := psi z t25 z
private def t27 : T := psi t1 z z
private def t28 : T := psi t27 z z
private def t29 : T := psi t28 z z
private def t30 : T := psi t1 t28 z
private def t31 : T := psi t1 t27 z
private def t32 : T := psi t1 t25 z
private def t33 : T := psi z t0 t1
private def t34 : T := psi t33 t24 z
private def t35 : T := psi t33 t23 z
private def t36 : T := psi t33 t21 z
private def t37 : T := psi t33 t20 z
private def t38 : T := psi t12 z z
private def t39 : T := psi t33 t12 z
private def t40 : T := psi t33 t9 z
private def t41 : T := psi t1 t10 t1
private def t42 : T := psi t41 t14 z
private def t43 : T := psi t0 z z
private def t44 : T := psi t1 z t43
private def t45 : T := psi t1 t44 z
private def t46 : T := psi t1 t45 z
private def t47 : T := psi t1 t46 z
private def t48 : T := psi t1 t10 t47
private def t49 : T := psi t48 z z
private def t50 : T := psi t11 t49 z
private def t51 : T := psi t12 z t50
private def t52 : T := psi t1 t51 z
private def t53 : T := psi t52 z z
private def t54 : T := psi t53 z z
private def t55 : T := psi t1 t54 z
private def t56 : T := psi t55 z z
private def t57 : T := psi t56 z z
private def t58 : T := psi z t57 z
private def t59 : T := psi t1 t57 z
private def t60 : T := psi t33 t56 z
private def t61 : T := psi t33 t55 z
private def t62 : T := psi t33 t53 z
private def t63 : T := psi t33 t52 z
private def t64 : T := psi t41 t45 z
private def t65 : T := psi z t27 z
private def t66 : T := psi t65 z z
private def t67 : T := psi t66 z z
private def t68 : T := psi t1 z t67
private def t69 : T := psi t1 t68 z
private def t70 : T := psi t1 t69 z
private def t71 : T := psi t1 t70 z
def M : Mat := [(0,0,0), (1,1,1), (2,1,1), (3,1,0), (1,1,1), (2,1,1), (3,1,0), (1,1,1), (2,1,0), (3,2,1), (4,2,1), (5,2,0), (3,2,1), (4,2,1), (5,1,0), (6,2,1), (7,2,1), (8,2,0), (6,2,1), (7,2,1), (8,1,0), (9,2,1), (10,2,1), (11,2,0), (9,2,1), (10,2,1), (11,1,0), (12,1,0), (12,1,0), (12,0,0), (13,1,1), (14,1,1), (14,1,1), (10,2,0), (11,3,1), (12,3,1), (13,1,0), (14,1,0), (15,0,0)]
def N : Mat := [(0,0,0), (1,1,1), (2,1,1), (3,1,0), (1,1,1), (2,1,1), (3,1,0), (1,1,1), (2,1,0), (3,2,1), (4,2,1), (5,2,0), (3,2,1), (4,2,1), (5,1,0), (6,2,1), (7,2,1), (8,2,0), (6,2,1), (7,2,1), (8,1,0), (9,2,1), (10,2,1), (11,2,0), (9,2,1), (10,2,1), (11,1,0), (12,1,0), (12,1,0), (12,0,0), (13,1,1), (14,1,1), (14,1,1), (10,2,0), (11,3,1), (12,3,1), (13,1,0), (14,1,0), (14,1,0)]
def trace : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
private theorem std_fold : ∀ (ns : List Nat) (P : Mat), Std P → Std (ns.foldl expand P)
  | [], _, h => h
  | n :: ns, P, h => std_fold ns (expand P n) (Std.exp n h)

theorem standard : Std M := by
  have h : trace.foldl expand SRO = M := by decide
  rw [← h]; exact std_fold trace SRO Std.sro

theorem ne_sro : M ≠ SRO := by decide
def ρ : Valn := ⟨fun i => [t26, t29, t30, t28, t28, t31, t27, t32, t32, t25, t34, t24, t24, t35, t23, t22, t36, t21, t21, t37, t20, t38, t39, t12, t18, t40, t9, t27, t27, t6, t5, t27, t27, t18, t17, t42, t14, t13, t0].getD i z, fun i => [z, t28, t1, t27, t27, t1, t1, t1, t1, t24, t33, t23, t23, t33, t1, t21, t33, t20, t20, t33, t1, t12, t33, t11, t11, t33, t1, t1, t1, z, t4, t1, t1, t11, t16, t41, t1, t1, z].getD i z⟩
def σ : Valn := ⟨fun i => [t58, t29, t30, t28, t28, t31, t27, t59, t59, t57, t60, t56, t56, t61, t55, t54, t62, t53, t53, t63, t52, t38, t39, t12, t50, t40, t9, t27, t27, t6, t5, t27, t27, t50, t49, t64, t45, t27, t43].getD i z, fun i => [z, t28, t1, t27, t27, t1, t1, t1, t1, t56, t33, t55, t55, t33, t1, t53, t33, t52, t52, t33, t1, t12, t33, t11, t11, t33, t1, t1, t1, z, t4, t1, t1, t11, t48, t41, t1, t1, t0].getD i z⟩
def q : T := t11
private def u : T := z
private def c : T := t71

theorem cons : Cons M ρ := by unfold Cons; decide

theorem consN : Cons N σ := by unfold Cons; decide

theorem expand_two : expand M 2 = N := by decide

theorem not_lhd : ¬ Lhd z q (bumpW M ρ 34) := by
  intro h
  have hd := h.2 u c (by decide) (by decide)
  have hno : ¬ Dom (comps u q) (comps u c ++ Gc u z) := by unfold Dom; decide
  exact hno hd

theorem not_t0AbsW : ¬ T0AbsW M 37 1 ρ := by
  intro h
  have he : expand M 2 = TRIO.gexp M 37 1 0 0 2 :=
    expand_eq_gexp M 2 (by decide) (by decide) (by decide)
  have hCN : Cons (TRIO.gexp M 37 1 0 0 2) σ := by rw [← he,expand_two]; exact consN
  exact not_lhd (h 2 (by omega) σ hCN 34 (by omega) (by decide) (by decide) q
    (by decide) (by decide) (by decide) (by decide))

/-- Every consistent source valuation with a ranking has the same obstruction. -/
theorem not_t0AbsW_of_cons {ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ') (hR : Rk M rk) : ¬ T0AbsW M 37 1 ρ' := by
  intro h
  have hag := agree_of_cons hC cons hR
  have hW := bumpW_congr hag 34
  have hV := vOpt_par_congr hag (r := 1) (i := 34) (by decide)
  have he : expand M 2 = TRIO.gexp M 37 1 0 0 2 :=
    expand_eq_gexp M 2 (by decide) (by decide) (by decide)
  have hCN : Cons (TRIO.gexp M 37 1 0 0 2) σ := by rw [← he,expand_two]; exact consN
  have hm : q ∈ summands (vOpt ρ' (par M 1 34)) := by rw [hV]; decide
  have hqW : q < bumpW M ρ' 34 := by rw [hW]; decide
  have hh := h 2 (by omega) σ hCN 34 (by omega) (by decide) (by decide) q hm
    (by decide) (by decide) hqW
  rw [hW] at hh
  exact not_lhd hh

/-- This obstruction is separate from the false QR input: any invariant-producing
engine outputs together with the current t0 absorption input are inconsistent. -/
theorem inconsistent_abs_input
    (hD : V3Main.HDropV3) (hF : WfExQ2.HFrameV3)
    (h0 : V3Main.ExpOutV3 0) (h1 : V3Main.ExpOutV3 1) (h2 : V3Main.ExpOutV3 2)
    (hAbs : V3Main.T0AtV3 (fun M ρ r L => T0AbsW M r L ρ)) : False := by
  obtain ⟨ρ',rk,I⟩ := V3Main.inv3V3_all hD hF h0 h1 h2 M standard ne_sro (by decide)
  have C := V3Main.ctx3 hD hF standard ne_sro (by decide) I
  have H := hAbs M ρ' rk C 37 1 (by decide) (by omega) (by decide) (by decide)
  exact not_t0AbsW_of_cons I.cons I.rank H

/-- The failed t0 call has exactly the already named bad-absorption shape. -/
theorem bad_shape : WfAbsW.BadAbsShape M N ρ σ 34 := by
  refine ⟨33, [], by decide, by decide, by decide, by decide, by decide, by decide,
    ?_, by decide, ?_⟩
  · simp
  · intro j hj
    have hlt : j < M.length := by
      by_contra h
      exact (upg_e12 hj).1 (entry_out (by omega) 1)
    have hjb : j < 39 := hlt
    have hall : ∀ k : Fin 39, upg M k.val ≠ some 34 := by decide
    exact hall ⟨j,hjb⟩ hj

theorem parent_par : par M 0 33 = some 24 := by decide

theorem parent_not_bump : col M 33 ≠ bump M 24 := by decide

end Ytosk.T0AbsFalse
