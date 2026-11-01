/- Positive DQX witnesses with true Cons valuations on the two unresolved
standard matrices. No engine or top adopts DQX here. -/
import Ytosk.V3DQX
import Ytosk.V3QRStepV3
namespace Ytosk.DQXSanity
open T
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
private theorem std_fold : ∀ (ns : List Nat) (P : Mat), Std P → Std (ns.foldl expand P)
  | [], _, h => h
  | n :: ns, P, h => std_fold ns (expand P n) (Std.exp n h)
private def t0 : T := psi z z z
private def t1 : T := psi z t0 z
private def t2 : T := psi z t0 t1
private def t3 : T := psi z t0 t0
private def t4 : T := psi t2 z z
private def t5 : T := psi z z t0
private def t6 : T := psi z t5 z
private def t7 : T := psi t6 z z
private def t8 : T := psi z t7 z
private def t9 : T := psi t3 t4 t8
private def t10 : T := psi t2 z t9
private def t11 : T := psi t1 t10 z
private def t12 : T := psi t3 t4 t11
private def t13 : T := psi t2 z t12
private def t14 : T := psi t1 t13 z
private def t15 : T := psi t3 t4 t14
private def t16 : T := psi t2 z t15
private def t17 : T := psi t1 t16 z
private def t18 : T := psi t17 z z
private def t19 : T := psi t2 z t4
private def t20 : T := psi t1 t19 z
private def t21 : T := psi t20 z z
private def t22 : T := psi t17 t21 z
private def t23 : T := psi t18 z t22
private def t24 : T := psi t1 t23 z
private def t25 : T := psi t24 z z
private def t26 : T := psi t25 z z
private def t27 : T := psi t1 t26 z
private def t28 : T := psi t27 z z
private def t29 : T := psi t28 z z
private def t30 : T := psi z t29 z
private def t31 : T := psi t1 z z
private def t32 : T := psi t31 z z
private def t33 : T := psi t32 z z
private def t34 : T := psi t1 t32 z
private def t35 : T := psi t1 t31 z
private def t36 : T := psi t1 t29 z
private def t37 : T := psi t2 t28 z
private def t38 : T := psi t2 t27 z
private def t39 : T := psi t2 t25 z
private def t40 : T := psi t2 t24 z
private def t41 : T := psi t18 z z
private def t42 : T := psi t2 t18 z
private def t43 : T := psi t2 t11 z
private def t44 : T := psi t3 t4 z
private def t45 : T := psi t1 t16 t1
private def t46 : T := psi t45 t20 z
private def t47 : T := psi t2 z t44
private def t48 : T := psi t1 t47 z
private def t49 : T := psi t1 t16 t48
private def t50 : T := psi t49 z z
private def t51 : T := psi t17 t50 z
private def t52 : T := psi t18 z t51
private def t53 : T := psi t1 t52 z
private def t54 : T := psi t53 z z
private def t55 : T := psi t54 z z
private def t56 : T := psi t1 t55 z
private def t57 : T := psi t56 z z
private def t58 : T := psi t57 z z
private def t59 : T := psi z t58 z
private def t60 : T := psi t1 t58 z
private def t61 : T := psi t2 t57 z
private def t62 : T := psi t2 t56 z
private def t63 : T := psi t2 t54 z
private def t64 : T := psi t2 t53 z
private def t65 : T := psi t45 t48 z
private def t66 : T := psi t48 z z
private def t67 : T := psi z z t5
private def t68 : T := psi z t67 z
private def t69 : T := psi t68 z z
private def t70 : T := psi z t69 z
private def t71 : T := psi t3 t4 t70
private def t72 : T := psi t2 z t71
private def t73 : T := psi t1 t72 z
private def t74 : T := psi t3 t4 t73
private def t75 : T := psi t2 z t74
private def t76 : T := psi t1 t75 z
private def t77 : T := psi t3 t4 t76
private def t78 : T := psi t2 z t77
private def t79 : T := psi t1 t78 z
private def t80 : T := psi t79 z z
private def t81 : T := psi t79 t21 z
private def t82 : T := psi t80 z t81
private def t83 : T := psi t1 t82 z
private def t84 : T := psi t83 z z
private def t85 : T := psi t84 z z
private def t86 : T := psi t1 t85 z
private def t87 : T := psi t86 z z
private def t88 : T := psi t87 z z
private def t89 : T := psi z t88 z
private def t90 : T := psi t1 t88 z
private def t91 : T := psi t2 t87 z
private def t92 : T := psi t2 t86 z
private def t93 : T := psi t2 t84 z
private def t94 : T := psi t2 t83 z
private def t95 : T := psi t80 z z
private def t96 : T := psi t2 t80 z
private def t97 : T := psi t2 t73 z
private def t98 : T := psi t1 t78 t1
private def t99 : T := psi t98 t20 z
private def t100 : T := psi t1 t78 t48
private def t101 : T := psi t100 z z
private def t102 : T := psi t79 t101 z
private def t103 : T := psi t80 z t102
private def t104 : T := psi t1 t103 z
private def t105 : T := psi t104 z z
private def t106 : T := psi t105 z z
private def t107 : T := psi t1 t106 z
private def t108 : T := psi t107 z z
private def t109 : T := psi t108 z z
private def t110 : T := psi z t109 z
private def t111 : T := psi t1 t109 z
private def t112 : T := psi t2 t108 z
private def t113 : T := psi t2 t107 z
private def t114 : T := psi t2 t105 z
private def t115 : T := psi t2 t104 z
private def t116 : T := psi t98 t48 z
def M0 : Mat := [(0,0,0), (1,1,1), (2,1,1), (3,1,0), (1,1,1), (2,1,1), (3,1,0), (1,1,1), (2,1,0), (3,2,1), (4,2,1), (5,2,0), (3,2,1), (4,2,1), (5,1,0), (6,2,1), (7,2,1), (8,2,0), (6,2,1), (7,2,1), (8,1,0), (9,2,1), (10,2,1), (11,2,0), (9,2,1), (10,2,1), (11,1,0), (12,2,1), (12,2,0), (13,3,1), (12,0,0), (13,1,1), (14,1,1), (10,2,0), (11,3,1), (12,3,1), (13,1,0), (14,2,1), (14,2,1)]

def N0 : Mat := expand M0 2

private def trace0 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]

def ρ0 : Valn := ⟨fun i => [t30, t33, t34, t32, t32, t35, t31, t36, t36, t29, t37, t28, t28, t38, t27, t26, t39, t25, t25, t40, t24, t41, t42, t18, t22, t43, t11, t4, t44, t4, t8, t7, t31, t22, t21, t46, t20, t4, t4].getD i z, fun i => [z, t32, t1, t31, t31, t1, t1, t1, t1, t28, t2, t27, t27, t2, t1, t25, t2, t24, t24, t2, t1, t18, t2, t17, t17, t2, t1, t2, t3, t2, z, t6, t1, t17, t20, t45, t1, t2, t2].getD i z⟩

def σ0 : Valn := ⟨fun i => [t59, t33, t34, t32, t32, t35, t31, t60, t60, t58, t61, t57, t57, t62, t56, t55, t63, t54, t54, t64, t53, t41, t42, t18, t51, t43, t11, t4, t44, t4, t8, t7, t31, t51, t50, t65, t48, t4, t44, t4].getD i z, fun i => [z, t32, t1, t31, t31, t1, t1, t1, t1, t57, t2, t56, t56, t2, t1, t54, t2, t53, t53, t2, t1, t18, t2, t17, t17, t2, t1, t2, t3, t2, z, t6, t1, t17, t49, t45, t1, t2, t3, t2].getD i z⟩

theorem standard36407 : Std M0 := by
  have h : trace0.foldl expand SRO = M0 := by decide
  rw [← h]; exact std_fold trace0 SRO Std.sro

theorem cons36407 : Cons M0 ρ0 := by unfold Cons; decide

theorem consN36407 : Cons N0 σ0 := by unfold Cons; decide

theorem root_decreases36407 : root N0 σ0 < root M0 ρ0 := by decide

theorem v36407 : ∃ tS, DQX z true (ρ0.v 34) (σ0.v 34) tS := by
  refine ⟨t48,?_⟩
  change DQX z true t20 t49 t48
  exact (DQX.mk (B := z) (l := t20) (lN := t48) (Q := t17) rfl (DQX.arg (DQX.mk (B := t4) (l := t4) (lN := t44) (Q := z) rfl (DQX.leaf (η := z) (l := t4) (q := t44) (by decide) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide))

theorem o36407 : ∃ tS, DQX z false (ρ0.o 34) (σ0.o 34) tS := by
  refine ⟨t66,?_⟩
  change DQX z false t21 t50 t66
  exact (DQX.sub (DQX.mk (B := z) (l := t20) (lN := t48) (Q := t17) rfl (DQX.arg (DQX.mk (B := t4) (l := t4) (lN := t44) (Q := z) rfl (DQX.leaf (η := z) (l := t4) (q := t44) (by decide) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)))

theorem W36407 : ∃ tS, DQX z false (bumpW M0 ρ0 34) (bumpW N0 σ0 34) tS := by
  refine ⟨t48,?_⟩
  change DQX z false t20 t48 t48
  exact (DQX.arg (DQX.mk (B := t4) (l := t4) (lN := t44) (Q := z) rfl (DQX.leaf (η := z) (l := t4) (q := t44) (by decide) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide))

def M1 : Mat := [(0,0,0), (1,1,1), (2,1,1), (3,1,0), (1,1,1), (2,1,1), (3,1,0), (1,1,1), (2,1,0), (3,2,1), (4,2,1), (5,2,0), (3,2,1), (4,2,1), (5,1,0), (6,2,1), (7,2,1), (8,2,0), (6,2,1), (7,2,1), (8,1,0), (9,2,1), (10,2,1), (11,2,0), (9,2,1), (10,2,1), (11,1,0), (12,2,1), (12,2,0), (13,3,1), (12,0,0), (13,1,1), (14,1,1), (14,1,1), (10,2,0), (11,3,1), (12,3,1), (13,1,0), (14,2,1), (14,2,1)]

def N1 : Mat := expand M1 2

private def trace1 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]

def ρ1 : Valn := ⟨fun i => [t89, t33, t34, t32, t32, t35, t31, t90, t90, t88, t91, t87, t87, t92, t86, t85, t93, t84, t84, t94, t83, t95, t96, t80, t81, t97, t73, t4, t44, t4, t70, t69, t31, t31, t81, t21, t99, t20, t4, t4].getD i z, fun i => [z, t32, t1, t31, t31, t1, t1, t1, t1, t87, t2, t86, t86, t2, t1, t84, t2, t83, t83, t2, t1, t80, t2, t79, t79, t2, t1, t2, t3, t2, z, t68, t1, t1, t79, t20, t98, t1, t2, t2].getD i z⟩

def σ1 : Valn := ⟨fun i => [t110, t33, t34, t32, t32, t35, t31, t111, t111, t109, t112, t108, t108, t113, t107, t106, t114, t105, t105, t115, t104, t95, t96, t80, t102, t97, t73, t4, t44, t4, t70, t69, t31, t31, t102, t101, t116, t48, t4, t44, t4].getD i z, fun i => [z, t32, t1, t31, t31, t1, t1, t1, t1, t108, t2, t107, t107, t2, t1, t105, t2, t104, t104, t2, t1, t80, t2, t79, t79, t2, t1, t2, t3, t2, z, t68, t1, t1, t79, t100, t98, t1, t2, t3, t2].getD i z⟩

theorem standard36420 : Std M1 := by
  have h : trace1.foldl expand SRO = M1 := by decide
  rw [← h]; exact std_fold trace1 SRO Std.sro

theorem cons36420 : Cons M1 ρ1 := by unfold Cons; decide

theorem consN36420 : Cons N1 σ1 := by unfold Cons; decide

theorem root_decreases36420 : root N1 σ1 < root M1 ρ1 := by decide

theorem v36420 : ∃ tS, DQX z true (ρ1.v 35) (σ1.v 35) tS := by
  refine ⟨t48,?_⟩
  change DQX z true t20 t100 t48
  exact (DQX.mk (B := z) (l := t20) (lN := t48) (Q := t79) rfl (DQX.arg (DQX.mk (B := t4) (l := t4) (lN := t44) (Q := z) rfl (DQX.leaf (η := z) (l := t4) (q := t44) (by decide) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide))

theorem o36420 : ∃ tS, DQX z false (ρ1.o 35) (σ1.o 35) tS := by
  refine ⟨t66,?_⟩
  change DQX z false t21 t101 t66
  exact (DQX.sub (DQX.mk (B := z) (l := t20) (lN := t48) (Q := t79) rfl (DQX.arg (DQX.mk (B := t4) (l := t4) (lN := t44) (Q := z) rfl (DQX.leaf (η := z) (l := t4) (q := t44) (by decide) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)))

theorem W36420 : ∃ tS, DQX z false (bumpW M1 ρ1 35) (bumpW N1 σ1 35) tS := by
  refine ⟨t48,?_⟩
  change DQX z false t20 t48 t48
  exact (DQX.arg (DQX.mk (B := t4) (l := t4) (lN := t44) (Q := z) rfl (DQX.leaf (η := z) (l := t4) (q := t44) (by decide) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide))
/-- The actual translation values exist and strictly decrease, independently
of every unproved engine-input hypothesis. -/
theorem values_decrease36407 : ∃ a b, Val M0 a ∧ Val N0 b ∧ b < a := by
  obtain ⟨rk,hR⟩ := rk_std standard36407 (by decide : M0 ≠ SRO)
  obtain ⟨rkN,hRN⟩ := rk_std (Std.exp 2 standard36407) (by decide : N0 ≠ SRO)
  exact ⟨root M0 ρ0,root N0 σ0,⟨ρ0,rk,cons36407,hR,rfl⟩,
    ⟨σ0,rkN,consN36407,hRN,rfl⟩,root_decreases36407⟩

/-- The actual translation values exist and strictly decrease, independently
of every unproved engine-input hypothesis. -/
theorem values_decrease36420 : ∃ a b, Val M1 a ∧ Val N1 b ∧ b < a := by
  obtain ⟨rk,hR⟩ := rk_std standard36420 (by decide : M1 ≠ SRO)
  obtain ⟨rkN,hRN⟩ := rk_std (Std.exp 2 standard36420) (by decide : N1 ≠ SRO)
  exact ⟨root M1 ρ1,root N1 σ1,⟨ρ1,rk,cons36420,hR,rfl⟩,
    ⟨σ1,rkN,consN36420,hRN,rfl⟩,root_decreases36420⟩

/-- The positive leaf witness is attached to an actual BadCall at this source. -/
theorem badCall36407 : WfBad.BadCall M0 ρ0 36 z 34 := by
  refine ⟨?_,by decide,by decide,by decide,head (ρ0.v 33),by decide,by decide,by decide⟩
  refine ⟨33,[],by decide,by decide,by decide,by decide,?_⟩
  decide

/-- The positive leaf witness is attached to an actual BadCall at this source. -/
theorem badCall36420 : WfBad.BadCall M1 ρ1 37 z 35 := by
  refine ⟨?_,by decide,by decide,by decide,head (ρ1.v 34),by decide,by decide,by decide⟩
  refine ⟨34,[],by decide,by decide,by decide,by decide,?_⟩
  decide

end Ytosk.DQXSanity
