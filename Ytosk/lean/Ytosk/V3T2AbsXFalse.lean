/- A standard t=2 counterexample to the proposed AbsWNx boundary input. -/
import Ytosk.V3TranslationInputsV3
import Ytosk.ExpGexp
namespace Ytosk.T2AbsXFalse
open T WfAbsW
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
def M : Mat := [(0,0,0), (1,1,1), (2,1,1), (3,1,0), (1,1,1), (2,1,1), (3,1,0), (1,1,1), (2,1,0), (3,2,1), (4,2,1), (5,2,0), (3,2,1), (4,2,1), (5,1,0), (6,2,1), (7,2,1), (8,2,0), (6,2,1), (7,2,1), (8,1,0), (9,2,1), (10,2,1), (11,2,0), (9,2,1), (10,2,1), (11,1,0), (12,2,0), (12,0,0), (13,1,1), (14,1,1), (10,2,0), (11,3,1), (12,3,1), (13,1,0), (14,2,1), (12,3,0), (11,3,1), (12,3,1), (13,1,0), (14,2,1)]
def trace : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1]
private theorem std_fold : ∀ (ns : List Nat) (P : Mat), Std P → Std (ns.foldl expand P)
  | [], _, h => h
  | n :: ns, P, h => std_fold ns (expand P n) (Std.exp n h)
theorem standard : Std M := by
  have h : trace.foldl expand SRO = M := by decide
  rw [← h]; exact std_fold trace SRO Std.sro
def N : Mat := expand M 2
private def t0 : T := psi z z z
private def t1 : T := psi z t0 z
private def t2 : T := psi z t0 t0
private def t3 : T := psi z z t0
private def t4 : T := psi z t3 z
private def t5 : T := psi t4 z z
private def t6 : T := psi z t5 z
private def t7 : T := psi t2 z t6
private def t8 : T := psi t1 t7 z
private def t9 : T := psi t2 z t8
private def t10 : T := psi t1 t9 z
private def t11 : T := psi t2 z t10
private def t12 : T := psi t1 t11 z
private def t13 : T := psi t12 z z
private def t14 : T := psi z t0 t1
private def t15 : T := psi t14 z z
private def t16 : T := psi t1 t15 z
private def t17 : T := psi t16 z z
private def t18 : T := psi t16 t17 z
private def t19 : T := psi t12 t18 z
private def t20 : T := psi t13 z t19
private def t21 : T := psi t1 t20 z
private def t22 : T := psi t21 z z
private def t23 : T := psi t22 z z
private def t24 : T := psi t1 t23 z
private def t25 : T := psi t24 z z
private def t26 : T := psi t25 z z
private def t27 : T := psi z t26 z
private def t28 : T := psi t1 z z
private def t29 : T := psi t28 z z
private def t30 : T := psi t29 z z
private def t31 : T := psi t1 t29 z
private def t32 : T := psi t1 t28 z
private def t33 : T := psi t1 t26 z
private def t34 : T := psi t14 t25 z
private def t35 : T := psi t14 t24 z
private def t36 : T := psi t14 t22 z
private def t37 : T := psi t14 t21 z
private def t38 : T := psi t13 z z
private def t39 : T := psi t14 t13 z
private def t40 : T := psi t14 t8 z
private def t41 : T := psi t2 z z
private def t42 : T := psi t1 t11 t1
private def t43 : T := psi t42 t16 z
private def t44 : T := psi t1 t41 z
private def t45 : T := psi t1 t11 t44
private def t46 : T := psi t45 z z
private def t47 : T := psi t16 t46 z
private def t48 : T := psi t12 t47 z
private def t49 : T := psi t13 z t48
private def t50 : T := psi t1 t49 z
private def t51 : T := psi t50 z z
private def t52 : T := psi t51 z z
private def t53 : T := psi t1 t52 z
private def t54 : T := psi t53 z z
private def t55 : T := psi t54 z z
private def t56 : T := psi z t55 z
private def t57 : T := psi t1 t55 z
private def t58 : T := psi t14 t54 z
private def t59 : T := psi t14 t53 z
private def t60 : T := psi t14 t51 z
private def t61 : T := psi t14 t50 z
private def t62 : T := psi t42 t44 z
private def t63 : T := psi t0 z z
private def t64 : T := psi t1 t11 t63
private def t65 : T := psi t64 z z
private def t66 : T := psi t16 t65 z
private def t67 : T := psi t12 t66 z
private def t68 : T := psi t13 z t67
private def t69 : T := psi t1 t68 z
private def t70 : T := psi t69 z z
private def t71 : T := psi t70 z z
private def t72 : T := psi t1 t71 z
private def t73 : T := psi t72 z z
private def t74 : T := psi t73 z z
private def t75 : T := psi z t74 z
private def t76 : T := psi t1 t74 z
private def t77 : T := psi t14 t73 z
private def t78 : T := psi t14 t72 z
private def t79 : T := psi t14 t70 z
private def t80 : T := psi t14 t69 z
private def t81 : T := psi t42 t63 z
private def t82 : T := psi t2 z t41
private def t83 : T := psi t2 z t82
private def t84 : T := psi t2 z t83
private def t85 : T := psi t1 t84 z
def ρ : Valn := ⟨fun i => [t27, t30, t31, t29, t29, t32, t28, t33, t33, t26, t34, t25, t25, t35, t24, t23, t36, t22, t22, t37, t21, t38, t39, t13, t19, t40, t8, t41, t6, t5, t28, t19, t18, t43, t16, t15, t17, t17, t43, t16, t15].getD i z, fun i => [z, t29, t1, t28, t28, t1, t1, t1, t1, t25, t14, t24, t24, t14, t1, t22, t14, t21, t21, t14, t1, t13, t14, t12, t12, t14, t1, t2, z, t4, t1, t12, t16, t42, t1, t14, t16, t16, t42, t1, t14].getD i z⟩
def σ : Valn := ⟨fun i => [t56, t30, t31, t29, t29, t32, t28, t57, t57, t55, t58, t54, t54, t59, t53, t52, t60, t51, t51, t61, t50, t38, t39, t13, t48, t40, t8, t41, t6, t5, t28, t48, t47, t43, t16, t15, t46, t46, t62, t44, t41].getD i z, fun i => [z, t29, t1, t28, t28, t1, t1, t1, t1, t54, t14, t53, t53, t14, t1, t51, t14, t50, t50, t14, t1, t13, t14, t12, t12, t14, t1, t2, z, t4, t1, t12, t16, t42, t1, t14, t45, t45, t42, t1, t2].getD i z⟩
def τ : Valn := ⟨fun i => [t75, t30, t31, t29, t29, t32, t28, t76, t76, t74, t77, t73, t73, t78, t72, t71, t79, t70, t70, t80, t69, t38, t39, t13, t67, t40, t8, t41, t6, t5, t28, t67, t66, t43, t16, t15, t65, t65, t81, t63].getD i z, fun i => [z, t29, t1, t28, t28, t1, t1, t1, t1, t73, t14, t72, t72, t14, t1, t70, t14, t69, t69, t14, t1, t13, t14, t12, t12, t14, t1, t2, z, t4, t1, t12, t16, t42, t1, t14, t64, t64, t42, t0].getD i z⟩
def q : T := t12
private def c : T := t85
theorem cons : Cons M ρ := by unfold Cons; decide
theorem consN : Cons N σ := by unfold Cons; decide
theorem consP : Cons (M.take 40) τ := by unfold Cons; decide
theorem goodP : Good3 (M.take 40) τ := by
  refine ⟨?_,?_,?_⟩ <;> decide
theorem not_absAt : ¬ AbsAt M N ρ σ 37 := by
  intro h
  have hh := h q (by decide) (by decide) (by decide) (by decide)
  have hd := hh.2 z c (by decide) (by decide)
  have hn : ¬ Dom (comps z q) (comps z c ++ Gc z z) := by unfold Dom; decide
  exact hn hd
theorem not_bad_shape : ¬ BadAbsShape M N ρ σ 37 := by
  intro h
  obtain ⟨m,lc,_,_,_,_,_,_,_,_,hu⟩ := h
  exact hu 36 (by decide)
theorem not_absWNx : ¬ AbsWNx M N 40 ρ σ := by
  intro h
  exact (h 37 (by omega) (by decide) (by decide)).elim not_absAt not_bad_shape

theorem gexp_two : TRIO.gexp M 39 1 1 1 2 = N := by
  have he : expand M 2 = TRIO.gexp M 39 1 1 1 2 :=
    expand_eq_gexp M 2 (by decide) (by decide) (by decide)
  exact he.symm

/-- The exact residual is false: all of its n=2 premises are satisfied. -/
private theorem below_absWNx {ν : Valn} (h : WfT2X.T2BelowResX M ν 39 1 1 1) : AbsWNx M N 40 ν σ := by
  have hGP : ∀ m, 1 ≤ m → m < 2 → ∀ ν, Cons (TRIO.gexp M 39 1 1 1 m) ν →
      Good3 (TRIO.gexp M 39 1 1 1 m) ν := by
    intro m hm hm2 ν hC
    have hm1 : m = 1 := by omega
    subst m
    have he : TRIO.gexp M 39 1 1 1 1 = M.take 40 := gexp_one_gen (by decide)
    rw [he] at hC ⊢
    obtain ⟨rk,hR⟩ := rk_std (std_take standard 40 (by decide)) (by decide : M.take 40 ≠ SRO)
    exact good3_congr goodP (agree_of_cons consP hC hR)
  have hCN : Cons (TRIO.gexp M 39 1 1 1 2) σ := by rw [gexp_two]; exact consN
  have hOT : ∀ b j, 40 ≤ j → j < (TRIO.gexp M 39 1 1 1 2).length →
      isOT (valB σ b j) = true := by
    intro b j hj hjN
    rw [gexp_two] at hjN
    have hl : N.length = 41 := by decide
    have he : j = 40 := by omega
    subst j
    cases b <;> decide
  have hh := h 2 (by omega) hGP σ hCN hOT
  simpa only [gexp_two] using hh.2.2.2.1

theorem not_t2BelowResX : ¬ WfT2X.T2BelowResX M ρ 39 1 1 1 :=
  fun h => not_absWNx (below_absWNx h)

theorem not_t2BelowResX_of_cons {ρ' : Valn} {rk : Bool → Nat → Nat}
    (hC : Cons M ρ') (hR : Rk M rk) : ¬ WfT2X.T2BelowResX M ρ' 39 1 1 1 := by
  intro h
  have hag := agree_of_cons hC cons hR
  have hW := bumpW_congr hag 37
  have hV := vOpt_par_congr hag (r := 1) (i := 37) (by decide)
  rcases below_absWNx h 37 (by omega) (by decide) (by decide) with hA | hs
  · apply not_absAt
    intro t ht ht2 htN htM
    have ht' : t ∈ summands (vOpt ρ' (par M 1 37)) := by rw [hV]; exact ht
    have htM' : t < bumpW M ρ' 37 := by rw [hW]; exact htM
    have hh := hA t ht' ht2 htN htM'
    rwa [hW] at hh
  · obtain ⟨m,lc,_,_,_,_,_,_,_,_,hu⟩ := hs
    exact hu 36 (by decide)

/-- Independent of the two other false inputs: the current below-boundary
input conflicts with the repaired induction outputs themselves. -/
theorem inconsistent_below_input
    (hD : V3Main.HDropV3) (hF : WfExQ2.HFrameV3)
    (h0 : V3Main.ExpOutV3 0) (h1 : V3Main.ExpOutV3 1) (h2 : V3Main.ExpOutV3 2)
    (hBX : V3Main.T2AtV3 V3Main.T2BelowAtV3) : False := by
  obtain ⟨ρ',rk,I⟩ := V3Main.inv3V3_all hD hF h0 h1 h2 M standard (by decide) (by decide)
  have C := V3Main.ctx3 hD hF standard (by decide) (by decide) I
  have H := hBX M ρ' rk C (by decide) (by decide)
  have hh := H 39 1 (by decide) (by decide)
  exact not_t2BelowResX_of_cons I.cons I.rank hh
end Ytosk.T2AbsXFalse
