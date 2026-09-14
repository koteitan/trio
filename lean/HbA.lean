/-
HbA.lean: tools/gen_gyk.py が生成。錨の列つきの子の述語で証明するシート行。
-/
import GzJ
import GzS
import HaJ
import HaL
import HaP
import HaT
import HaV
import HaZ

namespace TRIO
namespace HbA

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzJ GzM GzN GzP GzS GzU GzV GzW GzY HaA HaC HaD HaE HaF HaG HaJ HaL HaN HaP HaR HaS HaT HaV HaZ

/-- ★ シート行 1515。 -/
theorem R1515_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_tieTie (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_TowP (Q := HaZ.QP (HaZ.QP HaZ.QNil)) (TowP_QP (TowP_QP TowP_nil)) (A := []) (o := 1) (by decide) (by decide) (by decide) 0)))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil] using h

/-- ★ シート行 1516。 -/
theorem R1516_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 3, 0), (4, 3, 1), (5, 3, 1), (5, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_tieTie (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_TowP (Q := HaZ.QP (HaZ.QP HaZ.QNil)) (TowP_QP (TowP_QP TowP_nil)) (A := []) (o := 1) (by decide) (by decide) (by decide) 0)) (GPF_of_PVF (PVF_TowP (Q := HaZ.QP (HaZ.QP HaZ.QNil)) (TowP_QP (TowP_QP TowP_nil)) (A := []) (o := 2) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil] using h

/-- ★ シート行 1517。 -/
theorem R1517_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_tieTie (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_TowP (Q := HaZ.QP (HaZ.QP HaZ.QNil)) (TowP_QP (TowP_QP TowP_nil)) (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil] using h

/-- ★ シート行 1518。 -/
theorem R1518_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (6, 3, 0), (5, 3, 1), (6, 3, 1), (6, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_tieTie (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_TowP (Q := HaZ.QP (HaZ.QP HaZ.QNil)) (TowP_QP (TowP_QP TowP_nil)) (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_TowP (Q := HaZ.QP (HaZ.QP HaZ.QNil)) (TowP_QP (TowP_QP TowP_nil)) (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil] using h

/-- ★ シート行 1519。 -/
theorem R1519_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1), (6, 3, 0), (5, 3, 1), (6, 3, 1), (6, 3, 0), (5, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_tieTie (v := 0) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_TowP (Q := HaZ.QP (HaZ.QP HaZ.QNil)) (TowP_QP (TowP_QP TowP_nil)) (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_snoc (A := [1]) (o := 2) (by decide) (PVF_TowP (Q := HaZ.QP (HaZ.QP HaZ.QNil)) (TowP_QP (TowP_QP TowP_nil)) (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0) (RLF_nil (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self, HaL.PfF, HaI.towF, HaI.Pf, HaN.QFn, HaN.QF, HaN.towQ, HaN.Lw, List.replicate, HaZ.QP, HaZ.QNil] using h

end HbA
end TRIO
