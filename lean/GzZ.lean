/-
GzZ.lean: tools/gen_gyk.py が生成。錨の列つきの子の述語で証明するシート行。
-/
import GzJ
import GzS
import GzY

namespace TRIO
namespace GzZ

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI GzJ GzM GzN GzP GzS GzU GzV GzW GzY

/-- ★ シート行 1467。 -/
theorem R1467_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farW_Fr (o := 1) (by decide) le_rfl (fun k hk => (OkWsk_nil k 0)) (fun k hk => (okWkF_nil k 0)))) (GPF_of_PVF (PVF_farW_Fr (o := 2) (by decide) le_rfl (fun k hk => (OkWsk_nil k 0)) (fun k hk => (okWkF_nil k 0))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

/-- ★ シート行 1468。 -/
theorem R1468_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 3, 0), (4, 3, 0), (5, 4, 1), (6, 4, 1), (6, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farW_Fr (o := 1) (by decide) le_rfl (fun k hk => (OkWsk_nil k 0)) (fun k hk => (okWkF_nil k 0)))) (GPF_node (A := []) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [] (by decide) (GPF_of_PVF (PVF_farW_Fr (o := 2) (by decide) le_rfl (fun k hk => (OkWsk_nil k 0)) (fun k hk => (okWkF_nil k 0)))) (GPF_of_PVF (PVF_farWsk (A := []) (o := 3) (by decide) (by decide) (by decide) (by decide) (by decide) 0 _ (OkWsk_cons le_rfl (okWkF_node (k := 3) (τ := 3) (by decide) (by decide) (okWkF_nil 3 0) (GPF_nil (A := []) (o := 3) (by decide) (by decide) 0)) (OkWsk_nil 3 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

/-- ★ シート行 1469。 -/
theorem R1469_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 3, 0), (4, 3, 0), (5, 4, 1), (6, 4, 1), (6, 3, 0), (5, 4, 1), (6, 4, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farW_Fr (o := 1) (by decide) le_rfl (fun k hk => (OkWsk_nil k 0)) (fun k hk => (okWkF_nil k 0)))) (GPF_node (A := []) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [] (by decide) (GPF_of_PVF (PVF_farW_Fr (o := 2) (by decide) le_rfl (fun k hk => (OkWsk_nil k 0)) (fun k hk => (okWkF_nil k 0)))) (GPF_of_PVF (PVF_farWsk (A := []) (o := 3) (by decide) (by decide) (by decide) (by decide) (by decide) 0 _ (OkWsk_cons le_rfl (okWkF_node (k := 3) (τ := 3) (by decide) (by decide) (okWkF_nil 3 0) (GPF_nil (A := []) (o := 3) (by decide) (by decide) 0)) (OkWsk_cons le_rfl (okWkF_nil 3 0) (OkWsk_nil 3 0))))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

/-- ★ シート行 1470。 -/
theorem R1470_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 3, 0), (4, 3, 0), (5, 4, 1), (6, 4, 1), (6, 3, 0), (6, 3, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farW_Fr (o := 1) (by decide) le_rfl (fun k hk => (OkWsk_nil k 0)) (fun k hk => (okWkF_nil k 0)))) (GPF_node (A := []) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [] (by decide) (GPF_of_PVF (PVF_farW_Fr (o := 2) (by decide) le_rfl (fun k hk => (OkWsk_nil k 0)) (fun k hk => (okWkF_nil k 0)))) (GPF_of_PVF (PVF_farWsk (A := []) (o := 3) (by decide) (by decide) (by decide) (by decide) (by decide) 0 _ (OkWsk_cons le_rfl (okWkF_node (k := 3) (τ := 3) (by decide) (by decide) (okWkF_node (k := 3) (τ := 3) (by decide) (by decide) (okWkF_nil 3 0) (GPF_nil (A := []) (o := 3) (by decide) (by decide) 0)) (GPF_nil (A := []) (o := 3) (by decide) (by decide) 0)) (OkWsk_nil 3 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

/-- ★ シート行 1471。 -/
theorem R1471_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 0), (4, 3, 1), (5, 3, 1), (5, 3, 0), (4, 3, 0), (5, 4, 1), (6, 4, 1), (6, 4, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_node (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [] (by decide) (GPF_of_PVF (PVF_farW_Fr (o := 1) (by decide) le_rfl (fun k hk => (OkWsk_nil k 0)) (fun k hk => (okWkF_nil k 0)))) (GPF_node (A := []) (o := 2) (by decide) (by decide) (by decide) (b := 0) (τ := 3) [] (by decide) (GPF_of_PVF (PVF_farW_Fr (o := 2) (by decide) le_rfl (fun k hk => (OkWsk_nil k 0)) (fun k hk => (okWkF_nil k 0)))) (GPF_of_PVF (PVF_farW_Fr (o := 3) (by decide) le_rfl (fun k hk => (OkWsk_nil k 0)) (fun k hk => (okWkF_nil k 0)))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

/-- ★ シート行 1472。 -/
theorem R1472_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farW_Fr (o := 1) (by decide) le_rfl (fun k hk => (OkWsk_nil k 0)) (fun k hk => (okWkF_nil k 0))) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

/-- ★ シート行 1473。 -/
theorem R1473_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 1), (3, 2, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farW_Fr (o := 1) (by decide) le_rfl (fun k hk => (OkWsk_nil k 0)) (fun k hk => (okWkF_nil k 0))) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0)) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

/-- ★ シート行 1474。 -/
theorem R1474_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 1), (2, 1, 0), (1, 1, 1), (2, 1, 0), (3, 2, 1), (4, 2, 1), (4, 2, 0), (3, 2, 1), (4, 2, 0), (5, 3, 1), (6, 3, 1)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_topFarTie (v := 0) ([] : List (List (Option TrioSeq))) (RawUs_nil 0) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil 0) (by simp [NoTie]) (WordsG_consT (v := 0) (TF_tieG (u := 0) (TF_nil 0) (GF_of_GPF (GPF_of_PVF (PVF_snoc (A := []) (o := 1) (by decide) (PVF_farW_Fr (o := 1) (by decide) le_rfl (fun k hk => (OkWsk_nil k 0)) (fun k hk => (okWkF_nil k 0))) (RLF_child (A := []) (o := 1) (by decide) (by decide) (by decide) (b := 0) (τ := 2) [1] (by decide) (by decide) (RLF_nil (A := []) (o := 1) (by decide) (by decide) (by decide) 0) (GPF_of_PVF (PVF_farU (A := [1]) (o := 2) (by decide) (by decide) (by decide) 0 ([([] : List (Option TrioSeq))] : List (List (Option TrioSeq))) (RawUs_cons (RawU_nil 0) (RawUs_nil 0))))))))) (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol, farR, farU, fwU, unitsC, unitC, fwTop, farW, fwW, mlift_zero, Nat.sub_self] using h

end GzZ
end TRIO
