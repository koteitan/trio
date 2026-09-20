import GzD
import RFarword

namespace TRIO
namespace RFbase

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD RFarword

/-- linchpin（仮説）: 遠い語頭が Wg の子を包む。 -/
def Wrap : Prop := ∀ (w : ℕ) (X : TrioSeq), X ∈ Wg (2 * (w + 1)) → based X →
  (((1, w + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0 X) ∈ Wg (2 * (w + 1))

/-- P_u = rword 0 u (L↑) の略記の展開: mlift で 1 段上げると P_{u+1}。 -/
theorem P_step {v : ℕ} {L : List TrioSeq} (hL : ∀ X ∈ L, ∀ x ∈ X, 1 ≤ x.1) {u : ℕ} (hu : v ≤ u) :
    mlift (rword 0 u (L.map (fun X => mlift X v (u - v)))) u 1
      = rword 0 (u + 1) (L.map (fun X => mlift X v (u + 1 - v))) := by
  rw [mlift_rword u 1 _ (mlift_map_ge hL v (u - v)), map_mlift_step hu]

/-- 二重遠い語頭の語の oper は based（根 (0,w,0) 始まり、または空）。 -/
theorem based_double_oper {w : ℕ} {Q : TrioSeq} (hQ : Fr Q) (n : ℕ) :
    based ((((0, w, 0) : ℕ × ℕ × ℕ) ::
      (Q ++ [((1, w + 1, 1) : ℕ × ℕ × ℕ), ((2, w + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hP : Fr (Q ++ [((1, w + 1, 1) : ℕ × ℕ × ℕ)]) :=
      Fr_append hQ (by intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact le_rfl)
    have hc : coneV ((Q ++ [((1, w + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, w + 1, 1) : ℕ × ℕ × ℕ)]) w
        (Q ++ [((1, w + 1, 1) : ℕ × ℕ × ℕ)]).length := by
      rw [List.length_append, List.length_singleton, List.append_assoc,
        show ([((1, w + 1, 1) : ℕ × ℕ × ℕ)] ++ [((2, w + 1, 1) : ℕ × ℕ × ℕ)] : TrioSeq)
          = [((1, w + 1, 1) : ℕ × ℕ × ℕ), ((2, w + 1, 1) : ℕ × ℕ × ℕ)] from rfl]
      exact coneV_double_head hQ w
    have e := oper_zcone hP (show 1 ≤ 2 by omega) hc 0
    rw [List.append_assoc,
      show ([((1, w + 1, 1) : ℕ × ℕ × ℕ)] ++ [((2, w + 1, 1) : ℕ × ℕ × ℕ)] : TrioSeq)
        = [((1, w + 1, 1) : ℕ × ℕ × ℕ), ((2, w + 1, 1) : ℕ × ℕ × ℕ)] from rfl] at e
    rw [e]; simp only [List.range_zero, List.flatMap_nil]; exact based_nil
  · exact based_oper hn (based_cons w 0 _)

/-- GT_nest 底（W=[]）の oper 塔が Wg。linchpin Wrap を仮定。 -/
theorem farhead_base_oper (hw : Wrap) {v : ℕ} {L : List TrioSeq}
    (hL : ∀ X ∈ L, ∀ x ∈ X, 1 ≤ x.1) (hB : BwT v L) :
    ∀ (n u : ℕ), v ≤ u →
      (((0, u, 0) : ℕ × ℕ × ℕ) :: (rword 0 u (L.map (fun X => mlift X v (u - v))) ++
        [((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧ ∈ Wg (2 * u) := by
  intro n
  induction n with
  | zero =>
      intro u hu
      have hP : Fr (rword 0 u (L.map (fun X => mlift X v (u - v))) ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)]) :=
        Fr_append (Fr_rword u _) (by intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact le_rfl)
      have hc := coneV_double_head (P := rword 0 u (L.map (fun X => mlift X v (u - v)))) (Fr_rword u _) u
      have hc' : coneV ((rword 0 u (L.map (fun X => mlift X v (u - v))) ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)])
          ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)]) u
          (rword 0 u (L.map (fun X => mlift X v (u - v))) ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)]).length := by
        rw [List.length_append, List.length_singleton, List.append_assoc,
          show ([((1, u + 1, 1) : ℕ × ℕ × ℕ)] ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)] : TrioSeq)
            = [((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 1) : ℕ × ℕ × ℕ)] from rfl]
        exact hc
      have e0 := oper_zcone hP (show 1 ≤ 2 by omega) hc' 0
      rw [List.append_assoc,
        show ([((1, u + 1, 1) : ℕ × ℕ × ℕ)] ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)] : TrioSeq)
          = [((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 1) : ℕ × ℕ × ℕ)] from rfl] at e0
      rw [e0]
      simp only [List.range_zero, List.flatMap_nil]
      exact Wg_nil (2 * u)
  | succ n ih =>
      intro u hu
      have hP : Fr (rword 0 u (L.map (fun X => mlift X v (u - v))) ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)]) :=
        Fr_append (Fr_rword u _) (by intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact le_rfl)
      have hc' : coneV ((rword 0 u (L.map (fun X => mlift X v (u - v))) ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)])
          ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)]) u
          (rword 0 u (L.map (fun X => mlift X v (u - v))) ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)]).length := by
        rw [List.length_append, List.length_singleton, List.append_assoc,
          show ([((1, u + 1, 1) : ℕ × ℕ × ℕ)] ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)] : TrioSeq)
            = [((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 1) : ℕ × ℕ × ℕ)] from rfl]
        exact coneV_double_head (Fr_rword u _) u
      -- peel one level
      have hsucc := oper_zcone_succ hP (show 1 ≤ 2 by omega) hc' n
      rw [List.append_assoc,
        show ([((1, u + 1, 1) : ℕ × ℕ × ℕ)] ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)] : TrioSeq)
          = [((1, u + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1, 1) : ℕ × ℕ × ℕ)] from rfl] at hsucc
      rw [hsucc]
      -- identify the inner word as M(u+1)
      have einner : ((0, u + 1, 0) : ℕ × ℕ × ℕ) ::
          (mlift (rword 0 u (L.map (fun X => mlift X v (u - v))) ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)]) u 1
            ++ [((2, u + 1 + 1, 1) : ℕ × ℕ × ℕ)])
          = ((0, u + 1, 0) : ℕ × ℕ × ℕ) :: (rword 0 (u + 1) (L.map (fun X => mlift X v (u + 1 - v)))
              ++ [((1, u + 1 + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1 + 1, 1) : ℕ × ℕ × ℕ)]) := by
        congr 1
        rw [mlift_app (Fr_rword u _) (show Hd [((1, u + 1, 1) : ℕ × ℕ × ℕ)] from fun _ => rfl),
          P_step hL hu, mlift_one_letter u 1, List.append_assoc, List.singleton_append]
      rw [einner]
      -- IH at u+1
      have hIH := ih (u + 1) (by omega)
      have hbased : based ((((0, u + 1, 0) : ℕ × ℕ × ℕ) ::
          (rword 0 (u + 1) (L.map (fun X => mlift X v (u + 1 - v)))
            ++ [((1, u + 1 + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧) :=
        based_double_oper (w := u + 1) (Fr_rword (u + 1) _) n
      -- wrap gives R ∈ Wg
      have hwrap := hw u _ (by
        have : (2 : ℕ) * (u + 1) = 2 * (u + 1) := rfl
        exact hIH) hbased
      -- hangv
      have hA : rword 0 u (L.map (fun X => mlift X v (u - v))) ∈ Wstarv u := hB u hu
      have hR : (((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0
          ((((0, u + 1, 0) : ℕ × ℕ × ℕ) :: (rword 0 (u + 1) (L.map (fun X => mlift X v (u + 1 - v)))
            ++ [((1, u + 1 + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧))
          ∈ Wg (2 * (u + 1)) := hwrap
      have hRge : ∀ x ∈ (((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0
          ((((0, u + 1, 0) : ℕ × ℕ × ℕ) :: (rword 0 (u + 1) (L.map (fun X => mlift X v (u + 1 - v)))
            ++ [((1, u + 1 + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧)), 1 ≤ x.1 := by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact le_rfl
        · obtain ⟨p, -, rfl⟩ := mem_shiftr01.1 hx; dsimp only; omega
      have hhd : entry (((1, u + 1, 1) : ℕ × ℕ × ℕ) :: shiftr01 2 0
          ((((0, u + 1, 0) : ℕ × ℕ × ℕ) :: (rword 0 (u + 1) (L.map (fun X => mlift X v (u + 1 - v)))
            ++ [((1, u + 1 + 1, 1) : ℕ × ℕ × ℕ), ((2, u + 1 + 1, 1) : ℕ × ℕ × ℕ)]))⟦n⟧)) 0 0 ≤ 1 := by
        show 1 ≤ 1; exact le_rfl
      have hhang := hangv hA (fun x hx => rword_ge 0 u _ x hx) hR hRge hhd (2 * u) le_rfl
      rw [List.append_assoc]
      exact hhang

end RFbase
end TRIO
