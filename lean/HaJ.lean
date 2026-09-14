/-
HaJ.lean: 行 1489 の形 [W_tie, W_far]（子のないタイで終わる遠い語のあとに中身なしの遠い語）を、最上段の全ての段 u で示す（BwT）。

    BwT_tieFar v : BwT v [fwTop v [none], fwTop v []]
    starOK_tieFar : そのあとに TF の語の並び（WordsG）が続いてよい（BwT_append_words）。
-/
import HaI

namespace TRIO
namespace HaJ

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaD HaE HaF HaG HaI

theorem topTF_Wg (u m : ℕ) : (((0, u, 0) : ℕ × ℕ × ℕ) :: towF (u + 1) m) ∈ Wg (2 * u) := by
  cases m with
  | zero =>
      have h := Wg_of_starOK (starOK_topFarTie (v := u) ([] : List (List (Option TrioSeq)))
        (RawUs_nil u) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil u) (by simp [NoTie])
        (WordsG_consT (v := u) (TF_nil u) (WordsG_nil u)))
      simpa [shiftr01, rword, rcol, unitsC, unitC, fwTop, towF, Pf] using h
  | succ m =>
      have hG := towF_GpT m [] 1 (fun _ => 0) u (by simp) (by simp) le_rfl
      rw [liftOff_zeroF] at hG
      have h := Wg_of_starOK (starOK_topFarTie (v := u) ([] : List (List (Option TrioSeq)))
        (RawUs_nil u) (by simp [NoTie]) ([] : List (Option TrioSeq)) (RawU_nil u) (by simp [NoTie])
        (WordsG_consT (v := u) (TF_tieG (u := u) (TF_nil u) (GF_of_GPF ⟨hG, Fr_towF m _⟩))
          (WordsG_nil u)))
      simpa [shiftr01, rword, rcol, unitsC, unitC, fwTop, towF, Pf] using h

theorem tieFar_Wstarv (u : ℕ) : towF (u + 1) 0 ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)] ∈ Wstarv u := by
  simp only [Wstarv, Set.mem_setOf_eq]
  intro _ a ha
  obtain ⟨hP, hc⟩ := towF0_P u
  refine A1g_intro (Or.inr (Or.inl ⟨zcone_natDom hP (show 1 ≤ 2 by omega) hc, fun k hk => ?_⟩))
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [oper_zcone hP (show 1 ≤ 2 by omega) hc (m + 1), towF_flat m u]
  exact Wg_mono ha (topTF_Wg u m)

/-- ★ 行 1489 の形は最上段の全ての段で良い。 -/
theorem BwT_tieFar (v : ℕ) : BwT v [fwTop v [none], fwTop v []] := by
  intro u hu
  have e : rword 0 u ([fwTop v [none], fwTop v []].map (fun X => mlift X v (u - v)))
      = towF (u + 1) 0 ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)] := by
    rw [List.map_cons, List.map_cons, List.map_nil, mlift_fwTop (RawU_cons_none (RawU_nil v)),
      mlift_fwTop (RawU_nil v), show v + (u - v) = u by omega]
    simp [rword, rcol, fwTop, unitsC, unitC, towF, Pf, shiftr01]
  rw [e]
  exact tieFar_Wstarv u

/-- ★ [W_tie, W_far] のあとに TF の語の並び。 -/
theorem starOK_tieFar {v : ℕ} {Ls : List TrioSeq} (hW : WordsG v Ls) :
    StarOK v (rword 0 v ([fwTop v [none], fwTop v []] ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hFr : ∀ X ∈ [fwTop v [none], fwTop v []], ∀ x ∈ X, 1 ≤ x.1 := by
    intro X hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl <;> exact Fr_fwTop v _
  have hB := BwT_append_words hFr (BwT_tieFar v) Ls hW v le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

end HaJ
end TRIO
