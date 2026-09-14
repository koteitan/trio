/-
HdV.lean: 生成器のための形。木の単位の語の並び（CLT）のあとに最後の語 K、そのあとに TF の語の並び。

- starOK_lastTL: StarOK v (rword 0 v (ps.map (wLT v) ++ [K] ++ Ls))（K は GTC CLT、Ls は WordsG）。
- starOK_N2: K が F のタイの子の木のあとに 2 段上の節点を置いた語（HdU.GTC_N2）。
- TRaws_* / RawssT_*: 生成する項のための木の生の条件の組み立て。
-/
import HdU

namespace TRIO
namespace HdV

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HbU HbV HbX HcA HcI HcM
open HdA HdQ HdR HdS HdU

theorem TRaws_nil (v : ℕ) : TRaws v [] := trivial

theorem TRaws_cons_ch {v : ℕ} {Z : TrioSeq} (hZ : Z ∈ Wg (2 * v)) (hb : based Z) {us : List UT}
    (h : TRaws v us) : TRaws v (UT.ch Z :: us) := ⟨⟨hZ, hb⟩, h⟩

theorem TRaws_cons_tie {v : ℕ} {cs : List UT} (hc : TRaws v cs) {us : List UT} (h : TRaws v us) :
    TRaws v (UT.tie cs :: us) := ⟨hc, h⟩

theorem RawssT_nil (v : ℕ) : ∀ us ∈ ([] : List (List UT)), TRaws v us := fun _ h => by simp at h

theorem RawssT_cons {v : ℕ} {us : List UT} {Uss : List (List UT)} (h1 : TRaws v us)
    (h2 : ∀ us' ∈ Uss, TRaws v us') : ∀ us' ∈ us :: Uss, TRaws v us' := by
  intro us' h
  rcases List.mem_cons.mp h with rfl | h
  · exact h1
  · exact h2 us' h

/-- ★ 木の単位の語の並びのあとに最後の語 K と TF の語の並び。 -/
theorem starOK_lastTL {v : ℕ} (ps : List (List (List UT) × List (Option TrioSeq))) (h : PsLT v ps)
    {K : TrioSeq} (hK : GTC CLT v K) (hKF : ∀ x ∈ K, 1 ≤ x.1) {Ls : List TrioSeq} (hW : WordsG v Ls) :
    StarOK v (rword 0 v (ps.map (wLT v) ++ [K] ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hB0 := hK _ ⟨ps, h, rfl⟩ (Fr_CLT v ps) (BwT_CLT v ps h)
  have hL : ∀ X ∈ ps.map (wLT v) ++ [K], ∀ x ∈ X, 1 ≤ x.1 := by
    intro X hX
    rcases List.mem_append.mp hX with hX | hX
    · exact Fr_CLT v ps X hX
    · simp at hX; subst hX; exact hKF
  have hB := BwT_append_words hL hB0 Ls hW v le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

theorem Fr_N2 (v : ℕ) (Uss : List (List UT)) (us : List UT) :
    ∀ x ∈ wLT v (Uss ++ [us], []) ++ [((2, v + 2, 0) : ℕ × ℕ × ℕ)], 1 ≤ x.1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact Fr_wLT v _ x hx
  · simp at hx; subst hx; show 1 ≤ 2; omega

/-- ★ 木の単位の語の並びのあとに、F のタイの子の木と 2 段上の節点の語、そのあとに TF の語の並び。 -/
theorem starOK_N2 {v : ℕ} (ps : List (List (List UT) × List (Option TrioSeq))) (h : PsLT v ps)
    {Uss : List (List UT)} (hU : ∀ us ∈ Uss, TRaws v us) {us : List UT} (hus : TRaws v us)
    {Ls : List TrioSeq} (hW : WordsG v Ls) :
    StarOK v (rword 0 v (ps.map (wLT v) ++ [wLT v (Uss ++ [us], []) ++ [((2, v + 2, 0) : ℕ × ℕ × ℕ)]] ++ Ls)) :=
  starOK_lastTL ps h (GTC_N2 hU hus) (Fr_N2 v Uss us) hW

end HdV
end TRIO
