/-
PmF.lean: 木のクラス TX（深い節点の鎖つき）で出るシートの行（行1695〜1702）。
-/
import PmE

namespace TRIO
namespace PmF

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HbU HbV HbX HcA HcI HcM
open HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdQ HeK
open PmD PmE

/-! ## TX の組み立て -/

theorem TX_up1 {v : ℕ} {cs : List UT} (h : TX v 1 false cs) : TX v 0 true [UT.tie 1 cs] := by
  simpa using TX.up (TX.nil (v := v) 0 true) (by omega : 0 < 0 + 1) h

theorem TX_same1 {v : ℕ} {us cs : List UT} (hu : TX v 1 false us) (hc : TX v 1 false cs) :
    TX v 1 false (us ++ [UT.tie 1 cs]) := TX.same (l := 0) hu hc

theorem TX_one1 {v : ℕ} {cs : List UT} (hc : TX v 1 false cs) : TX v 1 false [UT.tie 1 cs] := by
  simpa using TX_same1 (TX.nil (v := v) 1 false) hc

theorem TX_tie0E {v p : ℕ} {cl : Bool} {us : List UT} (hu : TX v p cl us) : TX v p cl (us ++ [UT.tie 0 []]) :=
  TX.tie0 hu (TX.nil (v := v) 0 true)

theorem Wg0_single : ([((0, 0, 0) : ℕ × ℕ × ℕ)] : TrioSeq) ∈ Wg 0 :=
  A1g_intro (Or.inl ⟨by simp, by simp [lev, entry]⟩)

/-! ## 行 -/

/-- ★ シート行 1695 = (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(4,2,0) ∈ W 0。 -/
theorem R1695 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(4,2,0)] : TrioSeq) ∈ W 0 := by
  have hx : TX 0 0 true [UT.tie 1 [UT.tie 1 [], UT.tie 1 []]] := by
    simpa using TX_up1 (TX_same1 (TX_one1 (TX.nil (v := 0) 1 false)) (TX.nil (v := 0) 1 false))
  have h := W0_of_X _ hx
  simpa [rword, rcol, wLT, FTL0, topTs, topT, unitsC, shiftr01] using h

/-- ★ シート行 1696 = (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(4,2,0)(4,2,0) ∈ W 0。 -/
theorem R1696 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(4,2,0),(4,2,0)] : TrioSeq) ∈ W 0 := by
  have hx : TX 0 0 true [UT.tie 1 [UT.tie 1 [], UT.tie 1 [], UT.tie 1 []]] := by
    simpa using TX_up1 (TX_same1 (TX_same1 (TX_one1 (TX.nil (v := 0) 1 false)) (TX.nil (v := 0) 1 false))
      (TX.nil (v := 0) 1 false))
  have h := W0_of_X _ hx
  simpa [rword, rcol, wLT, FTL0, topTs, topT, unitsC, shiftr01] using h

/-- ★ シート行 1697 = (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(5,0,0) ∈ W 0。 -/
theorem R1697 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(5,0,0)] : TrioSeq) ∈ W 0 := by
  have hx : TX 0 0 true [UT.tie 1 [UT.tie 1 [UT.ch [((0, 0, 0) : ℕ × ℕ × ℕ)]]]] := by
    have hc : TX 0 1 false [UT.ch [((0, 0, 0) : ℕ × ℕ × ℕ)]] := by
      simpa using TX.ch (TX.nil (v := 0) 1 false) Wg0_single (by simp [based, entry])
    exact TX_up1 (TX_one1 hc)
  have h := W0_of_X _ hx
  simpa [rword, rcol, wLT, FTL0, topTs, topT, unitsC, shiftr01] using h

theorem TX_1698 : TX 0 0 true [UT.tie 1 [UT.tie 1 [UT.tie 0 []]]] := by
  simpa using TX_up1 (TX_one1 (by simpa using TX_tie0E (TX.nil (v := 0) 1 false)))

/-- ★ シート行 1698 = (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(5,1,0) ∈ W 0。 -/
theorem R1698 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(5,1,0)] : TrioSeq) ∈ W 0 := by
  have h := W0_of_X _ TX_1698
  simpa [rword, rcol, wLT, FTL0, topTs, topT, unitsC, shiftr01] using h

/-- ★ シート行 1699 = (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(5,1,0)(1,1,1) ∈ W 0。 -/
theorem R1699 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(5,1,0),(1,1,1)] : TrioSeq) ∈ W 0 := by
  have hS := starOK_X [[UT.tie 1 [UT.tie 1 [UT.tie 0 []]]]] (fun us h => by simp at h; subst h; exact TX_1698)
    [] (by simp [GzJ.NoTie]) (RawU_nil 0) [] (PsLTL_nil 0) (Ls := [([] : TrioSeq)])
    (WordsG_consT (TF_nil 0) (WordsG_nil 0))
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK hS)
  simpa [rword, rcol, wLT, FTL0, topTs, topT, unitsC, shiftr01] using h

/-- ★ シート行 1700 = (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(5,1,0)(1,1,1)(2,1,1) ∈ W 0。 -/
theorem R1700 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(5,1,0),(1,1,1),(2,1,1)] : TrioSeq) ∈ W 0 := by
  have hS := starOK_X [[UT.tie 1 [UT.tie 1 [UT.tie 0 []]]]] (fun us h => by simp at h; subst h; exact TX_1698)
    [] (by simp [GzJ.NoTie]) (RawU_nil 0) [PmA.p0]
    (PsLTL_cons (fun _ h => by simp at h) (by simp [GzJ.NoTie]) (RawU_nil 0) (PsLTL_nil 0))
    (WordsG_nil 0)
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK hS)
  simpa [rword, rcol, wLT, FTL0, topTs, topT, unitsC, shiftr01, PmA.p0] using h

/-- ★ シート行 1701 = (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(5,2,0) ∈ W 0。 -/
theorem R1701 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(5,2,0)] : TrioSeq) ∈ W 0 := by
  have hx : TX 0 0 true [UT.tie 1 [UT.tie 1 [UT.tie 1 []]]] :=
    TX_up1 (TX_one1 (TX_one1 (TX.nil (v := 0) 1 false)))
  have h := W0_of_X _ hx
  simpa [rword, rcol, wLT, FTL0, topTs, topT, unitsC, shiftr01] using h

/-- ★ シート行 1702 = (0,0,0)(1,1,1)(2,1,1)(2,1,0)(3,2,0)(4,2,0)(5,2,0)(6,2,0) ∈ W 0。 -/
theorem R1702 : ([(0,0,0),(1,1,1),(2,1,1),(2,1,0),(3,2,0),(4,2,0),(5,2,0),(6,2,0)] : TrioSeq) ∈ W 0 := by
  have hx : TX 0 0 true [UT.tie 1 [UT.tie 1 [UT.tie 1 [UT.tie 1 []]]]] :=
    TX_up1 (TX_one1 (TX_one1 (TX_one1 (TX.nil (v := 0) 1 false))))
  have h := W0_of_X _ hx
  simpa [rword, rcol, wLT, FTL0, topTs, topT, unitsC, shiftr01] using h

end PmF
end TRIO
