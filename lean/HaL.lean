/-
HaL.lean: F の語のあとに中身なしの遠い語（全ての級 (A, o, f)）。

    towF r 0 ++ [(2, r, 1)] = (1,r,1)(2,r,1)(2,r,0) (1,r,1)(2,r,1)     （r = b + liftOff f A o + 1）

最後の遠い字の潰れの展開は HaI の F の語の塔 towF そのもの（towF_flat）で、塔の良さは towF_GpT。
証明は GzU.farWk_collapse と同じ形（接頭辞を F の語に、塔を towF に替える）。
-/
import GzJ
import HaI

namespace TRIO
namespace HaL

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaD HaE HaF HaG HaI

/-- F の語のあとに中身なしの遠い語。 -/
def PfF (r : ℕ) : TrioSeq := towF r 0 ++ [((2, r, 1) : ℕ × ℕ × ℕ)]

theorem PfF_eq (r : ℕ) :
    PfF r = Pf r ++ ((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 [((1, r, 1) : ℕ × ℕ × ℕ)] := by
  simp [PfF, towF, shiftr01]

theorem Fr_PfF (r : ℕ) : Fr (PfF r) := by
  rw [PfF_eq]; exact Fr_append (Fr_Pf r) (Fr_letter _ _)

theorem mlift_PfF {v r : ℕ} (hvr : v < r) (t : ℕ) : mlift (PfF r) v t = PfF (r + t) := by
  rw [PfF_eq, PfF_eq, mlift_app (Fr_Pf r) (Hd_letter _ _), mlift_Pf hvr t,
    mlift_letter hvr (GzF.Fr_single le_rfl _ _) t, mlift_one hvr]

theorem reliftX_PfF {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (b : ℕ) (f g : ℕ → ℕ) :
    reliftX b f g A (PfF (b + liftOff f A o + 1)) = PfF (b + liftOff (addF f g) A o + 1) := by
  have hlow : lowP f A (liftOff f A o + 1) = A :=
    lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
  have hnode : reliftX b f g A [((1, b + (liftOff f A o + 1), 1) : ℕ × ℕ × ℕ)]
      = [((1, b + (liftOff (addF f g) A o + 1), 1) : ℕ × ℕ × ℕ)] := by
    have := reliftX_node (V := []) Fr_nil b (liftOff f A o + 1) 1 f g A
    rw [hlow, reOff_above hA f g 1] at this
    simpa [shiftr01, reliftX, slift_nil] using this
  rw [PfF_eq, PfF_eq, reliftX_app (Fr_Pf _) (Hd_letter _ _), reliftX_Pf hA b f g,
    show b + liftOff f A o + 1 = b + (liftOff f A o + 1) by omega,
    reliftX_node (GzF.Fr_single le_rfl _ _) b (liftOff f A o + 1) 1 f g A, hlow, reOff_above hA f g 1,
    hnode]
  simp only [← Nat.add_assoc]

/-- ★ F の語のあとに中身なしの遠い語は、全ての級で良い。 -/
theorem GpT_PfF {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (f : ℕ → ℕ) (b : ℕ) : GpT A o f b (PfF (b + liftOff f A o + 1)) := by
  refine GpT_intro hA (fun R hR' g => ?_)
  rw [reliftX_PfF hA b f g]
  obtain ⟨F, hF⟩ : ∃ F, F = addF f g := ⟨_, rfl⟩
  obtain ⟨kk, hkk⟩ : ∃ kk, kk = liftOff F A o := ⟨_, rfl⟩
  rw [← hF, ← hkk]
  have hk1 : o ≤ kk := by rw [hkk]; unfold liftOff; omega
  intro u' hu X hX hRX
  rw [mlift_PfF (show b < b + kk + 1 by omega) (u' - b), show b + kk + 1 + (u' - b) = u' + kk + 1 by omega]
  obtain ⟨c, hc⟩ : ∃ c, c = u' + kk := ⟨_, rfl⟩
  rw [← hc]
  obtain ⟨hP, hcone⟩ := towF0_P c
  obtain ⟨U0, hU0⟩ : ∃ U0 : TrioSeq, U0 = ((0, c, 0) : ℕ × ℕ × ℕ) ::
      (towF (c + 1) 0 ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)]) := ⟨_, rfl⟩
  have eU : ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (PfF (c + 1)) = shiftr01 1 0 U0 := by
    rw [hU0, PfF]; simp [shiftr01]
  rw [eU]
  have hlen : 2 ≤ U0.length := by rw [hU0]; simp
  have hpV : hasParent U0 (srow U0 (U0.length - 1)) (U0.length - 1) := by
    have hn := zcone_natDom hP (show 1 ≤ 2 by omega) hcone
    rw [← hU0] at hn
    rcases natDom_iff.mp hn with h | h
    · exfalso
      have hl : U0.length - 1 = (((0, c, 0) : ℕ × ℕ × ℕ) :: towF (c + 1) 0).length + 0 := by
        rw [hU0]; simp
      rw [hl] at h
      unfold lev at h
      rw [hU0, show ((0, c, 0) : ℕ × ℕ × ℕ) :: (towF (c + 1) 0 ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)])
          = (((0, c, 0) : ℕ × ℕ × ℕ) :: towF (c + 1) 0) ++ [((2, c + 1, 1) : ℕ × ℕ × ℕ)] by simp,
        entry_append_right, entry_append_right] at h
      simp [entry] at h
    · exact h
  refine (hR' F).1.oper u' X (shiftr01 1 0 U0) hX (Fr_shift1 U0)
    (fun _ => by rw [entry0_shiftr01 (by rw [hU0]; simp), hU0]; rfl)
    (by rw [shiftr01_length]; exact hlen)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpV) (fun m hm => ?_)
  have eO := oper_shift [] U0 1 m hlen hpV
  simp only [List.nil_append] at eO
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [eO, hU0, oper_zcone hP (show 1 ≤ 2 by omega) hcone (m' + 1), towF_flat m' c]
  have eS : shiftr01 1 0 (((0, c, 0) : ℕ × ℕ × ℕ) :: towF (c + 1) m')
      = ((1, c, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towF (c + 1) m') := by
    simp [shiftr01]
  rw [eS]
  have hD := towF_GpT m' A o F u' hA hA1 ho
  rw [← hkk, show u' + kk + 1 = c + 1 by omega] at hD
  have h := GpT_elim0 hD hR'
  rw [← hkk] at h
  have := h u' le_rfl X hX hRX
  rwa [Nat.sub_self, mlift_zero, ← hc] at this

/-- ★ 語の述語（全ての列が節点の段より上なので t の持ち上げで一緒に動く）。 -/
theorem PVF_PfF {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (b : ℕ) : PVF A o b (PfF (b + o + 1)) := by
  refine ⟨fun t => ?_, Fr_PfF _⟩
  rw [liftOff_zeroF, mlift_PfF (show b + o < b + o + 1 by omega) t]
  have := GpT_PfF (A := A) (o := o + t) (fun a ha => by have := hA a ha; omega) hA1 (by omega)
    (fun _ => 0) b
  rwa [liftOff_zeroF, show b + (o + t) + 1 = b + o + 1 + t by omega] at this

end HaL
end TRIO
