/-
KxF.lean: κ の族の FarP の中身の移し替え（CT）。

語の段の文脈の h1 / h2 が要る中身（状態の持ち上げ S ++ A、基準の持ち上げ、語の上の mlift をかけた klift）は、
族 UK の h1 が与える中身（(o :: A) の持ち上げ g + G_A）を、ある κ で klift したもの。
-/
import KxE

namespace TRIO
namespace KxF

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzB KxA KxB KxC KxD KxE KlA KlB KlE KlG KlH

theorem maskF_not_mem {A : List ℕ} {G : ℕ → ℕ} {x : ℕ} (hx : x ∉ A) : maskF A G x = 0 := by
  unfold maskF; rw [if_neg hx]

theorem upperF_not_mem {A : List ℕ} {G : ℕ → ℕ} {x : ℕ} (hx : x ∉ A) : upperF A G x = G x := by
  unfold upperF; rw [if_neg hx]

theorem upperF_mem {A : List ℕ} {G : ℕ → ℕ} {x : ℕ} (hx : x ∈ A) : upperF A G x = 0 := by
  unfold upperF; rw [if_pos hx]

/-- ★ 中身の移し替え。 -/
theorem content_transport {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (ho : 1 ≤ o)
    {H g F K G : ℕ → ℕ} {S : List ℕ} {j b b' b3 t : ℕ} {P : TrioSeq}
    (hS : ∀ s ∈ S, o + addF H g o ≤ s ∧ s < o + addF H g o + j)
    (hF : ∀ a ∈ A, F a = addF H g a) (hb : b ≤ b') (hb3 : b' ≤ b3) :
    ∃ K2, reliftX b3 F G (S ++ A)
        (mlift (mlift (klift (reliftX b' H g (o :: A) (mlift P b (b' - b)))
          (b' + liftOff (addF H g) A (o + addF H g o)) (j + sumOn F S) K)
          (b' + liftOff (addF H g) A (o + addF H g o) + (j + sumOn F S)) t) b' (b3 - b'))
      = klift (reliftX b3 H (addF g (maskF A G)) (o :: A) (mlift P b (b3 - b)))
          (b3 + liftOff (addF F (maskF A G)) A (o + addF H g o)) ((j + t) + sumOn (addF F G) S) K2 := by
  classical
  obtain ⟨o', ho'⟩ : ∃ o', o' = o + addF H g o := ⟨_, rfl⟩
  rw [← ho'] at hS ⊢
  have hAo' : ∀ a ∈ A, a < o' := fun a ha => by have := hA a ha; omega
  have hS0 : ∀ s ∈ S, o' ≤ s := fun s hs => (hS s hs).1
  have hSA : ∀ s ∈ S, s ∉ A := fun s hs ha => by have := hS0 s hs; have := hAo' s ha; omega
  have hkF : liftOff (addF H g) A o' = liftOff F A o' := liftOff_congrA (fun a ha => (hF a ha).symm)
  rw [hkF]
  obtain ⟨k, hk⟩ : ∃ k, k = liftOff F A o' := ⟨_, rfl⟩
  rw [← hk]
  have hk1 : 1 ≤ k := by rw [hk]; unfold liftOff; omega
  obtain ⟨J, hJ⟩ : ∃ J, J = j + sumOn F S := ⟨_, rfl⟩
  rw [← hJ]
  -- (1) 上の mlift と (2) 基準の持ち上げ
  rw [mlift_klift_top, KlD.klift_mlift_low (show b' < b' + k by omega),
    show b' + k + (b3 - b') = b3 + k by omega]
  -- (3) 状態の持ち上げを分ける
  rw [reliftX_split hAo' hS0 b3 F G]
  -- (4) A の部分
  rw [KlD.klift_reliftX (f := F) (g := maskF A G) (A := A) (o := k)
      (fun a ha => by rw [hk]; exact liftVal_lt_liftOff hAo' ha),
    reStair_base]
  have hre : reOff F (maskF A G) A k = liftOff (addF F (maskF A G)) A o' := by
    have := reOff_above hAo' F (maskF A G) 0
    simp only [Nat.add_zero] at this
    rw [hk]; exact this
  rw [hre]
  -- (5) S の部分（帯）
  have hS' : ∀ s ∈ S, o' ≤ s ∧ s < o' + (j + t) := fun s hs => by have := hS s hs; omega
  have hband := band_reStair hAo' hS' b3 (addF F (maskF A G)) (upperF A G)
    (fun a ha => upperF_mem ha)
  have hsumS : sumOn (addF F (maskF A G)) S = sumOn F S :=
    sumOn_congr (fun s hs => by unfold addF; rw [maskF_not_mem (hSA s hs)]; rfl)
  rw [hsumS, show j + t + sumOn F S = J + t by omega] at hband
  rw [show ∀ (Y : TrioSeq) (KK : ℕ → ℕ), reliftX b3 (addF F (maskF A G)) (upperF A G) (S ++ A)
        (klift Y (b3 + liftOff (addF F (maskF A G)) A o') (J + t) KK)
      = klift Y (b3 + liftOff (addF F (maskF A G)) A o') (J + t + sumOn (upperF A G) S)
          (bandK (b3 + liftOff (addF F (maskF A G)) A o') (J + t)
            (reStair b3 (addF F (maskF A G)) (upperF A G) (S ++ A)) KK)
      from fun Y KK => klift_slift_band (reStair_stair _ _ _ _) hband.1 hband.2]
  -- (6) 中身を (o :: A) の持ち上げに合成する
  have eP1 : mlift (reliftX b' H g (o :: A) (mlift P b (b' - b))) b' (b3 - b')
      = reliftX b3 H g (o :: A) (mlift P b (b3 - b)) := by
    rw [mlift_reliftX, show b' + (b3 - b') = b3 by omega]
    have e := mlift_mlift P b (b' - b) (b3 - b')
    rw [show b + (b' - b) = b' by omega, show b' - b + (b3 - b') = b3 - b by omega] at e
    rw [e]
  have eA : reliftX b3 F (maskF A G) A (mlift (reliftX b' H g (o :: A) (mlift P b (b' - b))) b' (b3 - b'))
      = reliftX b3 H (addF g (maskF A G)) (o :: A) (mlift P b (b3 - b)) := by
    rw [eP1, ← reliftX_comp]
    have hm0 : ∀ s ∈ [o], maskF A G s = 0 := fun s hs => by
      simp only [List.mem_singleton] at hs
      subst hs
      exact maskF_not_mem (fun ha => by have := hA _ ha; omega)
    have e1 := reliftX_ins (S := [o]) hA (fun s hs => by simp at hs; omega) b3 (addF H g) (maskF A G)
      hm0 (reliftX b3 H g (o :: A) (mlift P b (b3 - b)))
    simp only [List.singleton_append] at e1
    rw [e1]
    exact reliftX_congr b3 hF (fun _ _ => rfl) _
  rw [eA]
  have hG : sumOn (upperF A G) S = sumOn G S :=
    sumOn_congr (fun s hs => upperF_not_mem (hSA s hs))
  have hJt : J + t + sumOn (upperF A G) S = j + t + sumOn (addF F G) S := by
    rw [hG, sumOn_addF]; omega
  rw [hJt]
  exact ⟨_, rfl⟩

end KxF
end TRIO
