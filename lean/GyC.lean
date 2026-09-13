/-
GyC.lean: GpT の導入の向き、差し込み口の公理 SlotAx、状態の合同、持ち上げで閉じる性質。
-/
import GyB

namespace TRIO
namespace GyC

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY GyA GyB

/-! ## リストの補題 -/

theorem stepSum_all (b m : ℕ) (f : ℕ → ℕ) : ∀ {A : List ℕ}, (∀ a ∈ A, b + a < m) →
    stepSum b f A m = sumOn f A
  | [], _ => rfl
  | a :: A, h => by
      simp only [stepSum, sumOn]
      rw [if_pos (h a (by simp)),
        stepSum_all b m f (A := A) (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem le_foldr_max : ∀ {A : List ℕ} {a : ℕ}, a ∈ A → a ≤ A.foldr max 0
  | [], _, h => by simp at h
  | x :: A, a, h => by
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (le_foldr_max h) (le_max_right _ _)

theorem foldr_max_mem : ∀ {A : List ℕ}, A ≠ [] → A.foldr max 0 ∈ A
  | [], h => absurd rfl h
  | x :: A, _ => by
      simp only [List.foldr_cons]
      by_cases hA : A = []
      · subst hA; simp
      · have ih := foldr_max_mem hA
        rcases le_total x (A.foldr max 0) with hle | hle
        · rw [max_eq_right hle]; exact List.mem_cons_of_mem x ih
        · rw [max_eq_left hle]; simp

theorem filter_length_lt {p : ℕ → Bool} : ∀ {A : List ℕ} {a : ℕ}, a ∈ A → p a = false →
    (A.filter p).length < A.length
  | [], _, h, _ => by simp at h
  | x :: A, a, ha, hp => by
      rw [List.filter_cons]
      have hle := List.length_filter_le p A
      rcases List.mem_cons.mp ha with rfl | ha'
      · rw [if_neg (by simp [hp])]
        simp only [List.length_cons]; omega
      · have := filter_length_lt ha' hp
        split_ifs <;> simp only [List.length_cons] <;> omega

theorem filter_all {p : ℕ → Bool} : ∀ {A : List ℕ}, (∀ a ∈ A, p a = true) → A.filter p = A
  | [], _ => rfl
  | x :: A, h => by
      rw [List.filter_cons, if_pos (h x (by simp)),
        filter_all (A := A) (fun a ha => h a (List.mem_cons_of_mem x ha))]

/-! ## ガードと導入の向き -/

theorem GpT_guard {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {h : ℕ → ℕ} {τ : ℕ}
    (hτ : τ < liftOff h A o) :
    (lowP h A τ).length < A.length ∨ ((lowP h A τ).length = A.length ∧
      τ - sumOn h (lowP h A τ) - (lowP h A τ).foldr max 0 < o - A.foldr max 0) := by
  by_cases hall : ∀ a ∈ A, liftVal h A a < τ
  · right
    have hlow : lowP h A τ = A := by
      unfold lowP
      exact filter_all (fun a ha => by simpa using hall a ha)
    rw [hlow]
    refine ⟨rfl, ?_⟩
    have hsum : liftOff h A o = o + sumOn h A := by
      unfold liftOff
      rw [stepSum_all 0 o h (fun a ha => by have := hA a ha; omega)]
    by_cases hAe : A = []
    · subst hAe
      simp only [liftOff, stepSum, sumOn, List.foldr_nil, Nat.sub_zero, Nat.add_zero] at hτ ⊢
      exact hτ
    · have hmem := foldr_max_mem hAe
      have hM := hall _ hmem
      have hlv : liftVal h A (A.foldr max 0) = A.foldr max 0 + sumOn h A := by
        unfold liftVal
        rw [stepSum_all 0 _ h (fun a ha => by have := le_foldr_max ha; omega)]
      have hMo := hA _ hmem
      omega
  · left
    push_neg at hall
    obtain ⟨a, ha, hle⟩ := hall
    unfold lowP
    exact filter_length_lt ha (by simpa using hle)

/-- ★ 導入の向き: ガードなしの文脈で示せば GpT。 -/
theorem GpT_intro {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {f : ℕ → ℕ} {b : ℕ} {E : TrioSeq}
    (H : ∀ R, CtxP (GC A) A o R → ∀ g,
      nslot (R (addF f g)) (liftOff (addF f g) A o) b (reliftX b f g A E)) :
    GpT A o f b E := by
  rw [GpT]
  intro R hR g
  refine H R (fun f' => ⟨(hR f').1, (hR f').2.1, (hR f').2.2.1, fun s h2 hs => ?_⟩) g
  intro b0 P d hP hd hbot h1 h2'
  refine (hR f').2.2.2 s h2 hs b0 P d hP hd hbot h1
    (fun g' b' hb τ L h1τ hτ hL hGL => h2' g' b' hb τ L h1τ hτ hL ?_)
  have hτ' : τ < liftOff (addF f' g') A o := by
    rw [← reOff_liftOff]; exact lt_of_lt_of_le hτ (reOff_mono f' g' A hs)
  have hg := GpT_guard (h := addF f' g') hA hτ'
  simpa [hg] using hGL

/-! ## slift の部品（末尾の列） -/

theorem slift_snoc (K : TrioSeq) (c : ℕ × ℕ × ℕ) (φ : ℕ → ℕ) :
    slift (K ++ [c]) φ = slift K φ ++
      [((c.1, c.2.1 + (φ (amin (K ++ [c]) K.length) - amin (K ++ [c]) K.length), c.2.2) :
        ℕ × ℕ × ℕ)] := by
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [slift_length, List.length_append, List.length_singleton] at hi
  rw [slift_getD (by rw [List.length_append, List.length_singleton]; omega)]
  rcases Nat.lt_or_ge i K.length with hiK | hiK
  · have eg : (slift K φ ++ [((c.1, c.2.1 + (φ (amin (K ++ [c]) K.length) -
          amin (K ++ [c]) K.length), c.2.2) : ℕ × ℕ × ℕ)]).getD i (0, 0, 0)
        = (slift K φ).getD i (0, 0, 0) := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [slift_length]; exact hiK)]
    rw [eg, slift_getD hiK, Small.entry_append_left hiK, Small.entry_append_left hiK,
      Small.entry_append_left hiK, amin_append_left hiK]
  · have hiK' : i = K.length := by omega
    subst hiK'
    rw [getD_app_right _ _ (by rw [slift_length]), slift_length, Nat.sub_self]
    rw [show K.length = K.length + 0 from rfl, entry_append_right, entry_append_right,
      entry_append_right]
    rfl

theorem slift_snoc_fix (K : TrioSeq) (c : ℕ × ℕ × ℕ) {φ : ℕ → ℕ}
    (hφ : ∀ m, m ≤ c.2.1 → φ m = m) : slift (K ++ [c]) φ = slift K φ ++ [c] := by
  rw [slift_snoc]
  have hle : amin (K ++ [c]) K.length ≤ c.2.1 := by
    have := amin_self_le (K ++ [c]) K.length
    rw [show K.length = K.length + 0 from rfl, entry_append_right] at this
    exact this
  rw [hφ _ hle, Nat.sub_self, Nat.add_zero]

theorem slift_append_low {A B : TrioSeq} {v : ℕ}
    (hB : ∀ i, i < B.length → ∃ k, Relation.ReflTransGen (nextrel0 B) k i ∧ entry B 1 k ≤ v)
    {φ : ℕ → ℕ} (hφ : ∀ m, m ≤ v → φ m = m) : slift (A ++ B) φ = slift A φ ++ B := by
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [slift_length, List.length_append] at hi
  rw [slift_getD (by rw [List.length_append]; omega)]
  rcases Nat.lt_or_ge i A.length with hiA | hiA
  · have eg : (slift A φ ++ B).getD i (0, 0, 0) = (slift A φ).getD i (0, 0, 0) := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [slift_length]; exact hiA)]
    rw [eg, slift_getD hiA, Small.entry_append_left hiA, Small.entry_append_left hiA,
      Small.entry_append_left hiA, amin_append_left hiA]
  · obtain ⟨q, rfl⟩ : ∃ q, i = A.length + q := ⟨i - A.length, by omega⟩
    have hq : q < B.length := by omega
    obtain ⟨k, hk, hkv⟩ := hB q hq
    have hle : amin (A ++ B) (A.length + q) ≤ v := by
      have := amin_le (A := A ++ B) (rtg_nextrel0_lift A B hk)
      rw [entry_append_right] at this
      omega
    rw [getD_app_right _ _ (by rw [slift_length]; omega), slift_length,
      show A.length + q - A.length = q from by omega, hφ _ hle, Nat.sub_self, Nat.add_zero,
      entry_append_right, entry_append_right, entry_append_right,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
    exact entry_triple hq

theorem reStair_low (b : ℕ) (f g : ℕ → ℕ) (A : List ℕ) {m : ℕ} (hm : m ≤ b) :
    reStair b f g A m = m := by
  simp [reStair, reStep_le_base b f g A hm]

theorem reStair_tie (b : ℕ) (f g : ℕ → ℕ) {A : List ℕ} (hA : ∀ a ∈ A, 1 ≤ a) {m : ℕ}
    (hm : m ≤ b + 1) : reStair b f g A m = m := by
  have key : ∀ A' : List ℕ, (∀ a ∈ A', 1 ≤ a) → reStep b f g A A' m = 0 := by
    intro A' hA'
    induction A' with
    | nil => rfl
    | cons a A' ih =>
        simp only [reStep]
        have h1 := hA' a (by simp)
        have h2 : a ≤ liftVal f A a := by unfold liftVal; omega
        rw [if_neg (by omega), ih (fun x hx => hA' x (List.mem_cons_of_mem a hx))]
  simp [reStair, key A hA]

/-! ## 差し込み口の公理 -/

theorem GpT_ax {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (f : ℕ → ℕ) : SlotAx (GpT A o f) where
  lift := by
    intro u W hW h u' hu
    refine GpT_intro hA (fun R hR g => ?_)
    have hk : 1 ≤ liftOff (addF f g) A o := by unfold liftOff; omega
    have := (nslot_ax (hR (addF f g)).1 hk).lift u _ (Fr_reliftX hW _ _ _ _) (GpT_elim h hR g) u' hu
    rwa [mlift_reliftX, show u + (u' - u) = u' by omega] at this
  oper := by
    intro u W U hW hU hH hlen hp hIH
    refine GpT_intro hA (fun R hR g => ?_)
    have hk : 1 ≤ liftOff (addF f g) A o := by unfold liftOff; omega
    have hUne : U ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    rw [reliftX_app hW hH]
    refine (nslot_ax (hR (addF f g)).1 hk).oper u _ _ (Fr_reliftX hW _ _ _ _) (Fr_reliftX hU _ _ _ _)
      (Hd_reliftX hH _ _ _ _) (by rw [reliftX_length]; exact hlen) ?_ (fun m hm => ?_)
    · unfold reliftX
      rw [slift_length, srow_slift (reStair_stair u f g A) (by omega),
        hasParent_slift (reStair_stair u f g A)]
      exact hp
    · have h1 := GpT_elim (hIH m hm) hR g
      rw [reliftX_app hW (Hd_oper hH hUne hm)] at h1
      unfold reliftX at h1 ⊢
      rwa [slift_oper (reStair_stair u f g A)] at h1
  orph := by
    intro u W U h j hW hU hH hj1 hj hnp hz
    refine GpT_intro hA (fun R hR g => ?_)
    have hk : 1 ≤ liftOff (addF f g) A o := by unfold liftOff; omega
    have hfix : ∀ m, m ≤ j → reStair u f g A m = m := fun m hm => reStair_low u f g A (by omega)
    have eU : reliftX u f g A U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]
        = reliftX u f g A (U ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
      unfold reliftX; rw [slift_snoc_fix U _ hfix]
    rw [reliftX_app hW hH, ← eU]
    refine (nslot_ax (hR (addF f g)).1 hk).orph u _ _ h j (Fr_reliftX hW _ _ _ _)
      (by rw [eU]; exact Fr_reliftX hU _ _ _ _) (by rw [eU]; exact Hd_reliftX hH _ _ _ _) hj1 hj
      ?_ (fun z hz' hbz => ?_)
    · rw [eU, reliftX_length]
      unfold reliftX
      rw [hasParent_slift (reStair_stair u f g A)]
      exact hnp
    · have h1 := GpT_elim (hz z hz' hbz) hR g
      have hzW : z ∈ Wg (2 * j) := Wg_mono (by omega) hz'
      have hHz : Hd (U ++ shiftr01 h 0 z) := by
        intro hne
        by_cases hUn : U = []
        · subst hUn
          have hh1 : h = 1 := by have := hH (by simp); simpa [entry] using this
          have hzne : z ≠ [] := by intro hz0; apply hne; subst hz0; rfl
          simp only [List.nil_append]
          rw [entry0_shiftr01 (List.length_pos_iff.mpr hzne), show entry z 0 0 = 0 from hbz, hh1]
        · rw [Small.entry_append_left (List.length_pos_iff.mpr hUn)]
          have := hH (by simp)
          rwa [Small.entry_append_left (List.length_pos_iff.mpr hUn)] at this
      rw [reliftX_app hW hHz] at h1
      unfold reliftX at h1 ⊢
      rw [slift_append_low (low_of_Wg hzW h le_rfl) hfix] at h1
      exact h1
  tie := by
    intro u W U x hW hU hH hc hload
    refine GpT_intro hA (fun R hR g => ?_)
    have hk : 1 ≤ liftOff (addF f g) A o := by unfold liftOff; omega
    have hfix : ∀ m, m ≤ u + 1 → reStair u f g A m = m := fun m hm => reStair_tie u f g hA1 hm
    have hHU : Hd U := by
      intro hne
      have := hH (by simp)
      rwa [Small.entry_append_left (List.length_pos_iff.mpr hne)] at this
    have eU : reliftX u f g A U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]
        = reliftX u f g A (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) := by
      unfold reliftX; rw [slift_snoc_fix U _ hfix]
    rw [reliftX_app hW hH, ← eU]
    refine (nslot_ax (hR (addF f g)).1 hk).tie u _ _ x (Fr_reliftX hW _ _ _ _)
      (by rw [eU]; exact Fr_reliftX hU _ _ _ _) (by rw [eU]; exact Hd_reliftX hH _ _ _ _) ?_
      (fun u' hu' Z hZ hbZ => ?_)
    · rw [eU, reliftX_length]
      unfold reliftX
      rw [coneV_iff_amin, amin_slift (reStair_stair u f g A) (by simp)]
      have h0 := coneV_iff_amin.mp hc
      have h1 := (reStair_stair u f g A).ge (amin (U ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) U.length)
      omega
    · have h1 := GpT_elim (hload u' hu' Z hZ hbZ) hR g
      have e1 : reliftX u' f g A (mlift (W ++ U) u (u' - u) ++ shiftr01 x 0 Z)
          = reliftX u' f g A (mlift (W ++ U) u (u' - u)) ++ shiftr01 x 0 Z := by
        unfold reliftX
        exact slift_append_low (low_of_Wg hZ x le_rfl) (fun m hm => reStair_low u' f g A hm)
      have e2 : reliftX u' f g A (mlift (W ++ U) u (u' - u))
          = mlift (reliftX u f g A W ++ reliftX u f g A U) u (u' - u) := by
        rw [← reliftX_app hW hHU, mlift_reliftX, show u + (u' - u) = u' by omega]
      rw [e1, e2] at h1
      exact h1
  flat := by
    intro u W hW h
    refine GpT_intro hA (fun R hR g => ?_)
    have hk : 1 ≤ liftOff (addF f g) A o := by unfold liftOff; omega
    have e : reliftX u f g A (W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)])
        = reliftX u f g A W ++ [((1, 0, 0) : ℕ × ℕ × ℕ)] := by
      unfold reliftX
      refine slift_snoc_fix W _ (fun m hm => ?_)
      have hm0 : m = 0 := by simpa using hm
      subst hm0
      exact (reStair_stair u f g A).zero
    rw [e]
    exact (nslot_ax (hR (addF f g)).1 hk).flat u _ (Fr_reliftX hW _ _ _ _) (GpT_elim h hR g)

/-! ## 状態の合同と、持ち上げで閉じる性質 -/

theorem GpT_congr {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {f f' : ℕ → ℕ}
    (hff : ∀ a ∈ A, f a = f' a) {b : ℕ} {E : TrioSeq} (h : GpT A o f b E) : GpT A o f' b E := by
  refine GpT_intro hA (fun R hR g => ?_)
  have hA' : ∀ a ∈ A, addF f g a = addF f' g a := fun a ha => by unfold addF; rw [hff a ha]
  have h1 := GpT_elim h hR g
  rw [reliftX_congr b hff (fun a _ => rfl) E] at h1
  have ek : liftOff (addF f g) A o = liftOff (addF f' g) A o := by
    unfold liftOff; rw [stepSum_congr 0 o hA']
  rw [ek] at h1
  intro u' hu X hX hRX
  exact (hR (addF f g)).2.1 _ u' _ hA'
    (h1 u' hu X hX ((hR (addF f' g)).2.1 _ u' X (fun a ha => (hA' a ha).symm) hRX))

theorem addF_assoc (f g g' : ℕ → ℕ) : addF (addF f g) g' = addF f (addF g g') := by
  funext a; unfold addF; omega

theorem GpT_lift {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) {f : ℕ → ℕ} {b : ℕ} {X : TrioSeq}
    (h : GpT A o f b X) (g : ℕ → ℕ) : GpT A o (addF f g) b (reliftX b f g A X) := by
  refine GpT_intro hA (fun R hR g' => ?_)
  rw [reliftX_comp, addF_assoc]
  exact GpT_elim h hR (addF g g')

end GyC
end TRIO
