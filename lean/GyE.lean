/-
GyE.lean: 子の級の制限のための部品（錨の列の分割、状態の差し替え mergeF と、その位置の計算）。

    lowP h0 A τ1 : 状態 h0 で行 1 の値 τ1 より下の錨（子の錨の列）
    lowU h0 A τ1 : それ以外（上の錨）
    mergeF A1 h' h0 : A1 の上では h'、それ以外では h0
-/
import GyD

namespace TRIO
namespace GyE

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY GyA GyB GyC GyD

/-! ## 足し算の分割 -/

theorem stepSum_split (b m : ℕ) (F : ℕ → ℕ) (p : ℕ → Bool) : ∀ A : List ℕ,
    stepSum b F A m = stepSum b F (A.filter p) m + stepSum b F (A.filter (fun x => !p x)) m
  | [] => rfl
  | a :: A => by
      have ih := stepSum_split b m F p A
      rw [List.filter_cons, List.filter_cons]
      by_cases hp : p a = true
      · rw [if_pos hp, if_neg (by simp [hp])]
        simp only [stepSum, ih]; omega
      · rw [if_neg hp, if_pos (by simpa using hp)]
        simp only [stepSum, ih]; omega

theorem sumOn_congr {F G : ℕ → ℕ} : ∀ {A : List ℕ}, (∀ a ∈ A, F a = G a) → sumOn F A = sumOn G A
  | [], _ => rfl
  | a :: A, h => by
      simp only [sumOn]
      rw [h a (by simp), sumOn_congr (A := A) (fun x hx => h x (List.mem_cons_of_mem a hx))]

def lowU (f : ℕ → ℕ) (A : List ℕ) (r : ℕ) : List ℕ := A.filter (fun a => !decide (liftVal f A a < r))

theorem stepSum_lowPU (b m : ℕ) (F h0 : ℕ → ℕ) (A : List ℕ) (τ1 : ℕ) :
    stepSum b F A m = stepSum b F (lowP h0 A τ1) m + stepSum b F (lowU h0 A τ1) m :=
  stepSum_split b m F (fun a => decide (liftVal h0 A a < τ1)) A

theorem mem_lowP_iff {f : ℕ → ℕ} {A : List ℕ} {r a : ℕ} :
    a ∈ lowP f A r ↔ a ∈ A ∧ liftVal f A a < r := by
  unfold lowP; rw [List.mem_filter]; simp

theorem mem_lowU_iff {f : ℕ → ℕ} {A : List ℕ} {r a : ℕ} :
    a ∈ lowU f A r ↔ a ∈ A ∧ ¬ liftVal f A a < r := by
  unfold lowU; rw [List.mem_filter]; simp

theorem lowP_down {f : ℕ → ℕ} {A : List ℕ} {r a a' : ℕ} (ha : a ∈ A) (ha' : a' ∈ lowP f A r)
    (hle : a ≤ a') : a ∈ lowP f A r := by
  rw [mem_lowP_iff] at ha' ⊢
  exact ⟨ha, lt_of_le_of_lt (liftVal_mono f A hle) ha'.2⟩

/-- 子の錨は子の元の値より下で、合計も子の持ち上げ後の値より小さい。 -/
theorem lowP_lt_o1 {h0 : ℕ → ℕ} {A : List ℕ} {τ1 : ℕ} :
    ∀ a ∈ lowP h0 A τ1, a < τ1 - sumOn h0 (lowP h0 A τ1) ∧ sumOn h0 (lowP h0 A τ1) < τ1 := by
  intro a ha
  have hne : lowP h0 A τ1 ≠ [] := List.ne_nil_of_mem ha
  have hMmem := foldr_max_mem hne
  have haM_le := le_foldr_max ha
  have hM := mem_lowP_iff.mp hMmem
  have hall : stepSum 0 h0 (lowP h0 A τ1) ((lowP h0 A τ1).foldr max 0 + 1)
      = sumOn h0 (lowP h0 A τ1) :=
    stepSum_all 0 _ h0 (fun x hx => by have := le_foldr_max hx; omega)
  have hsplit := stepSum_lowPU 0 ((lowP h0 A τ1).foldr max 0 + 1) h0 h0 A τ1
  have hlv := hM.2
  unfold liftVal at hlv
  omega

theorem liftOff_eq_sumOn {h : ℕ → ℕ} {A1 : List ℕ} {o1 : ℕ} (hlt : ∀ a ∈ A1, a < o1) :
    liftOff h A1 o1 = o1 + sumOn h A1 := by
  unfold liftOff; rw [stepSum_all 0 o1 h (fun x hx => by have := hlt x hx; omega)]

theorem liftOff_lowP (h0 : ℕ → ℕ) (A : List ℕ) (τ1 : ℕ) :
    liftOff h0 (lowP h0 A τ1) (τ1 - sumOn h0 (lowP h0 A τ1)) = τ1 := by
  by_cases hne : lowP h0 A τ1 = []
  · rw [hne]; simp [liftOff, stepSum, sumOn]
  · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
    have h1 := (lowP_lt_o1 a ha).2
    rw [liftOff_eq_sumOn (fun x hx => (lowP_lt_o1 x hx).1)]
    omega

/-! ## 状態の差し替え -/

def maskF (A1 : List ℕ) (g : ℕ → ℕ) : ℕ → ℕ := fun a => if a ∈ A1 then g a else 0

def mergeF (A1 : List ℕ) (h' h0 : ℕ → ℕ) : ℕ → ℕ := fun a => if a ∈ A1 then h' a else h0 a

theorem mergeF_self (A1 : List ℕ) (h : ℕ → ℕ) : mergeF A1 h h = h := by
  funext a; unfold mergeF; split_ifs <;> rfl

theorem mergeF_add (A1 : List ℕ) (h' h0 g : ℕ → ℕ) :
    mergeF A1 (addF h' g) h0 = addF (mergeF A1 h' h0) (maskF A1 g) := by
  funext a; by_cases ha : a ∈ A1 <;> simp [mergeF, addF, maskF, ha]

/-- 下の錨の位置は、差し替えた状態でも子の錨の列だけで決まる。 -/
theorem liftVal_merge {A : List ℕ} {h0 : ℕ → ℕ} {τ1 : ℕ} (h' h0' : ℕ → ℕ) {a : ℕ}
    (ha : a ∈ lowP h0 A τ1) :
    liftVal (mergeF (lowP h0 A τ1) h' h0') A a = liftVal h' (lowP h0 A τ1) a := by
  unfold liftVal
  congr 1
  have hsplit := stepSum_lowPU 0 (a + 1) (mergeF (lowP h0 A τ1) h' h0') h0 A τ1
  have hU : stepSum 0 (mergeF (lowP h0 A τ1) h' h0') (lowU h0 A τ1) (a + 1) = 0 := by
    have key : ∀ L : List ℕ, (∀ x ∈ L, x ∈ A ∧ ¬ liftVal h0 A x < τ1) →
        stepSum 0 (mergeF (lowP h0 A τ1) h' h0') L (a + 1) = 0 := by
      intro L hL
      induction L with
      | nil => rfl
      | cons x L ih =>
          simp only [stepSum]
          have hx := hL x (by simp)
          have hxa : ¬ 0 + x < a + 1 := by
            intro hlt
            have := liftVal_mono h0 A (show x ≤ a by omega)
            have := (mem_lowP_iff.mp ha).2
            exact hx.2 (by omega)
          rw [if_neg hxa, ih (fun y hy => hL y (List.mem_cons_of_mem x hy))]
    exact key _ (fun x hx => mem_lowU_iff.mp hx)
  rw [hsplit, hU, Nat.add_zero]
  exact stepSum_congr 0 (a + 1) (fun x hx => by unfold mergeF; rw [if_pos hx])

theorem reStep_filter_zero (b m : ℕ) (f g : ℕ → ℕ) (A0 : List ℕ) (p : ℕ → Bool) : ∀ {L : List ℕ},
    (∀ x ∈ L, p x = false → g x = 0) → reStep b f g A0 L m = reStep b f g A0 (L.filter p) m
  | [], _ => rfl
  | x :: L, h => by
      have ih := reStep_filter_zero b m f g A0 p (L := L)
        (fun y hy => h y (List.mem_cons_of_mem x hy))
      rw [List.filter_cons]
      by_cases hp : p x = true
      · rw [if_pos hp]; simp only [reStep, ih]
      · rw [if_neg hp]
        have hg : g x = 0 := h x (by simp) (by simpa using hp)
        simp only [reStep, ih, hg]
        split_ifs <;> simp

theorem reStep_congr2 (b m : ℕ) {f f' g g' : ℕ → ℕ} {A0 A1 : List ℕ} : ∀ {L : List ℕ},
    (∀ x ∈ L, liftVal f A0 x = liftVal f' A1 x) → (∀ x ∈ L, g x = g' x) →
    reStep b f g A0 L m = reStep b f' g' A1 L m
  | [], _, _ => rfl
  | x :: L, hl, hg => by
      simp only [reStep]
      rw [hl x (by simp), hg x (by simp),
        reStep_congr2 b m (L := L) (fun y hy => hl y (List.mem_cons_of_mem x hy))
          (fun y hy => hg y (List.mem_cons_of_mem x hy))]

/-- 差し替えた状態で、子の錨だけの持ち上げは子の列の持ち上げ。 -/
theorem reliftX_merge {A : List ℕ} {h0 : ℕ → ℕ} {τ1 : ℕ} (b : ℕ) (h' h0' g : ℕ → ℕ)
    (X : TrioSeq) :
    reliftX b (mergeF (lowP h0 A τ1) h' h0') (maskF (lowP h0 A τ1) g) A X
      = reliftX b h' g (lowP h0 A τ1) X := by
  unfold reliftX reStair
  congr 1
  funext m
  congr 1
  rw [reStep_filter_zero b m (mergeF (lowP h0 A τ1) h' h0') (maskF (lowP h0 A τ1) g) A
    (fun x => decide (liftVal h0 A x < τ1)) (L := A) (fun x hx hpx => ?_)]
  · change reStep b (mergeF (lowP h0 A τ1) h' h0') (maskF (lowP h0 A τ1) g) A (lowP h0 A τ1) m = _
    exact reStep_congr2 b m (fun x hx => liftVal_merge h' h0' hx)
      (fun x hx => by unfold maskF; rw [if_pos hx])
  · unfold maskF
    rw [if_neg]
    intro hmem
    have := (mem_lowP_iff.mp hmem).2
    simp [this] at hpx

/-- 上の錨は、差し替えた状態でも子の持ち上げ後の位置より上。 -/
theorem liftVal_merge_upper {A : List ℕ} {h0 : ℕ → ℕ} {τ1 : ℕ} (h' G : ℕ → ℕ) {a : ℕ}
    (ha : a ∈ A) (hna : a ∉ lowP h0 A τ1) :
    liftOff h' (lowP h0 A τ1) (τ1 - sumOn h0 (lowP h0 A τ1))
      ≤ liftVal (mergeF (lowP h0 A τ1) h' (addF h0 G)) A a := by
  have hnot : ¬ liftVal h0 A a < τ1 := fun h => hna (mem_lowP_iff.mpr ⟨ha, h⟩)
  have hA1lt : ∀ x ∈ lowP h0 A τ1, 0 + x < a + 1 := by
    intro x hx
    by_contra hc
    exact hna (lowP_down ha hx (by omega))
  have s1 := stepSum_lowPU 0 (a + 1) (mergeF (lowP h0 A τ1) h' (addF h0 G)) h0 A τ1
  have s2 := stepSum_lowPU 0 (a + 1) h0 h0 A τ1
  have e1 : stepSum 0 (mergeF (lowP h0 A τ1) h' (addF h0 G)) (lowP h0 A τ1) (a + 1)
      = sumOn h' (lowP h0 A τ1) := by
    rw [stepSum_congr 0 (a + 1) (g := h') (fun x hx => by unfold mergeF; rw [if_pos hx])]
    exact stepSum_all 0 (a + 1) h' hA1lt
  have e2 : stepSum 0 (mergeF (lowP h0 A τ1) h' (addF h0 G)) (lowU h0 A τ1) (a + 1)
      = stepSum 0 (addF h0 G) (lowU h0 A τ1) (a + 1) := by
    refine stepSum_congr 0 (a + 1) (fun x hx => ?_)
    unfold mergeF
    rw [if_neg]
    intro hmem
    exact (mem_lowU_iff.mp hx).2 (mem_lowP_iff.mp hmem).2
  have e3 : stepSum 0 h0 (lowP h0 A τ1) (a + 1) = sumOn h0 (lowP h0 A τ1) :=
    stepSum_all 0 (a + 1) h0 hA1lt
  have e4 : stepSum 0 (addF h0 G) (lowU h0 A τ1) (a + 1)
      = stepSum 0 h0 (lowU h0 A τ1) (a + 1) + stepSum 0 G (lowU h0 A τ1) (a + 1) := by
    unfold addF; exact stepSum_add 0 (a + 1) h0 G _
  by_cases hne : lowP h0 A τ1 = []
  · have hlo : liftOff h' (lowP h0 A τ1) (τ1 - sumOn h0 (lowP h0 A τ1)) = τ1 := by
      rw [hne]; simp [liftOff, stepSum, sumOn]
    have hs0 : sumOn h' (lowP h0 A τ1) = 0 := by rw [hne]; rfl
    have hs0' : sumOn h0 (lowP h0 A τ1) = 0 := by rw [hne]; rfl
    rw [hlo]
    unfold liftVal at hnot ⊢
    omega
  · have hlo : liftOff h' (lowP h0 A τ1) (τ1 - sumOn h0 (lowP h0 A τ1))
        = τ1 - sumOn h0 (lowP h0 A τ1) + sumOn h' (lowP h0 A τ1) :=
      liftOff_eq_sumOn (fun x hx => (lowP_lt_o1 x hx).1)
    obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil _ hne
    have hsum := (lowP_lt_o1 x0 hx0).2
    rw [hlo]
    unfold liftVal at hnot ⊢
    omega

end GyE
end TRIO
