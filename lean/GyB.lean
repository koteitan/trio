/-
GyB.lean: 錨の列（元の値）と持ち上げの関数による、節点の子の並びの述語 GpT。

    stepSum b f A m   = Σ_{a ∈ A} [b + a < m] f a
    liftVal f A a     = a + stepSum 0 f A (a + 1)             （状態 f での錨 a の位置）
    reStep b f g A m  = Σ_{a ∈ A} [b + liftVal f A a < m] g a  （状態 f から f+g への持ち上げ）
    reliftX b f g A X = slift X (m ↦ m + reStep b f g A m)
-/
import GyA

namespace TRIO
namespace GyB

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY GyA

/-! ## 階段 -/

def stepSum (b : ℕ) (f : ℕ → ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: A, m => (if b + a < m then f a else 0) + stepSum b f A m

theorem stepSum_mono (b : ℕ) (f : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) :
    ∀ A : List ℕ, stepSum b f A m ≤ stepSum b f A n
  | [] => le_rfl
  | a :: A => by
      have ih := stepSum_mono b f h A
      simp only [stepSum]
      split_ifs <;> omega

theorem stepSum_add (b m : ℕ) (f g : ℕ → ℕ) : ∀ A : List ℕ,
    stepSum b (fun a => f a + g a) A m = stepSum b f A m + stepSum b g A m
  | [] => rfl
  | a :: A => by
      simp only [stepSum, stepSum_add b m f g A]
      split_ifs <;> omega

theorem stepSum_congr (b m : ℕ) {f g : ℕ → ℕ} : ∀ {A : List ℕ}, (∀ a ∈ A, f a = g a) →
    stepSum b f A m = stepSum b g A m
  | [], _ => rfl
  | a :: A, h => by
      simp only [stepSum]
      rw [h a (by simp), stepSum_congr b m (fun x hx => h x (by simp [hx]))]

theorem stepSum_filter (b m : ℕ) (f : ℕ → ℕ) (p : ℕ → Bool) : ∀ {A : List ℕ},
    (∀ a ∈ A, b + a < m → p a = true) → stepSum b f (A.filter p) m = stepSum b f A m
  | [], _ => rfl
  | a :: A, h => by
      have ih := stepSum_filter b m f p (A := A) (fun x hx => h x (List.mem_cons_of_mem a hx))
      rw [List.filter_cons]
      by_cases hp : p a = true
      · rw [if_pos hp]
        simp only [stepSum, ih]
      · rw [if_neg hp]
        have hlt : ¬ b + a < m := fun hl => hp (h a (by simp) hl)
        simp only [stepSum, ih, if_neg hlt, Nat.zero_add]

/-! ## 状態 f での錨の位置 -/

def addF (f g : ℕ → ℕ) : ℕ → ℕ := fun a => f a + g a

def liftVal (f : ℕ → ℕ) (A : List ℕ) (a : ℕ) : ℕ := a + stepSum 0 f A (a + 1)

def liftOff (f : ℕ → ℕ) (A : List ℕ) (m : ℕ) : ℕ := m + stepSum 0 f A m

theorem liftVal_mono (f : ℕ → ℕ) (A : List ℕ) {a a' : ℕ} (h : a ≤ a') :
    liftVal f A a ≤ liftVal f A a' := by
  unfold liftVal
  have := stepSum_mono 0 f (show a + 1 ≤ a' + 1 by omega) A
  omega

theorem lt_of_liftVal_lt (f : ℕ → ℕ) (A : List ℕ) {a a' : ℕ}
    (h : liftVal f A a < liftVal f A a') : a < a' := by
  by_contra hc
  have := liftVal_mono f A (show a' ≤ a by omega)
  omega

theorem liftVal_add (f g : ℕ → ℕ) (A : List ℕ) (a : ℕ) :
    liftVal (addF f g) A a = liftVal f A a + stepSum 0 g A (a + 1) := by
  unfold liftVal addF; rw [stepSum_add]; omega

/-! ## 状態 f から f+g への持ち上げ -/

def reStep (b : ℕ) (f g : ℕ → ℕ) (A0 : List ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: A, m => (if b + liftVal f A0 a < m then g a else 0) + reStep b f g A0 A m

theorem reStep_mono (b : ℕ) (f g : ℕ → ℕ) (A0 : List ℕ) {m n : ℕ} (h : m ≤ n) :
    ∀ A : List ℕ, reStep b f g A0 A m ≤ reStep b f g A0 A n
  | [] => le_rfl
  | a :: A => by
      have ih := reStep_mono b f g A0 h A
      simp only [reStep]
      split_ifs <;> omega

theorem reStep_le_base (b : ℕ) (f g : ℕ → ℕ) (A0 : List ℕ) {m : ℕ} (h : m ≤ b) :
    ∀ A : List ℕ, reStep b f g A0 A m = 0
  | [] => rfl
  | a :: A => by
      simp only [reStep, reStep_le_base b f g A0 h A]
      rw [if_neg (by omega)]

theorem reStep_shift (b d m : ℕ) (f g : ℕ → ℕ) (A0 : List ℕ) :
    ∀ A : List ℕ, reStep (b + d) f g A0 A (m + d) = reStep b f g A0 A m
  | [] => rfl
  | a :: A => by
      simp only [reStep, reStep_shift b d m f g A0 A]
      by_cases h : b + liftVal f A0 a < m
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]

theorem reStep_base (b m : ℕ) (f g : ℕ → ℕ) (A0 A : List ℕ) :
    reStep b f g A0 A (b + m) = reStep 0 f g A0 A m := by
  have := reStep_shift 0 b m f g A0 A
  rwa [Nat.zero_add, Nat.add_comm m b] at this

theorem reStep_add (b m : ℕ) (f g g' : ℕ → ℕ) (A0 : List ℕ) : ∀ A : List ℕ,
    reStep b f (addF g g') A0 A m = reStep b f g A0 A m + reStep b f g' A0 A m
  | [] => rfl
  | a :: A => by
      simp only [reStep, addF, reStep_add b m f g g' A0 A]
      split_ifs <;> omega

theorem reStep_zeroG (b m : ℕ) (f : ℕ → ℕ) (A0 : List ℕ) : ∀ A : List ℕ,
    reStep b f (fun _ => 0) A0 A m = 0
  | [] => rfl
  | a :: A => by simp [reStep, reStep_zeroG b m f A0 A]

theorem reStep_congr (b m : ℕ) {f f' g g' : ℕ → ℕ} {A0 : List ℕ} (hf : ∀ a ∈ A0, f a = f' a) :
    ∀ {A : List ℕ}, (∀ a ∈ A, g a = g' a) → reStep b f g A0 A m = reStep b f' g' A0 A m
  | [], _ => rfl
  | a :: A, hg => by
      have e : liftVal f A0 a = liftVal f' A0 a := by
        unfold liftVal; rw [stepSum_congr 0 (a + 1) hf]
      simp only [reStep]
      rw [e, hg a (by simp), reStep_congr b m hf (fun x hx => hg x (by simp [hx]))]

theorem reStep_congrA0 (b m : ℕ) (f g : ℕ → ℕ) {A0 A1 : List ℕ} : ∀ {A : List ℕ},
    (∀ a ∈ A, liftVal f A0 a = liftVal f A1 a) → reStep b f g A0 A m = reStep b f g A1 A m
  | [], _ => rfl
  | a :: A, h => by
      simp only [reStep]
      rw [h a (by simp), reStep_congrA0 b m f g (fun x hx => h x (by simp [hx]))]

theorem reStep_ge (b : ℕ) (f g : ℕ → ℕ) (A0 : List ℕ) (a m : ℕ)
    (h : b + liftVal f A0 a < m) : ∀ A : List ℕ, stepSum 0 g A (a + 1) ≤ reStep b f g A0 A m
  | [] => le_rfl
  | a' :: A => by
      have ih := reStep_ge b f g A0 a m h A
      simp only [stepSum, reStep]
      by_cases h1 : 0 + a' < a + 1
      · have : liftVal f A0 a' ≤ liftVal f A0 a := liftVal_mono f A0 (by omega)
        rw [if_pos h1, if_pos (by omega)]; omega
      · rw [if_neg h1]; split_ifs <;> omega

theorem reStep_le (b : ℕ) (f g : ℕ → ℕ) (A0 : List ℕ) (a m : ℕ)
    (h : m ≤ b + liftVal f A0 a) : ∀ A : List ℕ, reStep b f g A0 A m ≤ stepSum 0 g A (a + 1)
  | [] => le_rfl
  | a' :: A => by
      have ih := reStep_le b f g A0 a m h A
      simp only [stepSum, reStep]
      by_cases h1 : b + liftVal f A0 a' < m
      · have : a' < a := lt_of_liftVal_lt f A0 (by omega)
        rw [if_pos h1, if_pos (by omega)]; omega
      · rw [if_neg h1]; split_ifs <;> omega

def reStair (b : ℕ) (f g : ℕ → ℕ) (A : List ℕ) (m : ℕ) : ℕ := m + reStep b f g A A m

def reOff (f g : ℕ → ℕ) (A : List ℕ) (m : ℕ) : ℕ := m + reStep 0 f g A A m

theorem ind_relift (b : ℕ) (f g : ℕ → ℕ) (A0 : List ℕ) (a m : ℕ) :
    b + liftVal (addF f g) A0 a < reStair b f g A0 m ↔ b + liftVal f A0 a < m := by
  rw [liftVal_add]
  unfold reStair
  constructor
  · intro h
    by_contra hc
    have := reStep_le b f g A0 a m (by omega) A0
    omega
  · intro h
    have := reStep_ge b f g A0 a m h A0
    omega

theorem reStep_comp (b : ℕ) (f g g' : ℕ → ℕ) (A0 : List ℕ) (m : ℕ) : ∀ A : List ℕ,
    reStep b (addF f g) g' A0 A (reStair b f g A0 m) = reStep b f g' A0 A m
  | [] => rfl
  | a :: A => by
      simp only [reStep, reStep_comp b f g g' A0 m A]
      by_cases h : b + liftVal f A0 a < m
      · rw [if_pos ((ind_relift b f g A0 a m).mpr h), if_pos h]
      · rw [if_neg (fun h' => h ((ind_relift b f g A0 a m).mp h')), if_neg h]

theorem reStair_stair (b : ℕ) (f g : ℕ → ℕ) (A : List ℕ) : Stair (reStair b f g A) := by
  refine ⟨fun m => by unfold reStair; omega, fun m n hmn => ?_, ?_⟩
  · unfold reStair
    have := reStep_mono b f g A hmn A
    omega
  · unfold reStair; rw [reStep_le_base b f g A (Nat.zero_le b)]

theorem reStair_comp (b : ℕ) (f g g' : ℕ → ℕ) (A : List ℕ) (m : ℕ) :
    reStair b (addF f g) g' A (reStair b f g A m) = reStair b f (addF g g') A m := by
  have e := reStep_comp b f g g' A m A
  show reStair b f g A m + reStep b (addF f g) g' A A (reStair b f g A m)
    = m + reStep b f (addF g g') A A m
  rw [e, reStep_add]
  unfold reStair
  omega

theorem reStair_base (b m : ℕ) (f g : ℕ → ℕ) (A : List ℕ) :
    reStair b f g A (b + m) = b + reOff f g A m := by
  unfold reStair reOff; rw [reStep_base]; omega

theorem reOff_comp (f g g' : ℕ → ℕ) (A : List ℕ) (m : ℕ) :
    reOff (addF f g) g' A (reOff f g A m) = reOff f (addF g g') A m := by
  have := reStair_comp 0 f g g' A m
  unfold reStair reOff at *
  exact this

theorem reOff_mono (f g : ℕ → ℕ) (A : List ℕ) {m n : ℕ} (h : m ≤ n) :
    reOff f g A m ≤ reOff f g A n := by
  unfold reOff; have := reStep_mono 0 f g A h A; omega

/-- 状態 f の値 liftOff f A m をさらに g で持ち上げると、状態 f+g の値。 -/
theorem reOff_liftOff (f g : ℕ → ℕ) (A : List ℕ) (m : ℕ) :
    reOff f g A (liftOff f A m) = liftOff (addF f g) A m := by
  unfold reOff liftOff addF
  rw [stepSum_add]
  have key : ∀ A' : List ℕ, reStep 0 f g A A' (m + stepSum 0 f A m) = stepSum 0 g A' m := by
    intro A'
    induction A' with
    | nil => rfl
    | cons a A' ih =>
        simp only [reStep, stepSum, ih]
        by_cases h : 0 + a < m
        · have h1 : stepSum 0 f A (a + 1) ≤ stepSum 0 f A m := stepSum_mono 0 f (by omega) A
          rw [if_pos (show 0 + liftVal f A a < m + stepSum 0 f A m by unfold liftVal; omega), if_pos h]
        · have h1 : stepSum 0 f A m ≤ stepSum 0 f A (a + 1) := stepSum_mono 0 f (by omega) A
          rw [if_neg (show ¬ 0 + liftVal f A a < m + stepSum 0 f A m by unfold liftVal; omega),
            if_neg h]
  rw [key]
  omega

/-! ## reliftX -/

noncomputable def reliftX (b : ℕ) (f g : ℕ → ℕ) (A : List ℕ) (X : TrioSeq) : TrioSeq :=
  slift X (reStair b f g A)

@[simp] theorem reliftX_length (b : ℕ) (f g : ℕ → ℕ) (A : List ℕ) (X : TrioSeq) :
    (reliftX b f g A X).length = X.length := slift_length _ _

theorem Fr_reliftX {X : TrioSeq} (hX : Fr X) (b : ℕ) (f g : ℕ → ℕ) (A : List ℕ) :
    Fr (reliftX b f g A X) := Fr_slift hX _

theorem Hd_reliftX {U : TrioSeq} (hU : Hd U) (b : ℕ) (f g : ℕ → ℕ) (A : List ℕ) :
    Hd (reliftX b f g A U) := Hd_slift hU _

theorem reliftX_app {W U : TrioSeq} (hW : Fr W) (hU : Hd U) (b : ℕ) (f g : ℕ → ℕ) (A : List ℕ) :
    reliftX b f g A (W ++ U) = reliftX b f g A W ++ reliftX b f g A U := slift_app hW hU _

theorem reliftX_shift0 (d : ℕ) (Z : TrioSeq) (b : ℕ) (f g : ℕ → ℕ) (A : List ℕ) :
    reliftX b f g A (shiftr01 d 0 Z) = shiftr01 d 0 (reliftX b f g A Z) := slift_shift0 d Z _

theorem reliftX_comp (b : ℕ) (f g g' : ℕ → ℕ) (A : List ℕ) (X : TrioSeq) :
    reliftX b (addF f g) g' A (reliftX b f g A X) = reliftX b f (addF g g') A X := by
  unfold reliftX
  rw [slift_slift (reStair_stair b f g A) (reStair_stair b (addF f g) g' A)]
  congr 1
  funext m
  exact reStair_comp b f g g' A m

theorem reliftX_zero (b : ℕ) (f : ℕ → ℕ) (A : List ℕ) (X : TrioSeq) :
    reliftX b f (fun _ => 0) A X = X := by
  unfold reliftX reStair
  simp only [reStep_zeroG, Nat.add_zero]
  exact slift_id X

theorem reliftX_congr (b : ℕ) {f f' g g' : ℕ → ℕ} {A : List ℕ} (hf : ∀ a ∈ A, f a = f' a)
    (hg : ∀ a ∈ A, g a = g' a) (X : TrioSeq) : reliftX b f g A X = reliftX b f' g' A X := by
  unfold reliftX reStair
  congr 1
  funext m
  rw [reStep_congr b m hf hg]

/-- 段の持ち上げと錨の持ち上げは交換する。 -/
theorem mlift_reliftX (b d : ℕ) (f g : ℕ → ℕ) (A : List ℕ) (X : TrioSeq) :
    mlift (reliftX b f g A X) b d = reliftX (b + d) f g A (mlift X b d) := by
  unfold reliftX
  rw [mlift_eq_slift, mlift_eq_slift, slift_slift (reStair_stair b f g A) (stair_step b d),
    slift_slift (stair_step b d) (reStair_stair (b + d) f g A)]
  congr 1
  funext m
  unfold reStair
  by_cases h : b < m
  · have e := reStep_shift b d m f g A A
    simp only [if_pos h]
    rw [if_pos (show b < m + reStep b f g A A m by omega), e]
    omega
  · have e1 := reStep_le_base b f g A (show m ≤ b by omega) A
    have e2 := reStep_le_base (b + d) f g A (show m ≤ b + d by omega) A
    simp [h, e1, e2]

/-! ## 節点の持ち上げ -/

/-- 状態 f で行 1 の値 r より下にある錨。 -/
def lowP (f : ℕ → ℕ) (A : List ℕ) (r : ℕ) : List ℕ := A.filter (fun a => decide (liftVal f A a < r))

theorem mem_lowP {f : ℕ → ℕ} {A : List ℕ} {r a : ℕ} (h : a ∈ lowP f A r) :
    a ∈ A ∧ liftVal f A a < r := by
  unfold lowP at h
  rw [List.mem_filter] at h
  exact ⟨h.1, by simpa using h.2⟩

theorem liftVal_lowP (f : ℕ → ℕ) (A : List ℕ) (r a : ℕ) (ha : liftVal f A a < r) :
    liftVal f (lowP f A r) a = liftVal f A a := by
  show a + stepSum 0 f (lowP f A r) (a + 1) = a + stepSum 0 f A (a + 1)
  unfold lowP
  rw [stepSum_filter 0 (a + 1) f _ (fun a' _ ha' => ?_)]
  have := liftVal_mono f A (show a' ≤ a by omega)
  simpa using (show liftVal f A a' < r by omega)

theorem reStep_cap (b r m : ℕ) (f g : ℕ → ℕ) (A0 : List ℕ) : ∀ A : List ℕ,
    reStep b f g A0 A (min (b + r) m)
      = reStep b f g A0 (A.filter (fun a => decide (liftVal f A0 a < r))) m
  | [] => rfl
  | a :: A => by
      have ih := reStep_cap b r m f g A0 A
      rw [List.filter_cons]
      by_cases hp : liftVal f A0 a < r
      · rw [if_pos (by simpa using hp)]
        simp only [reStep, ih]
        by_cases h1 : b + liftVal f A0 a < m
        · rw [if_pos (by omega), if_pos h1]
        · rw [if_neg (by omega), if_neg h1]
      · rw [if_neg (by simpa using hp)]
        simp only [reStep, ih]
        rw [if_neg (by omega), Nat.zero_add]

/-- ★ 節点の持ち上げ: 節点は reOff で動き、子の並びは節点より下の錨だけで持ち上がる。 -/
theorem reliftX_node {V : TrioSeq} (hV : Fr V) (b r z : ℕ) (f g : ℕ → ℕ) (A : List ℕ) :
    reliftX b f g A (((1, b + r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 V)
      = ((1, b + reOff f g A r, z) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (reliftX b f g (lowP f A r) V) := by
  unfold reliftX
  rw [slift_node hV (b + r) z (reStair_stair b f g A), reStair_base]
  congr 1
  congr 1
  refine congrArg (slift V) (funext fun m => ?_)
  show m + (reStair b f g A (min (b + r) m) - min (b + r) m) = reStair b f g (lowP f A r) m
  unfold reStair
  rw [reStep_cap]
  change m + (min (b + r) m + reStep b f g A (lowP f A r) m - min (b + r) m)
    = m + reStep b f g (lowP f A r) (lowP f A r) m
  rw [reStep_congrA0 b m f g (A1 := lowP f A r)
    (fun a ha => (liftVal_lowP f A r a (mem_lowP ha).2).symm)]
  omega

/-- ★ 入れ子の底に足した節点と子の並びの持ち上げ。 -/
theorem reliftX_bottom {P L : TrioSeq} (hL : Fr L) {d r z : ℕ} (hd : 1 ≤ d) (b : ℕ)
    (hbot : BotGe P d (b + r)) (f g : ℕ → ℕ) (A : List ℕ) :
    reliftX b f g A (P ++ shiftr01 (d - 1) 0 (((1, b + r, z) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L))
      = reliftX b f g A P ++ shiftr01 (d - 1) 0 (((1, b + reOff f g A r, z) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (reliftX b f g (lowP f A r) L)) := by
  have e := reliftX_node hL b r z f g A
  unfold reliftX at e ⊢
  rw [slift_bottom_node hL hd hbot (reStair_stair b f g A)]
  rw [slift_node hL (b + r) z (reStair_stair b f g A)] at e
  rw [e]

theorem reliftX_snoc_bottom {P : TrioSeq} {d s : ℕ} (hd : 1 ≤ d) (b : ℕ)
    (hbot : BotGe P d (b + s)) (f g : ℕ → ℕ) (A : List ℕ) :
    reliftX b f g A (P ++ [((d, b + s, 0) : ℕ × ℕ × ℕ)])
      = reliftX b f g A P ++ [((d, b + reOff f g A s, 0) : ℕ × ℕ × ℕ)] := by
  have e := reliftX_bottom (L := []) (z := 0) (fun x hx => by simp at hx) hd b hbot f g A
  have e1 : ∀ v, shiftr01 (d - 1) 0 [((1, v, 0) : ℕ × ℕ × ℕ)] = [((d, v, 0) : ℕ × ℕ × ℕ)] := by
    intro v; simp [shiftr01]; omega
  simp only [shiftr01, List.map_nil] at e
  simpa [shiftr01, show 1 + (d - 1) = d by omega] using e

/-! ## 錨の列の子の述語 -/

def sumOn (f : ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: A => f a + sumOn f A

/-- 入れ子の底に行 1 の差 s の節点を足す遠い塔の公理（錨の列 A、状態 f の文脈）。
h1, h2 は全ての持ち上げ g と段 b' で仮定する。h2 の子の並びの級は G (f+g) τ。 -/
def FarP (G : (ℕ → ℕ) → ℕ → ℕ → TrioSeq → Prop) (R : (ℕ → ℕ) → ℕ → TrioSeq → Prop)
    (A : List ℕ) (f : ℕ → ℕ) (s : ℕ) : Prop :=
  ∀ (b : ℕ) (P : TrioSeq) (d : ℕ), Fr P → 1 ≤ d → BotGe P d (b + s) →
    (∀ g b', b ≤ b' → R (addF f g) b' (reliftX b' f g A (mlift P b (b' - b)))) →
    (∀ g b', b ≤ b' → ∀ τ L, 1 ≤ τ → τ < reOff f g A s → Fr L → G (addF f g) τ b' L →
      R (addF f g) b' (reliftX b' f g A (mlift P b (b' - b)) ++
        shiftr01 (d - 1) 0 (((1, b' + τ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 L))) →
    R f b (P ++ [((d, b + s, 0) : ℕ × ℕ × ℕ)])

/-- 文脈の族（状態 f で添字づけ）の公理。 -/
def CtxP (G : (ℕ → ℕ) → ℕ → ℕ → TrioSeq → Prop) (A : List ℕ) (o : ℕ)
    (R : (ℕ → ℕ) → ℕ → TrioSeq → Prop) : Prop :=
  ∀ f, SlotAx (R f) ∧
    (∀ f' b X, (∀ a ∈ A, f a = f' a) → R f b X → R f' b X) ∧
    (∀ g b X, Fr X → R f b X → R (addF f g) b (reliftX b f g A X)) ∧
    (∀ s, 2 ≤ s → s ≤ liftOff f A o → FarP G R A f s)

/-- ★ 錨の列 A（元の値）、状態 f で、行 1 の差 o（元の値）の節点の子の並び。 -/
def GpT (A : List ℕ) (o : ℕ) (f : ℕ → ℕ) : ℕ → TrioSeq → Prop :=
  fun b E => ∀ R : (ℕ → ℕ) → ℕ → TrioSeq → Prop,
    CtxP (fun h τ b' L =>
        if hg : (lowP h A τ).length < A.length ∨ ((lowP h A τ).length = A.length ∧
            τ - sumOn h (lowP h A τ) - (lowP h A τ).foldr max 0 < o - A.foldr max 0)
        then GpT (lowP h A τ) (τ - sumOn h (lowP h A τ)) h b' L else True) A o R →
    ∀ g, nslot (R (addF f g)) (liftOff (addF f g) A o) b (reliftX b f g A E)
termination_by (A.length, o - A.foldr max 0)
decreasing_by
  rcases hg with h | ⟨h1, h2⟩
  · exact Prod.Lex.left _ _ h
  · rw [h1]; exact Prod.Lex.right _ h2

/-- 子の並びの級（ガードなし）。 -/
def GC (A : List ℕ) : (ℕ → ℕ) → ℕ → ℕ → TrioSeq → Prop :=
  fun h τ b L => GpT (lowP h A τ) (τ - sumOn h (lowP h A τ)) h b L

theorem FarP_mono {G G' : (ℕ → ℕ) → ℕ → ℕ → TrioSeq → Prop}
    (hG : ∀ h τ b L, G h τ b L → G' h τ b L)
    {R : (ℕ → ℕ) → ℕ → TrioSeq → Prop} {A : List ℕ} {f : ℕ → ℕ} {s : ℕ} (h : FarP G R A f s) :
    FarP G' R A f s :=
  fun b P d hP hd hbot h1 h2 => h b P d hP hd hbot h1
    (fun g b' hb τ L h1τ hτ hL hG1 => h2 g b' hb τ L h1τ hτ hL (hG _ _ _ _ hG1))

theorem CtxP_mono {G G' : (ℕ → ℕ) → ℕ → ℕ → TrioSeq → Prop}
    (hG : ∀ h τ b L, G h τ b L → G' h τ b L)
    {A : List ℕ} {o : ℕ} {R : (ℕ → ℕ) → ℕ → TrioSeq → Prop} (h : CtxP G A o R) : CtxP G' A o R :=
  fun f => ⟨(h f).1, (h f).2.1, (h f).2.2.1, fun s h2 hs => FarP_mono hG ((h f).2.2.2 s h2 hs)⟩

/-- ★ 使う向き: ガードなしの文脈で具体化できる。 -/
theorem GpT_elim {A : List ℕ} {o : ℕ} {f : ℕ → ℕ} {b : ℕ} {E : TrioSeq} (h : GpT A o f b E)
    {R : (ℕ → ℕ) → ℕ → TrioSeq → Prop} (hR : CtxP (GC A) A o R) (g : ℕ → ℕ) :
    nslot (R (addF f g)) (liftOff (addF f g) A o) b (reliftX b f g A E) := by
  rw [GpT] at h
  refine h R (CtxP_mono (fun h' τ b' L hL => ?_) hR) g
  split_ifs <;> first | exact hL | trivial

end GyB
end TRIO
