/-
HdA.lean: F のタイの子を木の単位（塊 ch X と、子の並びを持つ F の位置のタイ tie us）にした遠い語の土台（HcI の一般化）。

    unitT b r c : ch X ↦ mlift X c (b − c)、tie us ↦ (1, r, 0) :: (chT b r c us)↑1
    chT b r c us := 単位の語の連結
    FTLt b r c Lds := (1,r,1) :: Lds.flatMap (fun us => (1,r,0) :: (chT b r c us)↑1)
    farWt b r ws := ws.flatMap (fun w => fwH b r (FTLt b r w.2.1 w.1) w.2.1 w.2.2)
    relTs A0 h g c: 塊を reliftX c h g A0 で持ち上げた木の並び

F の位置のタイは入れ子でも級の F の位置 r に置き、持ち上げ・再持ち上げで r と一緒に動く（HcI の none の一般化）。
-/
import HcS

namespace TRIO
namespace HdA

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HbD HbM HbP HcA HcI

/-! ## 木の単位 -/

inductive UT : Type where
  | ch : TrioSeq → UT
  | tie : ℕ → List UT → UT

mutual
noncomputable def unitT (b r c : ℕ) : UT → TrioSeq
  | .ch X => mlift X c (b - c)
  | .tie l us => ((1, r + l, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b r c us)
noncomputable def chT (b r c : ℕ) : List UT → TrioSeq
  | [] => []
  | u :: us => unitT b r c u ++ chT b r c us
end

theorem chT_append (b r c : ℕ) : ∀ (us vs : List UT), chT b r c (us ++ vs) = chT b r c us ++ chT b r c vs
  | [], vs => by simp [chT]
  | u :: us, vs => by
      simp only [List.cons_append, chT, chT_append b r c us vs, List.append_assoc]

theorem chT_snoc (b r c : ℕ) (us : List UT) (u : UT) :
    chT b r c (us ++ [u]) = chT b r c us ++ unitT b r c u := by
  rw [chT_append]; simp [chT]

mutual
def RawT (k : ℕ) : UT → Prop
  | .ch X => Fr X ∧ Hd X ∧ LowC k X
  | .tie _ us => RawTs k us
def RawTs (k : ℕ) : List UT → Prop
  | [] => True
  | u :: us => RawT k u ∧ RawTs k us
end

theorem RawTs_iff {k : ℕ} : ∀ us : List UT, RawTs k us ↔ ∀ u ∈ us, RawT k u
  | [] => by simp [RawTs]
  | u :: us => by simp [RawTs, RawTs_iff us]

theorem RawTs_append {k : ℕ} {us vs : List UT} : RawTs k (us ++ vs) ↔ RawTs k us ∧ RawTs k vs := by
  rw [RawTs_iff, RawTs_iff, RawTs_iff]
  simp only [List.mem_append]
  constructor
  · intro h; exact ⟨fun u hu => h u (Or.inl hu), fun u hu => h u (Or.inr hu)⟩
  · rintro ⟨h1, h2⟩ u (hu | hu)
    · exact h1 u hu
    · exact h2 u hu

theorem RawTs_snoc {k : ℕ} {us : List UT} {u : UT} : RawTs k (us ++ [u]) ↔ RawTs k us ∧ RawT k u := by
  rw [RawTs_append]; simp [RawTs]

theorem RawT_tie {k l : ℕ} {us : List UT} : RawT k (.tie l us) ↔ RawTs k us := by simp [RawT]

mutual
theorem RawT_mono {k k' : ℕ} (hk : k ≤ k') : ∀ u : UT, RawT k u → RawT k' u
  | .ch X, h => ⟨h.1, h.2.1, LowC_mono hk h.2.2⟩
  | .tie _ us, h => RawTs_mono hk us h
theorem RawTs_mono {k k' : ℕ} (hk : k ≤ k') : ∀ us : List UT, RawTs k us → RawTs k' us
  | [], _ => trivial
  | u :: us, h => ⟨RawT_mono hk u h.1, RawTs_mono hk us h.2⟩
end

mutual
theorem Fr_unitT {b r c k : ℕ} : ∀ u : UT, RawT k u → Fr (unitT b r c u)
  | .ch X, h => by simp only [unitT]; exact Fr_mlift h.1 _ _
  | .tie _ _, _ => by simp only [unitT]; exact Fr_node _ _
theorem Fr_chT {b r c k : ℕ} : ∀ us : List UT, RawTs k us → Fr (chT b r c us)
  | [], _ => by simp only [chT]; exact Fr_nil
  | u :: us, h => by
      simp only [chT]
      exact Fr_append (Fr_unitT u h.1) (Fr_chT us h.2)
end

theorem Hd_app {A B : TrioSeq} (hA : Hd A) (hB : Hd B) : Hd (A ++ B) := by
  intro hne
  by_cases hA0 : A = []
  · subst hA0
    simp only [List.nil_append] at hne ⊢
    exact hB hne
  · rw [Small.entry_append_left (List.length_pos_iff.mpr hA0)]; exact hA hA0

theorem Hd_unitT {b r c k : ℕ} : ∀ u : UT, RawT k u → Hd (unitT b r c u)
  | .ch X, h => by simp only [unitT]; exact Hd_mlift h.2.1 _ _
  | .tie _ _, _ => by simp only [unitT]; exact Hd_node _ _

theorem Hd_chT {b r c k : ℕ} : ∀ us : List UT, RawTs k us → Hd (chT b r c us)
  | [], _ => fun h => absurd rfl h
  | u :: us, h => by
      simp only [chT]
      exact Hd_app (Hd_unitT u h.1) (Hd_chT us h.2)

/-! ## 持ち上げ -/

mutual
theorem mlift_unitT_base {b r c k : ℕ} (hbr : b < r) (hcb : c ≤ b) (t : ℕ) :
    ∀ u : UT, RawT k u → mlift (unitT b r c u) b t = unitT (b + t) (r + t) c u
  | .ch X, _ => by
      simp only [unitT]
      have e2 := mlift_mlift X c (b - c) t
      rw [show c + (b - c) = b by omega] at e2
      rw [e2, show b - c + t = b + t - c by omega]
  | .tie l us, h => by
      simp only [unitT]
      rw [mlift_node (show b < r + l by omega) (Fr_chT us h), mlift_chT_base hbr hcb t us h,
        show r + l + t = r + t + l by omega]
theorem mlift_chT_base {b r c k : ℕ} (hbr : b < r) (hcb : c ≤ b) (t : ℕ) :
    ∀ us : List UT, RawTs k us → mlift (chT b r c us) b t = chT (b + t) (r + t) c us
  | [], _ => by simp [chT, mlift_nil]
  | u :: us, h => by
      simp only [chT]
      rw [mlift_app (Fr_unitT u h.1) (Hd_chT us h.2), mlift_unitT_base hbr hcb t u h.1,
        mlift_chT_base hbr hcb t us h.2]
end

mutual
theorem mlift_unitT_high {b v r c K : ℕ} (hv : b + K ≤ v) (hvr : v < r) (hcb : c ≤ b) (t : ℕ) :
    ∀ u : UT, RawT (c + K) u → mlift (unitT b r c u) v t = unitT b (r + t) c u
  | .ch X, h => by
      simp only [unitT]
      have hLv : LowC v (mlift X c (b - c)) :=
        LowC_mono (by omega) (LowC_mliftk h.2.2 (b - c))
      have e := mlift_append_low (A := []) hLv t
      simpa [mlift_nil] using e
  | .tie l us, h => by
      simp only [unitT]
      rw [mlift_node (show v < r + l by omega) (Fr_chT us h), mlift_chT_high hv hvr hcb t us h,
        show r + l + t = r + t + l by omega]
theorem mlift_chT_high {b v r c K : ℕ} (hv : b + K ≤ v) (hvr : v < r) (hcb : c ≤ b) (t : ℕ) :
    ∀ us : List UT, RawTs (c + K) us → mlift (chT b r c us) v t = chT b (r + t) c us
  | [], _ => by simp [chT, mlift_nil]
  | u :: us, h => by
      simp only [chT]
      rw [mlift_app (Fr_unitT u h.1) (Hd_chT us h.2), mlift_unitT_high hv hvr hcb t u h.1,
        mlift_chT_high hv hvr hcb t us h.2]
end

/-! ## 塊の再持ち上げ -/

mutual
noncomputable def relT (A0 : List ℕ) (h g : ℕ → ℕ) (c : ℕ) : UT → UT
  | .ch X => .ch (reliftX c h g A0 X)
  | .tie l us => .tie l (relTs A0 h g c us)
noncomputable def relTs (A0 : List ℕ) (h g : ℕ → ℕ) (c : ℕ) : List UT → List UT
  | [] => []
  | u :: us => relT A0 h g c u :: relTs A0 h g c us
end

theorem relTs_append (A0 : List ℕ) (h g : ℕ → ℕ) (c : ℕ) :
    ∀ us vs : List UT, relTs A0 h g c (us ++ vs) = relTs A0 h g c us ++ relTs A0 h g c vs
  | [], vs => by simp [relTs]
  | u :: us, vs => by simp only [List.cons_append, relTs, relTs_append A0 h g c us vs]

theorem relTs_snoc (A0 : List ℕ) (h g : ℕ → ℕ) (c : ℕ) (us : List UT) (u : UT) :
    relTs A0 h g c (us ++ [u]) = relTs A0 h g c us ++ [relT A0 h g c u] := by
  rw [relTs_append]; simp [relTs]

mutual
theorem relT_comp (A0 : List ℕ) (H g g' : ℕ → ℕ) (c : ℕ) :
    ∀ u : UT, relT A0 (addF H g) g' c (relT A0 H g c u) = relT A0 H (addF g g') c u
  | .ch X => by simp only [relT, reliftX_comp]
  | .tie _ us => by simp only [relT, relTs_comp A0 H g g' c us]
theorem relTs_comp (A0 : List ℕ) (H g g' : ℕ → ℕ) (c : ℕ) :
    ∀ us : List UT, relTs A0 (addF H g) g' c (relTs A0 H g c us) = relTs A0 H (addF g g') c us
  | [] => by simp [relTs]
  | u :: us => by simp only [relTs, relT_comp A0 H g g' c u, relTs_comp A0 H g g' c us]
end

mutual
theorem relT_zero (A0 : List ℕ) (H : ℕ → ℕ) (c : ℕ) : ∀ u : UT, relT A0 H (fun _ => 0) c u = u
  | .ch X => by simp only [relT, reliftX_zero]
  | .tie _ us => by simp only [relT, relTs_zero A0 H c us]
theorem relTs_zero (A0 : List ℕ) (H : ℕ → ℕ) (c : ℕ) : ∀ us : List UT, relTs A0 H (fun _ => 0) c us = us
  | [] => by simp [relTs]
  | u :: us => by simp only [relTs, relT_zero A0 H c u, relTs_zero A0 H c us]
end

mutual
theorem relT_congr {H H' : ℕ → ℕ} {A0 : List ℕ} (hH : ∀ a ∈ A0, H a = H' a) (g : ℕ → ℕ) (c : ℕ) :
    ∀ u : UT, relT A0 H g c u = relT A0 H' g c u
  | .ch X => by simp only [relT, reliftX_congr c hH (fun _ _ => rfl) X]
  | .tie _ us => by simp only [relT, relTs_congr hH g c us]
theorem relTs_congr {H H' : ℕ → ℕ} {A0 : List ℕ} (hH : ∀ a ∈ A0, H a = H' a) (g : ℕ → ℕ) (c : ℕ) :
    ∀ us : List UT, relTs A0 H g c us = relTs A0 H' g c us
  | [] => by simp [relTs]
  | u :: us => by simp only [relTs, relT_congr hH g c u, relTs_congr hH g c us]
end

mutual
theorem RawT_relT {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {c : ℕ} (g : ℕ → ℕ) :
    ∀ u : UT, RawT (c + reOff (fun _ => 0) h A0 k0) u →
      RawT (c + reOff (fun _ => 0) (addF h g) A0 k0) (relT A0 h g c u)
  | .ch X, hX => by
      simp only [relT, RawT]
      refine ⟨Fr_reliftX hX.1 _ _ _ _, Hd_reliftX hX.2.1 _ _ _ _, ?_⟩
      have := LowC_reliftX hX.2.2 h g A0
      rwa [reOff_zero_comp] at this
  | .tie _ us, hu => by
      simp only [relT, RawT]
      exact RawTs_relTs g us hu
theorem RawTs_relTs {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {c : ℕ} (g : ℕ → ℕ) :
    ∀ us : List UT, RawTs (c + reOff (fun _ => 0) h A0 k0) us →
      RawTs (c + reOff (fun _ => 0) (addF h g) A0 k0) (relTs A0 h g c us)
  | [], _ => by simp [relTs, RawTs]
  | u :: us, h' => by
      simp only [relTs, RawTs]
      exact ⟨RawT_relT g u h'.1, RawTs_relTs g us h'.2⟩
end

mutual
theorem reliftX_unitTA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {f f0 : ℕ → ℕ} (hf : ∀ a ∈ A0, f a = f0 a)
    (g : ℕ → ℕ) {K c : ℕ} (hK : ∀ s ∈ S, K ≤ liftVal f (S ++ A0) s) (hcb : c ≤ b) :
    ∀ u : UT, RawT (c + K) u →
    reliftX b f g (S ++ A0) (unitT b (b + liftOff f (S ++ A0) o + 1) c u)
      = unitT b (b + liftOff (addF f g) (S ++ A0) o + 1) c (relT A0 f0 g c u)
  | .ch X, h => by
      simp only [unitT, relT]
      have hL' : LowC (b + K) (mlift X c (b - c)) := by
        have := LowC_mliftk h.2.2 (b - c)
        rwa [show c + K + (b - c) = b + K by omega] at this
      rw [reliftX_ins_low hSA hf b g hK hL']
      have em := mlift_reliftX c (b - c) f0 g A0 X
      rw [show c + (b - c) = b by omega] at em
      rw [em]
  | .tie l us, h => by
      simp only [unitT, relT]
      have hlow : lowP f (S ++ A0) (liftOff f (S ++ A0) o + (1 + l)) = S ++ A0 :=
        lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
      have e1 := reliftX_node (Fr_chT (b := b) (r := b + liftOff f (S ++ A0) o + 1) (c := c) us h) b
        (liftOff f (S ++ A0) o + (1 + l)) 0 f g (S ++ A0)
      rw [hlow, reOff_above hA f g (1 + l),
        show b + (liftOff f (S ++ A0) o + (1 + l)) = b + liftOff f (S ++ A0) o + 1 + l by omega,
        show b + (liftOff (addF f g) (S ++ A0) o + (1 + l)) = b + liftOff (addF f g) (S ++ A0) o + 1 + l by omega] at e1
      rw [e1, reliftX_chTA hA hSA b hf g hK hcb us h]
theorem reliftX_chTA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {f f0 : ℕ → ℕ} (hf : ∀ a ∈ A0, f a = f0 a)
    (g : ℕ → ℕ) {K c : ℕ} (hK : ∀ s ∈ S, K ≤ liftVal f (S ++ A0) s) (hcb : c ≤ b) :
    ∀ us : List UT, RawTs (c + K) us →
    reliftX b f g (S ++ A0) (chT b (b + liftOff f (S ++ A0) o + 1) c us)
      = chT b (b + liftOff (addF f g) (S ++ A0) o + 1) c (relTs A0 f0 g c us)
  | [], _ => by simp [chT, relTs, reliftX, slift_nil]
  | u :: us, h => by
      simp only [chT, relTs]
      rw [reliftX_app (Fr_unitT u h.1) (Hd_chT us h.2), reliftX_unitTA hA hSA b hf g hK hcb u h.1,
        reliftX_chTA hA hSA b hf g hK hcb us h.2]
end

/-! ## 頭 -/

noncomputable def FTLt (b r c : ℕ) (Lds : List (List UT)) : TrioSeq :=
  ((1, r, 1) : ℕ × ℕ × ℕ) ::
    Lds.flatMap (fun us => ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b r c us))

theorem FTLt_snoc (b r c : ℕ) (Lds : List (List UT)) (us : List UT) :
    FTLt b r c (Lds ++ [us]) = FTLt b r c Lds ++ ((1, r, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b r c us) := by
  simp [FTLt, List.flatMap_append]

theorem Fr_FTLt (b r c : ℕ) (Lds : List (List UT)) : Fr (FTLt b r c Lds) := by
  intro x hx
  simp only [FTLt, List.mem_cons, List.mem_flatMap] at hx
  rcases hx with rfl | ⟨us, -, hx⟩
  · exact Nat.le_refl 1
  · rcases hx with rfl | hx
    · exact Nat.le_refl 1
    · simp only [shiftr01, List.mem_map] at hx
      obtain ⟨p, -, rfl⟩ := hx
      dsimp only; omega

theorem mlift_FTLt_high {b v r c K : ℕ} (hv : b + K ≤ v) (hvr : v < r) (hcb : c ≤ b) (t : ℕ) :
    ∀ Lds : List (List UT), (∀ us ∈ Lds, RawTs (c + K) us) →
      mlift (FTLt b r c Lds) v t = FTLt b (r + t) c Lds := by
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil => intro _; simpa [FTLt] using mlift_one hvr t
  | append_singleton Lds us ih =>
      intro hL
      have hus := hL us (List.mem_append_right _ (List.mem_singleton_self _))
      rw [FTLt_snoc, FTLt_snoc, mlift_app (Fr_FTLt _ _ _ _) (Hd_node _ _),
        ih (fun L hL' => hL L (List.mem_append_left _ hL')), mlift_node hvr (Fr_chT us hus),
        mlift_chT_high hv hvr hcb t us hus]

theorem mlift_FTLt_base {b r c k : ℕ} (hbr : b < r) (hcb : c ≤ b) (t : ℕ) :
    ∀ Lds : List (List UT), (∀ us ∈ Lds, RawTs k us) →
      mlift (FTLt b r c Lds) b t = FTLt (b + t) (r + t) c Lds := by
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil => intro _; simpa [FTLt] using mlift_one hbr t
  | append_singleton Lds us ih =>
      intro hL
      have hus := hL us (List.mem_append_right _ (List.mem_singleton_self _))
      rw [FTLt_snoc, FTLt_snoc, mlift_app (Fr_FTLt _ _ _ _) (Hd_node _ _),
        ih (fun L hL' => hL L (List.mem_append_left _ hL')), mlift_node hbr (Fr_chT us hus),
        mlift_chT_base hbr hcb t us hus]

theorem reliftX_FTLtA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {f f0 : ℕ → ℕ} (hf : ∀ a ∈ A0, f a = f0 a)
    (g : ℕ → ℕ) {K c : ℕ} (hK : ∀ s ∈ S, K ≤ liftVal f (S ++ A0) s) (hcb : c ≤ b) :
    ∀ Lds : List (List UT), (∀ us ∈ Lds, RawTs (c + K) us) →
    reliftX b f g (S ++ A0) (FTLt b (b + liftOff f (S ++ A0) o + 1) c Lds)
      = FTLt b (b + liftOff (addF f g) (S ++ A0) o + 1) c (Lds.map (relTs A0 f0 g c)) := by
  have hlow : lowP f (S ++ A0) (liftOff f (S ++ A0) o + 1) = S ++ A0 :=
    lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
  intro Lds
  induction Lds using List.reverseRecOn with
  | nil =>
      intro _
      have := reliftX_one b (liftOff f (S ++ A0) o + 1) 1 f g (S ++ A0)
      rw [reOff_above hA f g 1] at this
      simpa [FTLt, ← Nat.add_assoc] using this
  | append_singleton Lds us ih =>
      intro hL
      have hus := hL us (List.mem_append_right _ (List.mem_singleton_self _))
      rw [List.map_append, List.map_singleton, FTLt_snoc, FTLt_snoc,
        reliftX_app (Fr_FTLt _ _ _ _) (Hd_node _ _),
        ih (fun L hL'' => hL L (List.mem_append_left _ hL''))]
      have e1 := reliftX_node (Fr_chT (b := b) (r := b + liftOff f (S ++ A0) o + 1) (c := c) us hus) b
        (liftOff f (S ++ A0) o + 1) 0 f g (S ++ A0)
      rw [hlow, reOff_above hA f g 1, show b + (liftOff f (S ++ A0) o + 1) = b + liftOff f (S ++ A0) o + 1 by omega,
        show b + (liftOff (addF f g) (S ++ A0) o + 1) = b + liftOff (addF f g) (S ++ A0) o + 1 by omega] at e1
      rw [e1, reliftX_chTA hA hSA b hf g hK hcb us hus]

/-! ## 語と並び -/

noncomputable def farWt (b r : ℕ) (ws : List (List (List UT) × ℕ × TrioSeq)) : TrioSeq :=
  ws.flatMap (fun w => fwH b r (FTLt b r w.2.1 w.1) w.2.1 w.2.2)

theorem farWt_cons (b r : ℕ) (w : List (List UT) × ℕ × TrioSeq)
    (ws : List (List (List UT) × ℕ × TrioSeq)) :
    farWt b r (w :: ws) = fwH b r (FTLt b r w.2.1 w.1) w.2.1 w.2.2 ++ farWt b r ws := by
  simp [farWt]

theorem farWt_snoc (b r : ℕ) (ws : List (List (List UT) × ℕ × TrioSeq))
    (w : List (List UT) × ℕ × TrioSeq) :
    farWt b r (ws ++ [w]) = farWt b r ws ++ fwH b r (FTLt b r w.2.1 w.1) w.2.1 w.2.2 := by
  simp [farWt, List.flatMap_append]

theorem Fr_farWt (b r : ℕ) (ws : List (List (List UT) × ℕ × TrioSeq)) : Fr (farWt b r ws) := by
  intro y hy
  simp only [farWt, List.mem_flatMap] at hy
  obtain ⟨w, -, hy⟩ := hy
  exact Fr_fwH b r _ w.2.1 w.2.2 y hy

theorem Hd_farWt (b r : ℕ) : ∀ ws : List (List (List UT) × ℕ × TrioSeq), Hd (farWt b r ws)
  | [] => fun h => absurd rfl h
  | w :: ws => fun _ => by rw [farWt_cons]; rfl

theorem farWt_rep (b r : ℕ) (ws : List (List (List UT) × ℕ × TrioSeq)) (w : List (List UT) × ℕ × TrioSeq) :
    ∀ m, farWt b r (ws ++ List.replicate m w)
      = farWt b r ws ++ (List.range m).flatMap (fun _ => fwH b r (FTLt b r w.2.1 w.1) w.2.1 w.2.2)
  | 0 => by simp [farWt]
  | m + 1 => by
      rw [List.replicate_succ', ← List.append_assoc, farWt_snoc, farWt_rep b r ws w m,
        List.range_succ, List.flatMap_append, List.append_assoc]
      simp

theorem mlift_fwt_highk {b v r c k : ℕ} (hv : b + k ≤ v) (hvr : v < r) (hcb : c ≤ b)
    {Lds : List (List UT)} (hL : ∀ us ∈ Lds, RawTs (c + k) us)
    {Y : TrioSeq} (hY : Fr Y) (hLY : LowC (c + k) Y) (t : ℕ) :
    mlift (fwH b r (FTLt b r c Lds) c Y) v t = fwH b (r + t) (FTLt b (r + t) c Lds) c Y := by
  unfold fwH
  rw [mlift_letter hvr (Fr_append (Fr_FTLt _ _ _ _) (Fr_mlift hY c (b - c))) t]
  have hL' : LowC v (mlift Y c (b - c)) := LowC_mono (by omega) (LowC_mliftk hLY (b - c))
  rw [mlift_append_low (A := FTLt b r c Lds) hL' t, mlift_FTLt_high hv hvr hcb t Lds hL]

theorem mlift_fwt_base {b r c k : ℕ} (hbr : b < r) (hcb : c ≤ b) {Lds : List (List UT)}
    (hL : ∀ us ∈ Lds, RawTs k us) {Y : TrioSeq} (hY : Fr Y) (hH : Hd Y) (t : ℕ) :
    mlift (fwH b r (FTLt b r c Lds) c Y) b t
      = fwH (b + t) (r + t) (FTLt (b + t) (r + t) c Lds) c Y := by
  unfold fwH
  rw [mlift_letter hbr (Fr_append (Fr_FTLt _ _ _ _) (Fr_mlift hY c (b - c))) t,
    mlift_app (Fr_FTLt _ _ _ _) (Hd_mlift hH c (b - c)) b t, mlift_FTLt_base hbr hcb t Lds hL]
  have e2 := mlift_mlift Y c (b - c) t
  rw [show c + (b - c) = b by omega] at e2
  rw [e2, show b - c + t = b + t - c by omega]

theorem reliftX_fwtA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {f f0 : ℕ → ℕ} (hf : ∀ a ∈ A0, f a = f0 a)
    (g : ℕ → ℕ) {K c : ℕ} (hK : ∀ s ∈ S, K ≤ liftVal f (S ++ A0) s) (hcb : c ≤ b)
    {Lds : List (List UT)} (hL : ∀ us ∈ Lds, RawTs (c + K) us)
    {Y : TrioSeq} (hY : Fr Y) (hH : Hd Y) (hLY : LowC (c + K) Y) :
    reliftX b f g (S ++ A0)
        (fwH b (b + liftOff f (S ++ A0) o + 1) (FTLt b (b + liftOff f (S ++ A0) o + 1) c Lds) c Y)
      = fwH b (b + liftOff (addF f g) (S ++ A0) o + 1)
          (FTLt b (b + liftOff (addF f g) (S ++ A0) o + 1) c (Lds.map (relTs A0 f0 g c))) c
          (reliftX c f0 g A0 Y) := by
  have hlow : lowP f (S ++ A0) (liftOff f (S ++ A0) o + 1) = S ++ A0 :=
    lowP_all (fun a ha => by have := liftVal_lt_liftOff (f := f) hA ha; omega)
  have hL' : LowC (b + K) (mlift Y c (b - c)) := by
    have := LowC_mliftk hLY (b - c)
    rwa [show c + K + (b - c) = b + K by omega] at this
  have eH := reliftX_FTLtA hA hSA b hf g hK hcb Lds hL
  unfold fwH
  rw [show b + liftOff f (S ++ A0) o + 1 = b + (liftOff f (S ++ A0) o + 1) by omega] at eH ⊢
  rw [reliftX_node (Fr_append (Fr_FTLt _ _ _ _) (Fr_mlift hY c (b - c))) b
      (liftOff f (S ++ A0) o + 1) 1 f g (S ++ A0),
    hlow, reOff_above hA f g 1, reliftX_app (Fr_FTLt _ _ _ _) (Hd_mlift hH _ _), eH,
    reliftX_ins_low hSA hf b g hK hL']
  have em := mlift_reliftX c (b - c) f0 g A0 Y
  rw [show c + (b - c) = b by omega] at em
  rw [← em]
  simp only [← Nat.add_assoc]

/-! ## 低さの条件 -/

def RawWkt (k b : ℕ) (w : List (List UT) × ℕ × TrioSeq) : Prop :=
  w.2.1 ≤ b ∧ (∀ us ∈ w.1, RawTs (w.2.1 + k) us) ∧ Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + k) w.2.2

def RawWskt (k b : ℕ) (ws : List (List (List UT) × ℕ × TrioSeq)) : Prop :=
  ∀ w ∈ ws, RawWkt k b w

theorem RawWskt_mono {k b b' : ℕ} (h : b ≤ b') {ws : List (List (List UT) × ℕ × TrioSeq)}
    (hR : RawWskt k b ws) : RawWskt k b' ws := fun w hw =>
  ⟨le_trans (hR w hw).1 h, (hR w hw).2⟩

theorem RawWskt_tail {k b : ℕ} {w : List (List UT) × ℕ × TrioSeq}
    {ws : List (List (List UT) × ℕ × TrioSeq)} (hR : RawWskt k b (w :: ws)) :
    RawWskt k b ws := fun w' h => hR w' (List.mem_cons_of_mem _ h)

theorem mlift_farWt_highk {k b v r : ℕ} (hv : b + k ≤ v) (hvr : v < r) (t : ℕ) :
    ∀ ws, RawWskt k b ws → mlift (farWt b r ws) v t = farWt b (r + t) ws
  | [] => fun _ => by simp [farWt, mlift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      rw [farWt_cons, farWt_cons, mlift_app (Fr_fwH _ _ _ _ _) (Hd_farWt b r ws),
        mlift_fwt_highk hv hvr hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.2 t,
        mlift_farWt_highk hv hvr t ws (RawWskt_tail hR)]

theorem mlift_farWt_basek {k b r : ℕ} (hbr : b < r) (t : ℕ) :
    ∀ ws, RawWskt k b ws → mlift (farWt b r ws) b t = farWt (b + t) (r + t) ws
  | [] => fun _ => by simp [farWt, mlift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      rw [farWt_cons, farWt_cons, mlift_app (Fr_fwH _ _ _ _ _) (Hd_farWt b r ws),
        mlift_fwt_base hbr hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 t,
        mlift_farWt_basek hbr t ws (RawWskt_tail hR)]

/-! ## 持ち上げた子と中身の並び -/

noncomputable def relWst (A0 : List ℕ) (h g : ℕ → ℕ) (ws : List (List (List UT) × ℕ × TrioSeq)) :
    List (List (List UT) × ℕ × TrioSeq) :=
  ws.map (fun w => (w.1.map (relTs A0 h g w.2.1), w.2.1, reliftX w.2.1 h g A0 w.2.2))

def RawWAt (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b : ℕ) (w : List (List UT) × ℕ × TrioSeq) : Prop :=
  w.2.1 ≤ b ∧ (∀ us ∈ w.1, RawTs (w.2.1 + reOff (fun _ => 0) h A0 k0) us) ∧
    Fr w.2.2 ∧ Hd w.2.2 ∧ LowC (w.2.1 + reOff (fun _ => 0) h A0 k0) w.2.2

def RawWsAt (A0 : List ℕ) (k0 : ℕ) (h : ℕ → ℕ) (b : ℕ) (ws : List (List (List UT) × ℕ × TrioSeq)) : Prop :=
  ∀ w ∈ ws, RawWAt A0 k0 h b w

theorem RawWsAt_mono {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b b' : ℕ} (hbb : b ≤ b')
    {ws : List (List (List UT) × ℕ × TrioSeq)} (hR : RawWsAt A0 k0 h b ws) : RawWsAt A0 k0 h b' ws :=
  fun w hw => ⟨le_trans (hR w hw).1 hbb, (hR w hw).2⟩

theorem RawWsAt_snoc {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b : ℕ}
    {ws : List (List (List UT) × ℕ × TrioSeq)} {w : List (List UT) × ℕ × TrioSeq}
    (h : RawWsAt A0 k0 H b ws) (hw : RawWAt A0 k0 H b w) : RawWsAt A0 k0 H b (ws ++ [w]) := by
  intro w' h'
  rcases List.mem_append.mp h' with h' | h'
  · exact h w' h'
  · simp at h'; subst h'; exact hw

theorem RawLdst_relift {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {c : ℕ} {Lds : List (List UT)}
    (hL : ∀ us ∈ Lds, RawTs (c + reOff (fun _ => 0) h A0 k0) us) (g : ℕ → ℕ) :
    ∀ us ∈ Lds.map (relTs A0 h g c), RawTs (c + reOff (fun _ => 0) (addF h g) A0 k0) us := by
  intro us hus
  simp only [List.mem_map] at hus
  obtain ⟨us0, hus0, rfl⟩ := hus
  exact RawTs_relTs g us0 (hL us0 hus0)

theorem RawWskt_relWst {A0 : List ℕ} {k0 : ℕ} {h : ℕ → ℕ} {b : ℕ}
    {ws : List (List (List UT) × ℕ × TrioSeq)} (hR : RawWsAt A0 k0 h b ws) (g : ℕ → ℕ) :
    RawWskt (reOff (fun _ => 0) (addF h g) A0 k0) b (relWst A0 h g ws) := by
  intro w hw
  simp only [relWst, List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  have h0 := hR w0 hw0
  refine ⟨h0.1, RawLdst_relift h0.2.1 g, Fr_reliftX h0.2.2.1 _ _ _ _, Hd_reliftX h0.2.2.2.1 _ _ _ _, ?_⟩
  have := LowC_reliftX h0.2.2.2.2 h g A0
  rwa [reOff_zero_comp] at this

theorem RawWsAt_relWst {A0 : List ℕ} {k0 : ℕ} {H : ℕ → ℕ} {b : ℕ}
    {ws : List (List (List UT) × ℕ × TrioSeq)} (hR : RawWsAt A0 k0 H b ws) (g : ℕ → ℕ) :
    RawWsAt A0 k0 (addF H g) b (relWst A0 H g ws) := by
  intro w hw
  simp only [relWst, List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  have h0 := hR w0 hw0
  refine ⟨h0.1, RawLdst_relift h0.2.1 g, Fr_reliftX h0.2.2.1 _ _ _ _, Hd_reliftX h0.2.2.2.1 _ _ _ _, ?_⟩
  have := LowC_reliftX h0.2.2.2.2 H g A0
  rwa [reOff_zero_comp] at this

theorem relWst_snoc (A0 : List ℕ) (H g : ℕ → ℕ) (ws : List (List (List UT) × ℕ × TrioSeq))
    (Lds : List (List UT)) (u : ℕ) (X : TrioSeq) :
    relWst A0 H g (ws ++ [(Lds, u, X)])
      = relWst A0 H g ws ++ [(Lds.map (relTs A0 H g u), u, reliftX u H g A0 X)] := by
  simp [relWst]

theorem relWst_rep (A0 : List ℕ) (H g : ℕ → ℕ) (ws : List (List (List UT) × ℕ × TrioSeq))
    (Lds : List (List UT)) (u : ℕ) (W : TrioSeq) (m : ℕ) :
    relWst A0 H g (ws ++ List.replicate m (Lds, u, W))
      = relWst A0 H g ws ++ List.replicate m (Lds.map (relTs A0 H g u), u, reliftX u H g A0 W) := by
  simp [relWst, List.map_replicate]

theorem relWst_comp (A0 : List ℕ) (H g g' : ℕ → ℕ) (ws : List (List (List UT) × ℕ × TrioSeq)) :
    relWst A0 (addF H g) g' (relWst A0 H g ws) = relWst A0 H (addF g g') ws := by
  simp only [relWst, List.map_map, Function.comp_def, reliftX_comp, relTs_comp]

theorem relWst_zero (A0 : List ℕ) (H : ℕ → ℕ) (ws : List (List (List UT) × ℕ × TrioSeq)) :
    relWst A0 H (fun _ => 0) ws = ws := by
  have e : ∀ c, relTs A0 H (fun _ => 0) c = id := fun c => funext (fun us => relTs_zero A0 H c us)
  simp [relWst, e, reliftX_zero]

theorem relWst_congr {H H' : ℕ → ℕ} {A0 : List ℕ} (hH : ∀ a ∈ A0, H a = H' a) (g : ℕ → ℕ)
    (ws : List (List (List UT) × ℕ × TrioSeq)) : relWst A0 H g ws = relWst A0 H' g ws := by
  unfold relWst
  refine List.map_congr_left (fun w _ => ?_)
  have e : relTs A0 H g w.2.1 = relTs A0 H' g w.2.1 := funext (fun us => relTs_congr hH g w.2.1 us)
  rw [e, reliftX_congr w.2.1 hH (fun _ _ => rfl) w.2.2]

theorem reliftX_farWtA {S A0 : List ℕ} {o : ℕ} (hA : ∀ a ∈ S ++ A0, a < o)
    (hSA : ∀ s ∈ S, ∀ a ∈ A0, a < s) (b : ℕ) {k0 : ℕ} {h g f : ℕ → ℕ}
    (hf : ∀ a ∈ A0, f a = addF h g a) (g' : ℕ → ℕ)
    (hK : ∀ s ∈ S, reOff (fun _ => 0) (addF h g) A0 k0 ≤ liftVal f (S ++ A0) s) :
    ∀ ws, RawWsAt A0 k0 h b ws →
    reliftX b f g' (S ++ A0) (farWt b (b + liftOff f (S ++ A0) o + 1) (relWst A0 h g ws))
      = farWt b (b + liftOff (addF f g') (S ++ A0) o + 1) (relWst A0 h (addF g g') ws)
  | [] => fun _ => by simp [farWt, relWst, reliftX, slift_nil]
  | w :: ws => fun hR => by
      have hw := hR w (by simp)
      have hR' : RawWsAt A0 k0 h b ws := fun w' h' => hR w' (List.mem_cons_of_mem _ h')
      rw [show relWst A0 h g (w :: ws)
          = (w.1.map (relTs A0 h g w.2.1), w.2.1, reliftX w.2.1 h g A0 w.2.2) :: relWst A0 h g ws from rfl,
        show relWst A0 h (addF g g') (w :: ws)
          = (w.1.map (relTs A0 h (addF g g') w.2.1), w.2.1, reliftX w.2.1 h (addF g g') A0 w.2.2) ::
            relWst A0 h (addF g g') ws from rfl,
        farWt_cons, farWt_cons, reliftX_app (Fr_fwH _ _ _ _ _) (Hd_farWt _ _ _)]
      have hL : LowC (w.2.1 + reOff (fun _ => 0) (addF h g) A0 k0) (reliftX w.2.1 h g A0 w.2.2) := by
        have := LowC_reliftX hw.2.2.2.2 h g A0
        rwa [reOff_zero_comp] at this
      rw [reliftX_fwtA hA hSA b hf g' hK hw.1 (RawLdst_relift hw.2.1 g) (Fr_reliftX hw.2.2.1 _ _ _ _)
          (Hd_reliftX hw.2.2.2.1 _ _ _ _) hL]
      simp only [List.map_map, Function.comp_def, reliftX_comp, relTs_comp]
      rw [reliftX_farWtA hA hSA b hf g' hK ws hR']

end HdA
end TRIO
