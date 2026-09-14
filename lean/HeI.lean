/-
HeI.lean: 段つきの木の並び（塊・段 0 のタイ・段 l ≥ 1 の節点）の良さ（生成器の形）。

    TreeOKs c p cl us: 親の段 p、親の集合が段 p の延長で閉じるか cl のもとで、
      塊 ch X は okLowP、段 0 のタイの子は (0, true)、段 l+1 の節点は cl ∧ p < l+1 で子は (l+1, false)。
- Gd_treeL: TreeOKs c p cl us → Gd P pre → Gd P (pre ++ us)（P の性質: PSOK・PSDec・最後の段 p・cl なら閉じる）。
  段 0 のタイは chS0、段 l+1 の節点は chU（空の子は親の集合での上の葉）。
- GoodChtX_snocT: 最後の語の F のタイの子の並びに、TreeOKs u 0 true の木を足す。
-/
import HeH

namespace TRIO
namespace HeI

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HcA HcE HcF HcI HcM HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ
open HeB HeC HeD HeE HeF HeG HeH

mutual
def TreeOK (c : ℕ) : ℕ → Bool → UT → Prop
  | _, _, .ch X => okLowP c X
  | _, _, .tie 0 cs => TreeOKs c 0 true cs
  | p, cl, .tie (l + 1) cs => cl = true ∧ p < l + 1 ∧ TreeOKs c (l + 1) false cs
def TreeOKs (c : ℕ) : ℕ → Bool → List UT → Prop
  | _, _, [] => True
  | p, cl, x :: us => TreeOK c p cl x ∧ TreeOKs c p cl us
end

theorem TreeOKs_nil (c p : ℕ) (cl : Bool) : TreeOKs c p cl [] := trivial

theorem TreeOKs_cons_ch {c p : ℕ} {cl : Bool} {X : TrioSeq} (hX : okLowP c X) {us : List UT}
    (h : TreeOKs c p cl us) : TreeOKs c p cl (UT.ch X :: us) := ⟨hX, h⟩

theorem TreeOKs_cons_tie0 {c p : ℕ} {cl : Bool} {cs : List UT} (hcs : TreeOKs c 0 true cs) {us : List UT}
    (h : TreeOKs c p cl us) : TreeOKs c p cl (UT.tie 0 cs :: us) := ⟨hcs, h⟩

theorem TreeOKs_cons_up {c p l : ℕ} {cl : Bool} (hcl : cl = true) (hpl : p < l + 1) {cs : List UT}
    (hcs : TreeOKs c (l + 1) false cs) {us : List UT} (h : TreeOKs c p cl us) :
    TreeOKs c p cl (UT.tie (l + 1) cs :: us) := ⟨⟨hcl, hpl, hcs⟩, h⟩

/-- 塊の規則（全ての良い集合で）。 -/
theorem Gd_snoc_ch {P : PS} (hP : PSOK P) (hD : PSDec P) {A : List ℕ} {k : ℕ} {H : ℕ → ℕ}
    (hA01 : ∀ a ∈ A, 1 ≤ a) (hk : 1 ≤ k) {c : ℕ} {pre : List UT} (hpre : Gd P A k H c pre)
    {X : TrioSeq} (hX : okLowP c X) : Gd P A k H c (pre ++ [UT.ch X]) := by
  have := (hX.2.2 P hP hD A k hA01 hk H).2.2 c le_rfl pre hpre
  rwa [Nat.sub_self, mlift_zero] at this

section
variable {A : List ℕ} {k : ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk : 1 ≤ k) (hAk : ∀ a ∈ A, a < k) (H : ℕ → ℕ)
include hA01 hk hAk

mutual
theorem Gd_treeU {c : ℕ} : ∀ (x : UT) (P : PS) (p : ℕ) (cl : Bool), PSOK P → PSDec P → LastL P p →
    (cl = true → Ext P p P) → ∀ (pre : List UT), TreeOK c p cl x →
    Gd P A k H c pre → Gd P A k H c (pre ++ [x])
  | .ch X, P, _, _, hP, hD, _, _, pre, hx, hpre => Gd_snoc_ch hP hD hA01 hk hpre hx
  | .tie 0 cs, P, _, _, hP, hD, _, _, pre, hx, hpre => by
      have hcs := Gd_treeL (c := c) cs (chS0 P) 0 true (PSOK_chS0 hP) (PSDec_chS0 P) (LastL_chS0 P)
        (fun _ => chS0_closed P) [] hx (Gd_nil_chS0 hP hD)
      rw [List.nil_append] at hcs
      exact Gd_tie (Ext_chS0 P) hA01 hk hAk hpre hcs
  | .tie (l + 1) cs, P, p, cl, hP, hD, hlast, hcl, pre, hx, hpre => by
      obtain ⟨hcl1, hpl, hx⟩ := hx
      have hcs := Gd_treeL (c := c) cs (chU P (l + 1)) (l + 1) false (PSOK_chU hP (l + 1))
        (PSDec_chU P (l + 1)) (LastL_chU P (l + 1)) (fun h => absurd h (by simp)) [] hx
        (Gd_nil_chU hP (hcl hcl1) hlast hpl)
      rw [List.nil_append] at hcs
      exact Gd_tie (Ext_chU P (l + 1)) hA01 hk hAk hpre hcs
theorem Gd_treeL {c : ℕ} : ∀ (us : List UT) (P : PS) (p : ℕ) (cl : Bool), PSOK P → PSDec P → LastL P p →
    (cl = true → Ext P p P) → ∀ (pre : List UT), TreeOKs c p cl us →
    Gd P A k H c pre → Gd P A k H c (pre ++ us)
  | [], _, _, _, _, _, _, _, pre, _, hpre => by rw [List.append_nil]; exact hpre
  | x :: us, P, p, cl, hP, hD, hlast, hcl, pre, hx, hpre => by
      have := Gd_treeL (c := c) us P p cl hP hD hlast hcl (pre ++ [x]) hx.2
        (Gd_treeU (c := c) x P p cl hP hD hlast hcl pre hx.1 hpre)
      rwa [List.append_assoc, List.singleton_append] at this
end

/-- ★ 段つきの木の並びは F のタイの子の位置 P0 で良い。 -/
theorem Gd_treeP0 {c : ℕ} {us : List UT} (h : TreeOKs c 0 true us) : Gd P0 A k H c us := by
  have := Gd_treeL hA01 hk hAk H us P0 0 true PSOK_P0 PSDec_P0 LastL_P0 (fun _ => P0_closed) [] h Gd_nil_P0
  rwa [List.nil_append] at this

end

/-- ★ 最後の語の F のタイの子の並びに、段つきの木の並びを足す。 -/
theorem GoodChtX_snocT {A0 : List ℕ} {o u : ℕ} (hAo : ∀ a ∈ A0, a < o) (hA01 : ∀ a ∈ A0, 1 ≤ a)
    (ho : 1 ≤ o) {Lds : List (List UT)} (hL : GoodChtX A0 o (fun _ => 0) u Lds) {us : List UT}
    (hus : TreeOKs u 0 true us) : GoodChtX A0 o (fun _ => 0) u (Lds ++ [us]) := by
  have := Gd_P0_good (Gd_treeP0 hA01 ho hAo (fun _ => 0) hus) (EmbU_triv hAo hA01 ho _) le_rfl
    (S := []) hL
  simpa only [imgT_zero] using this

end HeI
end TRIO
