/-
PmC.lean: 深い葉を「任意の接頭辞の後ろ」に置く基盤（行1693 へ）。

1. 核の補題の一般化: HeN.upleaf_deep_coreDT / HeQ.upleaf_deep_coreD の仮定 hD1（D の全列の行1 ≥ m）を
   「葉の行1の親が R 内に無い」に弱める。R = E ++ [(1,m,0),(d0,m,0)]（E は Fr）ならこれは常に成り立つ。
2. 塔の等式: 接頭辞 pre の後ろの深い葉の塔は Lt pre j（pre ++ [tie 1 [tie 0 (Lt pre (j-1))]]）。
-/
import PmB

namespace TRIO
namespace PmC

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzJ GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HbU HbV HbX HcA HcI HcM
open HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ HdQ HdR HeK

/-! ## 1. 葉の行1の親は R 内に無い -/

/-- ★ R = E ++ [(1,m,0),(d0,m,0)]、E の行0 ≥ 1 なら、最後の列の行1の親は R 内に無い。 -/
theorem hnp_E {E : TrioSeq} (hE : Fr E) (m d0 : ℕ) :
    ¬ hasParent (E ++ [((1, m, 0) : ℕ × ℕ × ℕ), ((d0, m, 0) : ℕ × ℕ × ℕ)]) 1 (E.length + 1) := by
  rintro ⟨k, hk, -⟩
  have hk' : nextrel1 (E ++ [((1, m, 0) : ℕ × ℕ × ℕ), ((d0, m, 0) : ℕ × ℕ × ℕ)]) k (E.length + 1) := by
    unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
  obtain ⟨-, -, hklt, hlt, ⟨-, -, hrt⟩, -⟩ := hk'
  have e0 : entry (E ++ [((1, m, 0) : ℕ × ℕ × ℕ), ((d0, m, 0) : ℕ × ℕ × ℕ)]) 0 (E.length + 0) = 1 := by
    rw [entry_append_right]; rfl
  have e1 : entry (E ++ [((1, m, 0) : ℕ × ℕ × ℕ), ((d0, m, 0) : ℕ × ℕ × ℕ)]) 1 (E.length + 0) = m := by
    rw [entry_append_right]; rfl
  have e1' : entry (E ++ [((1, m, 0) : ℕ × ℕ × ℕ), ((d0, m, 0) : ℕ × ℕ × ℕ)]) 1 (E.length + 1) = m := by
    rw [entry_append_right]; rfl
  rcases Nat.lt_or_ge k E.length with hkE | hkE
  · have hrec := rtg0_rec hrt (E.length + 0) (by omega) (by omega)
    rw [e0, entry_append_left _ _ hkE] at hrec
    have := getD_row0_ge hE hkE
    omega
  · have hk0 : k = E.length + 0 := by omega
    rw [hk0, e1, e1'] at hlt
    omega

/-! ## 核の補題（hnp 版） -/

/-- ★ HeN.upleaf_deep_coreDT の仮定 hD1 を hnp（葉の行1の親が R 内に無い）に替えた版。 -/
theorem upleaf_deep_coreDT' {C : ℕ → List TrioSeq → Prop} {u d q d0 m : ℕ} {Y D : TrioSeq}
    (hD : Fr D) (hnp : ¬ hasParent (D ++ [((d0, m, 0) : ℕ × ℕ × ℕ)]) 1 D.length)
    (hd0 : 1 ≤ d0) (hqm : q < m) (hm : 1 ≤ m)
    (hrep : ∀ m', 1 ≤ m' → GTC C u
      (Y ++ shiftr01 d 0 (shiftr01 1 0 (tow q 0 (D ++ [((d0, m, 0) : ℕ × ℕ × ℕ)]) m')))) :
    GTC C u (Y ++ shiftr01 d 0 (shiftr01 1 0
      (((0, q, 0) : ℕ × ℕ × ℕ) :: (D ++ [((d0, m, 0) : ℕ × ℕ × ℕ)])))) := by
  obtain ⟨R, hR⟩ : ∃ R, R = D ++ [((d0, m, 0) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  have hRne : R ≠ [] := by simp [hR]
  have hRlen : R.length - 1 = D.length + 0 := by simp [hR]
  have eL : ∀ i, entry R i (R.length - 1) = entry [((d0, m, 0) : ℕ × ℕ × ℕ)] i 0 := by
    intro i; rw [hRlen, hR, entry_append_right]
  have e1 : entry R 1 (R.length - 1) = m := by rw [eL]; rfl
  have e2 : entry R 2 (R.length - 1) = 0 := by rw [eL]; rfl
  have hRl : 0 < R.length := List.length_pos_iff.mpr hRne
  have hRok : argOK R := by
    intro x hx; rw [hR] at hx
    rcases List.mem_append.mp hx with hx | hx
    · have := hD x hx; omega
    · simp at hx; subst hx; exact hd0
  have hsr : srow R (R.length - 1) = 1 := by unfold srow; rw [e2, e1]; simp; omega
  have hnpR : ¬ hasParent R 1 (R.length - 1) := by
    rw [hRlen, Nat.add_zero, hR]; exact hnp
  have hd_ : domT R (2 * entry R 1 (R.length - 1) - 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [e1, e2]; omega
    · rw [hsr]; exact hnpR
  have hpM : hasParent (((0, q, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length := by
    rw [hsr]
    refine hasParent_one_of (b := R.length) (k := 0) (by simp) hRl
      ⟨by simp, by simp, rtg0_zero (fun l hl0 hl => ?_) (by simp)⟩ ?_
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      rw [entry_cons]
      have hl' : l' < R.length := by simp at hl; omega
      have hmem : R.getD l' (0, 0, 0) ∈ R := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl']; exact List.getElem_mem hl'
      have := hRok _ hmem
      show 0 < (R.getD l' (0, 0, 0)).1; omega
    · rw [entry_cons_last hRne 1, e1]; show q < m; omega
  rw [← hR] at hrep ⊢
  exact HeN.upleaf_deep_coreT_gen hRok hRne hd_ hsr hpM hrep

/-- ★ GTC 版: 任意の Fr な接頭辞 E の後ろの深い葉 (1,m,0),(2,m,0)。 -/
theorem upleaf_deep_coreE {C : ℕ → List TrioSeq → Prop} {u d q m : ℕ} {Y E : TrioSeq}
    (hE : Fr E) (hqm : q < m) (hm : 1 ≤ m)
    (hrep : ∀ m', 1 ≤ m' → GTC C u
      (Y ++ shiftr01 d 0 (shiftr01 1 0 (tow q 0 (E ++ [((1, m, 0) : ℕ × ℕ × ℕ), ((2, m, 0) : ℕ × ℕ × ℕ)]) m')))) :
    GTC C u (Y ++ shiftr01 d 0 (shiftr01 1 0
      (((0, q, 0) : ℕ × ℕ × ℕ) :: (E ++ [((1, m, 0) : ℕ × ℕ × ℕ), ((2, m, 0) : ℕ × ℕ × ℕ)])))) := by
  have eE : E ++ [((1, m, 0) : ℕ × ℕ × ℕ), ((2, m, 0) : ℕ × ℕ × ℕ)]
      = (E ++ [((1, m, 0) : ℕ × ℕ × ℕ)]) ++ [((2, m, 0) : ℕ × ℕ × ℕ)] := by simp
  rw [eE] at hrep ⊢
  refine upleaf_deep_coreDT' (Fr_append hE (GzF.Fr_single le_rfl _ _)) ?_ (by omega) hqm hm hrep
  rw [← eE, show (E ++ [((1, m, 0) : ℕ × ℕ × ℕ)]).length = E.length + 1 by simp]
  exact hnp_E hE m 2

section
variable {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o) (f : ℕ → ℕ)
include hA hA1 ho

/-- ★ HeQ.upleaf_deep_coreD の hnp 版（遠い像側）。 -/
theorem upleaf_deep_coreD' {b d q d0 m : ℕ} {Pre Yp D : TrioSeq}
    (hPre : Fr Pre) (hYp : Fr Yp) (hYpH : Hd Yp) (hYpne : Yp ≠ [])
    (hD : Fr D) (hnp : ¬ hasParent (D ++ [((d0, m, 0) : ℕ × ℕ × ℕ)]) 1 D.length)
    (hd0 : 1 ≤ d0) (hqm : q < m) (hm : 1 ≤ m)
    (hrep : ∀ m', 1 ≤ m' → GpT A o f b
      (Pre ++ (Yp ++ shiftr01 d 0 (shiftr01 1 0 (tow q 0 (D ++ [((d0, m, 0) : ℕ × ℕ × ℕ)]) m'))))) :
    GpT A o f b (Pre ++ (Yp ++ shiftr01 d 0 (shiftr01 1 0
      (((0, q, 0) : ℕ × ℕ × ℕ) :: (D ++ [((d0, m, 0) : ℕ × ℕ × ℕ)]))))) := by
  obtain ⟨R, hR⟩ : ∃ R, R = D ++ [((d0, m, 0) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  have hRne : R ≠ [] := by simp [hR]
  have hRlen : R.length - 1 = D.length + 0 := by simp [hR]
  have eL : ∀ i, entry R i (R.length - 1) = entry [((d0, m, 0) : ℕ × ℕ × ℕ)] i 0 := by
    intro i; rw [hRlen, hR, entry_append_right]
  have e1 : entry R 1 (R.length - 1) = m := by rw [eL]; rfl
  have e2 : entry R 2 (R.length - 1) = 0 := by rw [eL]; rfl
  have hRl : 0 < R.length := List.length_pos_iff.mpr hRne
  have hRok : argOK R := by
    intro x hx; rw [hR] at hx
    rcases List.mem_append.mp hx with hx | hx
    · have := hD x hx; omega
    · simp at hx; subst hx; exact hd0
  have hsr : srow R (R.length - 1) = 1 := by unfold srow; rw [e2, e1]; simp; omega
  have hnpR : ¬ hasParent R 1 (R.length - 1) := by
    rw [hRlen, Nat.add_zero, hR]; exact hnp
  have hd_ : domT R (2 * entry R 1 (R.length - 1) - 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [e1, e2]; omega
    · rw [hsr]; exact hnpR
  have hpM : hasParent (((0, q, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length := by
    rw [hsr]
    refine hasParent_one_of (b := R.length) (k := 0) (by simp) hRl
      ⟨by simp, by simp, rtg0_zero (fun l hl0 hl => ?_) (by simp)⟩ ?_
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      rw [entry_cons]
      have hl' : l' < R.length := by simp at hl; omega
      have hmem : R.getD l' (0, 0, 0) ∈ R := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl']; exact List.getElem_mem hl'
      have := hRok _ hmem
      show 0 < (R.getD l' (0, 0, 0)).1; omega
    · rw [entry_cons_last hRne 1, e1]; show q < m; omega
  rw [← hR] at hrep ⊢
  exact HeQ.upleaf_deep_core hA hA1 ho f hPre hYp hYpH hYpne hRok hRne hd_ hsr hpM hrep

/-- ★ 遠い像側: 任意の Fr な接頭辞 E の後ろの深い葉。 -/
theorem upleaf_deep_coreE_far {b d q m : ℕ} {Pre Yp E : TrioSeq}
    (hPre : Fr Pre) (hYp : Fr Yp) (hYpH : Hd Yp) (hYpne : Yp ≠ [])
    (hE : Fr E) (hqm : q < m) (hm : 1 ≤ m)
    (hrep : ∀ m', 1 ≤ m' → GpT A o f b
      (Pre ++ (Yp ++ shiftr01 d 0 (shiftr01 1 0
        (tow q 0 (E ++ [((1, m, 0) : ℕ × ℕ × ℕ), ((2, m, 0) : ℕ × ℕ × ℕ)]) m'))))) :
    GpT A o f b (Pre ++ (Yp ++ shiftr01 d 0 (shiftr01 1 0
      (((0, q, 0) : ℕ × ℕ × ℕ) :: (E ++ [((1, m, 0) : ℕ × ℕ × ℕ), ((2, m, 0) : ℕ × ℕ × ℕ)]))))) := by
  have eE : E ++ [((1, m, 0) : ℕ × ℕ × ℕ), ((2, m, 0) : ℕ × ℕ × ℕ)]
      = (E ++ [((1, m, 0) : ℕ × ℕ × ℕ)]) ++ [((2, m, 0) : ℕ × ℕ × ℕ)] := by simp
  rw [eE] at hrep ⊢
  refine upleaf_deep_coreD' hA hA1 ho f hPre hYp hYpH hYpne (Fr_append hE (GzF.Fr_single le_rfl _ _)) ?_
    (by omega) hqm hm hrep
  rw [← eE, show (E ++ [((1, m, 0) : ℕ × ℕ × ℕ)]).length = E.length + 1 by simp]
  exact hnp_E hE m 2

end

/-! ## 2. 塔の等式 -/

/-- 接頭辞 pre の後ろの深い葉の塔: Lt pre 0 = pre ++ [tie 1 []]、
Lt pre (j+1) = pre ++ [tie 1 [tie 0 (Lt pre j)]]。 -/
def Lt (pre : List UT) : ℕ → List UT
  | 0 => pre ++ [UT.tie 1 []]
  | j + 1 => pre ++ [UT.tie 1 [UT.tie 0 (Lt pre j)]]

/-- ★ 描き方 F（連結を保ち、段 l のタイを (1, r+l, 0) の列で描く）で、深い葉の塔 = F (Lt pre j)。 -/
theorem tow_Lt {F : List UT → TrioSeq} {r : ℕ} (hA : ∀ xs ys, F (xs ++ ys) = F xs ++ F ys)
    (hT : ∀ l cs, F [UT.tie l cs] = ((1, r + l, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (F cs))
    (hN : F [] = []) (pre : List UT) : ∀ j,
    tow r 0 (F pre ++ [((1, r + 1, 0) : ℕ × ℕ × ℕ), ((2, r + 1, 0) : ℕ × ℕ × ℕ)]) (j + 1)
      = ((0, r, 0) : ℕ × ℕ × ℕ) :: F (Lt pre j) := by
  have hdl : (F pre ++ [((1, r + 1, 0) : ℕ × ℕ × ℕ), ((2, r + 1, 0) : ℕ × ℕ × ℕ)]).dropLast
      = F pre ++ [((1, r + 1, 0) : ℕ × ℕ × ℕ)] := by
    rw [show F pre ++ [((1, r + 1, 0) : ℕ × ℕ × ℕ), ((2, r + 1, 0) : ℕ × ℕ × ℕ)]
        = (F pre ++ [((1, r + 1, 0) : ℕ × ℕ × ℕ)]) ++ [((2, r + 1, 0) : ℕ × ℕ × ℕ)] by simp,
      List.dropLast_concat]
  have he : entry (F pre ++ [((1, r + 1, 0) : ℕ × ℕ × ℕ), ((2, r + 1, 0) : ℕ × ℕ × ℕ)]) 0
      ((F pre ++ [((1, r + 1, 0) : ℕ × ℕ × ℕ), ((2, r + 1, 0) : ℕ × ℕ × ℕ)]).length - 1) = 2 := by
    rw [show (F pre ++ [((1, r + 1, 0) : ℕ × ℕ × ℕ), ((2, r + 1, 0) : ℕ × ℕ × ℕ)]).length - 1
        = (F pre).length + 1 by simp, entry_append_right]; rfl
  intro j
  induction j with
  | zero =>
      rw [tow, graft_eq_shift, hdl, he]
      simp only [tow, Lt, hA, hT, hN, shiftr01, List.map_nil, List.append_nil, List.append_assoc]
  | succ j ih =>
      rw [tow, graft_eq_shift, hdl, he, ih]
      have e2 : ∀ X : TrioSeq, shiftr01 2 0 X = shiftr01 1 0 (shiftr01 1 0 X) := fun X => by
        rw [shiftr01_comp]
      simp only [Lt, hA, hT, List.append_assoc, e2, Nat.add_zero]
      simp [shiftr01]

theorem topTs_Lt (u : ℕ) (pre : List UT) (j : ℕ) :
    tow (u + 1) 0 (topTs u pre ++ [((1, u + 1 + 1, 0) : ℕ × ℕ × ℕ), ((2, u + 1 + 1, 0) : ℕ × ℕ × ℕ)]) (j + 1)
      = ((0, u + 1, 0) : ℕ × ℕ × ℕ) :: topTs u (Lt pre j) :=
  tow_Lt (topTs_append u) (fun l cs => by simp [topTs, topT]) rfl pre j

theorem chT_Lt (b r c : ℕ) (pre : List UT) (j : ℕ) :
    tow r 0 (chT b r c pre ++ [((1, r + 1, 0) : ℕ × ℕ × ℕ), ((2, r + 1, 0) : ℕ × ℕ × ℕ)]) (j + 1)
      = ((0, r, 0) : ℕ × ℕ × ℕ) :: chT b r c (Lt pre j) :=
  tow_Lt (chT_append b r c) (fun l cs => by simp [chT, unitT]) rfl pre j

/-! ## 3. 同じ段の鎖の末尾の葉 -/

/-- 最後の列の行0の祖先（自分以外）は全て行1 = m。 -/
def AncM (M : TrioSeq) (m : ℕ) : Prop :=
  ∀ k, k + 1 < M.length → (∀ i, k < i → i < M.length → entry M 0 k < entry M 0 i) → entry M 1 k = m

/-- ★ AncM なら最後の列（行1 = m）の行1の親は無い。 -/
theorem hnp_of_AncM {M : TrioSeq} {m : ℕ} (hA : AncM M m) (hne : M ≠ [])
    (hl : entry M 1 (M.length - 1) = m) : ¬ hasParent M 1 (M.length - 1) := by
  rintro ⟨k, hk, -⟩
  have hk' : nextrel1 M k (M.length - 1) := by
    unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
  obtain ⟨-, -, hklt, hlt, ⟨-, -, hrt⟩, -⟩ := hk'
  have hMl : 0 < M.length := List.length_pos_iff.mpr hne
  have := hA k (by omega) (fun i h1 h2 => rtg0_rec hrt i h1 (by omega))
  omega

theorem HeB.plugQ_append : ∀ (Q Q' : HeB.Path) (T : List UT),
    HeB.plugQ (Q ++ Q') T = HeB.plugQ Q (HeB.plugQ Q' T)
  | [], Q', T => by simp [HeB.plugQ]
  | (us, l) :: Q, Q', T => by simp only [List.cons_append, HeB.plugQ, HeB.plugQ_append Q Q' T]

section
variable {F : List UT → TrioSeq} {r : ℕ} (hA : ∀ xs ys, F (xs ++ ys) = F xs ++ F ys)
  (hT : ∀ l cs, F [UT.tie l cs] = ((1, r + l, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (F cs))
include hA hT

theorem F_plugQ_cons (us : List UT) (l : ℕ) (C : HeB.Path) (T : List UT) :
    F (HeB.plugQ ((us, l) :: C) T) = F us ++ ((1, r + l, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (F (HeB.plugQ C T)) := by
  simp only [HeB.plugQ, hA, hT]

/-- ★ 描き方 F で、鎖 C の末尾に X を足すと、F は末尾に |C| だけずらした F X を足す。 -/
theorem F_plugQ_app : ∀ (C : HeB.Path) (cs X : List UT),
    F (HeB.plugQ C (cs ++ X)) = F (HeB.plugQ C cs) ++ shiftr01 C.length 0 (F X)
  | [], cs, X => by simp [HeB.plugQ, hA, shiftr01]
  | (us, l) :: C, cs, X => by
      rw [F_plugQ_cons hA hT, F_plugQ_cons hA hT, F_plugQ_app C cs X, shiftr01_append0, shiftr01_add0]
      simp [Nat.add_comm]

/-- ★★ 鎖 C（全て段 L）の末尾の並び cs の後ろの葉 (|C|+1, r+L, 0): 最後の列の行0の祖先は鎖の節点だけ。 -/
theorem AncM_chain (L : ℕ) : ∀ (C : HeB.Path) (cs : List UT), (∀ e ∈ C, e.2 = L) →
    (∀ e ∈ C, Fr (F e.1)) → Fr (F cs) →
    AncM (F (HeB.plugQ C cs) ++ [((C.length + 1, r + L, 0) : ℕ × ℕ × ℕ)]) (r + L)
  | [], cs, _, _, hcs => by
      intro k hk hanc
      simp only [HeB.plugQ, List.length_nil, List.length_append, List.length_singleton] at hk hanc ⊢
      have hkc : k < (F cs).length := by omega
      have h1 := hanc (F cs).length (by omega) (by simp)
      rw [entry_append_left _ _ hkc, show (F cs).length = (F cs).length + 0 by rfl,
        entry_append_right] at h1
      have := getD_row0_ge hcs hkc
      change entry (F cs) 0 k < 0 + 1 at h1
      omega
  | (us, l) :: C, cs, hC, hF, hcs => by
      have hl : l = L := hC (us, l) (by simp)
      subst hl
      have ih := AncM_chain l C cs (fun e he => hC e (by simp [he])) (fun e he => hF e (by simp [he])) hcs
      have hus : Fr (F us) := hF (us, l) (by simp)
      obtain ⟨M', hM'⟩ : ∃ M', M' = F (HeB.plugQ C cs) ++ [((C.length + 1, r + l, 0) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
      rw [← hM'] at ih
      have eM : F (HeB.plugQ ((us, l) :: C) cs) ++ [(((us, l) :: C).length + 1, r + l, 0)]
          = (F us ++ [((1, r + l, 0) : ℕ × ℕ × ℕ)]) ++ shiftr01 1 0 M' := by
        rw [F_plugQ_cons hA hT, hM', shiftr01_append0]
        simp [shiftr01]
      rw [eM]
      intro k hk hanc
      have hlen : ((F us ++ [((1, r + l, 0) : ℕ × ℕ × ℕ)]) ++ shiftr01 1 0 M').length
          = (F us).length + 1 + M'.length := by simp [shiftr01_length]; omega
      rcases Nat.lt_trichotomy k (F us).length with hk1 | hk1 | hk1
      · exfalso
        have h1 := hanc (F us).length hk1 (by omega)
        rw [entry_append_left _ _ (by simp; omega), entry_append_left _ _ hk1,
          entry_append_left _ _ (by simp), show (F us).length = (F us).length + 0 by rfl,
          entry_append_right] at h1
        have := getD_row0_ge hus hk1
        change entry (F us) 0 k < 0 + 1 at h1
        omega
      · subst hk1
        rw [entry_append_left _ _ (by simp), show (F us).length = (F us).length + 0 by rfl,
          entry_append_right]; rfl
      · obtain ⟨k', rfl⟩ : ∃ k', k = (F us ++ [((1, r + l, 0) : ℕ × ℕ × ℕ)]).length + k' :=
          ⟨k - (F us).length - 1, by simp; omega⟩
        rw [entry_append_right, entry1_shiftr01]
        refine ih k' (by rw [hlen] at hk; simp at hk; omega) (fun i h1 h2 => ?_)
        have h3 := hanc ((F us ++ [((1, r + l, 0) : ℕ × ℕ × ℕ)]).length + i) (by omega)
          (by rw [hlen]; simp; omega)
        rw [entry_append_right, entry_append_right, entry0_shiftr01 (by omega),
          entry0_shiftr01 (by omega)] at h3
        omega

/-- 鎖 C の末尾の並び cs の後ろの葉の塔: Lc 0 = plugQ C cs、Lc (j+1) = plugQ C (cs ++ [tie 0 (Lc j)])。 -/
def Lc (C : HeB.Path) (cs : List UT) : ℕ → List UT
  | 0 => HeB.plugQ C cs
  | j + 1 => HeB.plugQ C (cs ++ [UT.tie 0 (Lc C cs j)])

/-- ★★ 鎖の末尾の葉の塔 = F (Lc C cs j)。 -/
theorem tow_chain (L : ℕ) (C : HeB.Path) (cs : List UT) : ∀ j,
    tow r 0 (F (HeB.plugQ C cs) ++ [((C.length + 1, r + L, 0) : ℕ × ℕ × ℕ)]) (j + 1)
      = ((0, r, 0) : ℕ × ℕ × ℕ) :: F (Lc C cs j) := by
  have he : entry (F (HeB.plugQ C cs) ++ [((C.length + 1, r + L, 0) : ℕ × ℕ × ℕ)]) 0
      ((F (HeB.plugQ C cs) ++ [((C.length + 1, r + L, 0) : ℕ × ℕ × ℕ)]).length - 1) = C.length + 1 := by
    rw [show (F (HeB.plugQ C cs) ++ [((C.length + 1, r + L, 0) : ℕ × ℕ × ℕ)]).length - 1
        = (F (HeB.plugQ C cs)).length + 0 by simp, entry_append_right]; rfl
  intro j
  induction j with
  | zero =>
      rw [tow, graft_eq_shift, List.dropLast_concat, he]
      simp [tow, Lc, shiftr01]
  | succ j ih =>
      rw [tow, graft_eq_shift, List.dropLast_concat, he, ih]
      simp only [Lc]
      rw [F_plugQ_app hA hT, hT]
      simp [shiftr01]
      exact ⟨by omega, fun a _ _ _ => by omega⟩

end

end PmC
end TRIO
