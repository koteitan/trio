/-
HeH.lean: 上の葉の規則（段 l の空の節点、親の段 p < l）と、段 l の節点の子の位置の空の並び（追記577）。

    towT p Y 0 = Y、towT p Y (j+1) = Y ++ [tie p (towT p Y j)]（親の塊の複製の入れ子）
- 最後の列 (x, r+l, 0) の最も下の 0 でない行は行 1 なので、写しは行 0 だけが上がり、親の段 p の節点の塊の入れ子になる。
- upleaf_core: 接頭辞 Yp のあとの深さ d の塊 (1, q, 0) :: (D ++ [(1, m, 0)])↑1（q < m）は、
  展開 (1, q, 0) :: (towR q D j)↑1 が全て GpT なら GpT（tstep_oper と oper_cons_tower1、HdU.GTC_N2 の遠い段の写し）。
- Gd_upleaf: 集合 P が段 p の延長で閉じ、道の最後の段が p、p < l なら、Gd P us → Gd P (us ++ [tie l []])。
- Gd_nil_chU: 段 l の節点の子の位置 chU P l の空の並び。
-/
import HeG

namespace TRIO
namespace HeH

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzA GzD GzF GzH GzI GzM GzN GzP GzU GzV GzW GzY
open HaA HaC HaE HaF HaG HbD HbM HbP HbS HcA HcE HcF HcI HcM HdA HdB HdC HdD HdE HdF HdG HdH HdI HdJ
open HeB HeC HeD HeE HeF HeG

/-! ## 塔 -/

def towT (p : ℕ) (Y : List UT) : ℕ → List UT
  | 0 => Y
  | j + 1 => Y ++ [UT.tie p (towT p Y j)]

def towR (q : ℕ) (D : TrioSeq) : ℕ → TrioSeq
  | 0 => D
  | j + 1 => D ++ ((1, q, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towR q D j)

theorem imgT_towT (A : List ℕ) (H G : ℕ → ℕ) (c u p : ℕ) (Y : List UT) :
    ∀ j, imgT A H G c u (towT p Y j) = towT p (imgT A H G c u Y) j
  | 0 => rfl
  | j + 1 => by simp only [towT, imgT_append, imgT_tie, imgT_towT A H G c u p Y j]

theorem chT_towT (b r u p : ℕ) (Y : List UT) :
    ∀ j, chT b r u (towT p Y j) = towR (r + p) (chT b r u Y) j
  | 0 => rfl
  | j + 1 => by
      simp only [towT, towR, chT_append]
      simp [chT, unitT, chT_towT b r u p Y j]

theorem Gd_towT {P : PS} {p : ℕ} (hcl : Ext P p P) {A : List ℕ} {k : ℕ} {H : ℕ → ℕ}
    (hA01 : ∀ a ∈ A, 1 ≤ a) (hk : 1 ≤ k) (hAk : ∀ a ∈ A, a < k) {c : ℕ} {us : List UT}
    (h : Gd P A k H c us) : ∀ j, Gd P A k H c (towT p us j)
  | 0 => h
  | j + 1 => Gd_tie hcl hA01 hk hAk h (Gd_towT hcl hA01 hk hAk h j)

/-! ## 展開 -/

/-- ★ 深さ d の塊の最後の上の葉の展開は、親の塊の入れ子。 -/
theorem upleaf_core {A : List ℕ} {o : ℕ} (hA : ∀ a ∈ A, a < o) (hA1 : ∀ a ∈ A, 1 ≤ a) (ho : 1 ≤ o)
    (f : ℕ → ℕ) {b : ℕ} {Pre Yp D : TrioSeq} {d q m : ℕ} (hPre : Fr Pre) (hYp : Fr Yp) (hYpH : Hd Yp)
    (hYpne : Yp ≠ []) (hD : Fr D) (hqm : q < m)
    (hrep : ∀ j, GpT A o f b (Pre ++ (Yp ++ shiftr01 d 0
      (((1, q, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towR q D j))))) :
    GpT A o f b (Pre ++ (Yp ++ shiftr01 d 0
      (((1, q, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (D ++ [((1, m, 0) : ℕ × ℕ × ℕ)])))) := by
  obtain ⟨R, hR⟩ : ∃ R : TrioSeq, R = D ++ [((1, m, 0) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  rw [← hR]
  have hRok : argOK R := by
    intro x hx
    rw [hR] at hx
    rcases List.mem_append.mp hx with hx | hx
    · have := hD x hx; omega
    · simp at hx; subst hx; show 0 < 1; omega
  have hRne : R ≠ [] := by simp [hR]
  have hRlen : R.length - 1 = D.length + 0 := by simp [hR]
  have eL : ∀ i, entry R i (R.length - 1) = entry [((1, m, 0) : ℕ × ℕ × ℕ)] i 0 := by
    intro i; rw [hRlen, hR, entry_append_right]
  have e0 : entry R 0 (R.length - 1) = 1 := by rw [eL]; rfl
  have e1 : entry R 1 (R.length - 1) = m := by rw [eL]; rfl
  have e2' : entry R 2 (R.length - 1) = 0 := by rw [eL]; rfl
  have hsr : srow R (R.length - 1) = 1 := by unfold srow; rw [e2', e1]; simp; omega
  have hnpR : ¬ hasParent R 1 (R.length - 1) := by
    rintro ⟨k, hk, -⟩
    have hk' : nextrel1 R k (R.length - 1) := by
      unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
    obtain ⟨-, -, hkl, -, hle0, -⟩ := hk'
    have hrec := rtg0_rec hle0.2.2 (R.length - 1) hkl le_rfl
    rw [e0] at hrec
    have hkD : k < D.length := by omega
    rw [hR, Small.entry_append_left hkD] at hrec
    have := getD_row0_ge hD hkD
    omega
  have hd : domT R (2 * m - 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [e1, e2']; omega
    · rw [hsr]; exact hnpR
  have hRl : 0 < R.length := List.length_pos_iff.mpr hRne
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
      show 0 < (R.getD l' (0, 0, 0)).1
      omega
    · rw [entry_cons_last hRne 1, e1]; show q < m; omega
  have hdl : R.dropLast = D := by rw [hR, List.dropLast_concat]
  have htow : ∀ j, shiftr01 1 0 (tow q 0 R (j + 1))
      = ((1, q, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (D ++ shiftr01 1 0 (tow q 0 R j)) := by
    intro j
    rw [tow, graft_eq_shift, e0, hdl]
    simp [shiftr01]
  have htR : ∀ j, D ++ shiftr01 1 0 (tow q 0 R j) = towR q D j := by
    intro j
    induction j with
    | zero => simp [tow, towR, shiftr01]
    | succ j ih => rw [htow, ih]; rfl
  have eV : ((1, q, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 R
      = shiftr01 1 0 (((0, q, 0) : ℕ × ℕ × ℕ) :: R) := by simp [shiftr01]
  have hlen2 : 2 ≤ (((0, q, 0) : ℕ × ℕ × ℕ) :: R).length := by simp; omega
  have hpM' : hasParent (((0, q, 0) : ℕ × ℕ × ℕ) :: R)
      (srow (((0, q, 0) : ℕ × ℕ × ℕ) :: R) ((((0, q, 0) : ℕ × ℕ × ℕ) :: R).length - 1))
      ((((0, q, 0) : ℕ × ℕ × ℕ) :: R).length - 1) := by
    have hl : ((((0, q, 0) : ℕ × ℕ × ℕ) :: R).length - 1) = R.length := by simp
    rw [hl, srow_cons_last hRne]; exact hpM
  rw [eV]
  refine tstep_oper hA hA1 ho f hPre hYp hYpH hYpne (Fr_shift1 _)
    (by rw [shiftr01_length]; exact hlen2)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpM') (fun m' hm' => ?_)
  have eO := oper_shift [] (((0, q, 0) : ℕ × ℕ × ℕ) :: R) 1 m' hlen2 hpM'
  simp only [List.nil_append] at eO
  rw [eO, oper_cons_tower1 hRok hRne hd hsr hpM]
  obtain ⟨j, rfl⟩ : ∃ j, m' = j + 1 := ⟨m' - 1, by omega⟩
  rw [htow, htR]
  exact hrep j

/-! ## 遠い語 -/

theorem upleaf_snoc {C : List ℕ} {o : ℕ} (hC : ∀ a ∈ C, a < o) (hC1 : ∀ a ∈ C, 1 ≤ a) (ho : 1 ≤ o)
    {f : ℕ → ℕ} {u b : ℕ} {ws : List (List (List UT) × ℕ × TrioSeq)} {Lds : List (List UT)} {Q' : Path}
    {v Y : List UT} {p l K : ℕ} (hpl : p < l) (hv : RawTs K v) (hY : RawTs K Y)
    (hrep : ∀ j, GpT C o f b (farWt b (b + liftOff f C o + 1)
      (ws ++ [(Lds ++ [plugQ (Q' ++ [(v, p)]) (towT p Y j)], u, [])]))) :
    GpT C o f b (farWt b (b + liftOff f C o + 1)
      (ws ++ [(Lds ++ [plugQ (Q' ++ [(v, p)]) (Y ++ [UT.tie l []])], u, [])])) := by
  obtain ⟨r, hr⟩ : ∃ r, r = b + liftOff f C o + 1 := ⟨_, rfl⟩
  rw [← hr] at hrep ⊢
  obtain ⟨Yp, hYpd⟩ : ∃ Yp, Yp = fwH b r (FTLt b r u (Lds ++ [plugQ Q' []])) u [] ++
      shiftr01 (Q'.length + 2) 0 (chT b r u v) := ⟨_, rfl⟩
  have eW : ∀ T : List UT, farWt b r (ws ++ [(Lds ++ [plugQ (Q' ++ [(v, p)]) T], u, [])])
      = farWt b r ws ++ (Yp ++ shiftr01 (Q'.length + 2) 0
          (((1, r + p, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b r u T))) := by
    intro T
    rw [plugQ_snoc, HeD.farWt_botT, hYpd, chT_append, shiftr01_append0]
    simp [chT, unitT, List.append_assoc]
  have hYpF : Fr Yp := by rw [hYpd]; exact Fr_append (Fr_fwH _ _ _ _ _) (Fr_shiftr (Fr_chT _ hv) _)
  have hYpne : Yp ≠ [] := by rw [hYpd]; simp [fwH]
  have hYpH : Hd Yp := by rw [hYpd]; exact Hd_app_ne (Hd_fwH _ _ _ _ _) (by simp [fwH])
  have eT : chT b r u (Y ++ [UT.tie l []]) = chT b r u Y ++ [((1, r + l, 0) : ℕ × ℕ × ℕ)] := by
    simp [chT_append, chT, unitT, shiftr01]
  rw [eW, eT]
  refine upleaf_core hC hC1 ho f (Fr_farWt _ _ _) hYpF hYpH hYpne (Fr_chT _ hY) (by omega) (fun j => ?_)
  have := hrep j
  rwa [eW, chT_towT] at this

theorem upleaf_nil {C : List ℕ} {o : ℕ} (hC : ∀ a ∈ C, a < o) (hC1 : ∀ a ∈ C, 1 ≤ a) (ho : 1 ≤ o)
    {f : ℕ → ℕ} {u b : ℕ} {ws : List (List (List UT) × ℕ × TrioSeq)} {Lds : List (List UT)}
    {Y : List UT} {l K : ℕ} (hl : 0 < l) (hY : RawTs K Y)
    (hrep : ∀ j, GpT C o f b (farWt b (b + liftOff f C o + 1) (ws ++ [(Lds ++ [towT 0 Y j], u, [])]))) :
    GpT C o f b (farWt b (b + liftOff f C o + 1) (ws ++ [(Lds ++ [Y ++ [UT.tie l []]], u, [])])) := by
  obtain ⟨r, hr⟩ : ∃ r, r = b + liftOff f C o + 1 := ⟨_, rfl⟩
  rw [← hr] at hrep ⊢
  obtain ⟨Yp, hYpd⟩ : ∃ Yp, Yp = ((1, r, 1) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (FTLt b r u Lds) := ⟨_, rfl⟩
  have eW : ∀ T : List UT, farWt b r (ws ++ [(Lds ++ [T], u, [])])
      = farWt b r ws ++ (Yp ++ shiftr01 1 0
          (((1, r + 0, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (chT b r u T))) := by
    intro T
    rw [farWt_snoc, hYpd]
    simp [fwH, FTLt_snoc, mlift_nil, shiftr01_append0]
  have hYpF : Fr Yp := by rw [hYpd]; exact Fr_letter _ _
  have hYpne : Yp ≠ [] := by rw [hYpd]; simp
  have hYpH : Hd Yp := by rw [hYpd]; exact fun _ => rfl
  have eT : chT b r u (Y ++ [UT.tie l []]) = chT b r u Y ++ [((1, r + l, 0) : ℕ × ℕ × ℕ)] := by
    simp [chT_append, chT, unitT, shiftr01]
  rw [eW, eT]
  refine upleaf_core hC hC1 ho f (Fr_farWt _ _ _) hYpF hYpH hYpne (Fr_chT _ hY) (by omega) (fun j => ?_)
  have := hrep j
  rwa [eW, chT_towT] at this

/-! ## 規則 -/

/-- ★ 上の葉: 集合 P が段 p の延長で閉じ、道の最後の段が p < l なら、段 l の空の節点を足せる。 -/
theorem Gd_upleaf {P : PS} (hP : PSOK P) {p l : ℕ} (hcl : Ext P p P) (hlast : LastL P p) (hpl : p < l)
    {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} (hA01 : ∀ a ∈ A, 1 ≤ a) (hk : 1 ≤ k) (hAk : ∀ a ∈ A, a < k)
    {c : ℕ} {us : List UT} (h : Gd P A k H c us) : Gd P A k H c (us ++ [UT.tie l []]) := by
  refine ⟨RawTs_snoc.mpr ⟨h.1, by simp [RawT, RawTs]⟩, fun G S o f hE u hcu Lds hL Q hQ => ?_⟩
  intro b hub ws hC hR
  have hA := hE.2.2.1
  have hA1 := hE.2.2.2.1
  have ho := hE.2.2.2.2.1
  rw [imgT_append, imgT_tie, imgT_nil]
  have hT := Gd_towT hcl hA01 hk hAk h
  have hrep : ∀ j, GpT (S ++ A) o f b (farWt b (b + liftOff f (S ++ A) o + 1)
      (ws ++ [(Lds ++ [plugQ Q (towT p (imgT A H G c u us) j)], u, [])])) := by
    intro j
    have := (hT j).2 G S o f hE u hcu Lds hL Q hQ b hub ws hC hR
    rwa [imgT_towT] at this
  have hRaw := RawTs_imgT hE hcu h.1
  rcases List.eq_nil_or_concat Q with rfl | ⟨Q', ⟨v, p'⟩, rfl⟩
  · have hp0 : p = 0 := by have := hlast _ _ _ _ _ hQ; simpa [lastL] using this.symm
    subst hp0
    simp only [plugQ] at hrep ⊢
    exact upleaf_nil hA hA1 ho (by omega) hRaw hrep
  · simp only [List.concat_eq_append] at hQ hrep ⊢
    have hp' : p' = p := by have := hlast _ _ _ _ _ hQ; rwa [lastL_snoc] at this
    subst hp'
    have hQraw := hP.raw _ _ _ _ _ hQ
    exact upleaf_snoc hA hA1 ho hpl (hQraw (v, p') (by simp)) hRaw hrep

/-- ★ 段 l の節点の子の位置の空の並び（親の集合で上の葉）。 -/
theorem Gd_nil_chU {P : PS} (hP : PSOK P) {p l : ℕ} (hcl : Ext P p P) (hlast : LastL P p) (hpl : p < l)
    {A : List ℕ} {k : ℕ} {H : ℕ → ℕ} {c : ℕ} : Gd (chU P l) A k H c [] := by
  refine ⟨by simp [RawTs], fun G S o f hE u _ Lds hL Q hQ => ?_⟩
  obtain ⟨Q', us, rfl, hQ', hus⟩ := hQ
  rw [imgT_nil, BotT_snoc_eq]
  have := (Gd_upleaf hP hcl hlast hpl hE.2.2.2.1 hE.2.2.2.2.1 hE.2.2.1 hus).2 (fun _ => 0) [] o f
    (EmbU_triv hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2.1 f) u le_rfl Lds hL Q' hQ'
  rwa [imgT_zero] at this

end HeH
end TRIO
