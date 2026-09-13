/-
GxR.lean: 2 段上の錐の下の、同じ行 1 の錐（祖父のタイからの塔）。

    GHs_far : GHs u C → GHs u (C ++ [(1, u+2, 0)])

GHs を GTs まで開くとタイ t の子の並び X ++ h :: C が明示される。塔の写しはタイの単位で、
その子の並びは同じ X を使う X ++ h :: (C ++ 前の写し) なので、GHs_child で組み直せる。
h' の子の差し込み口は GHHs = nslot GHs 2。
-/
import GxP

namespace TRIO
namespace GxR

open Wset
open Small
open GwS
open Gw
open GwU
open GwZ
open GxD
open GxG
open GxJ
open GxK
open GxL
open GxN
open GxP

theorem GHs_far {u : ℕ} {C : TrioSeq} (hC : Fr C) (h : GHs u C) :
    GHs u (C ++ [((1, u + 2, 0) : ℕ × ℕ × ℕ)]) := by
  intro u' hu X hX hGX ok hA u'' hu'' Y hY hPY
  have hc := coneV_top' hC (show u < u + 2 by omega)
  have eC : mlift (C ++ [((1, u + 2, 0) : ℕ × ℕ × ℕ)]) u (u' - u)
      = mlift C u (u' - u) ++ [((1, u' + 2, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_cone C _ hc (u' - u)]
    show _ ++ [((1, u + 2 + (u' - u), 0) : ℕ × ℕ × ℕ)] = _
    rw [show u + 2 + (u' - u) = u' + 2 by omega]
  rw [eC]
  have hCl : Fr (mlift C u (u' - u)) := Fr_mlift hC u (u' - u)
  have hc' := coneV_top' hCl (show u' < u' + 2 by omega)
  have eX : mlift (X ++ ((1, u' + 2, 0) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (mlift C u (u' - u) ++ [((1, u' + 2, 0) : ℕ × ℕ × ℕ)])) u' (u'' - u')
      = mlift X u' (u'' - u') ++ ((1, u'' + 2, 0) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (mlift C u (u'' - u) ++ [((1, u'' + 2, 0) : ℕ × ℕ × ℕ)]) := by
    rw [mlift_app hX (Hd_node _ _), mlift_node (by omega) (Fr_append hCl (by
      intro y hy; simp at hy; subst hy; show 1 ≤ 1; omega)),
      mlift_snoc_cone _ _ hc' (u'' - u')]
    have e := mlift_mlift C u (u' - u) (u'' - u')
    rw [show u + (u' - u) = u' by omega, show u' - u + (u'' - u') = u'' - u by omega] at e
    rw [e]
    show _ ++ ((1, u' + 2 + (u'' - u'), 0) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (_ ++ [((1, u' + 2 + (u'' - u'), 0) : ℕ × ℕ × ℕ)]) = _
    rw [show u' + 2 + (u'' - u') = u'' + 2 by omega]
  rw [eX]
  have hXl : Fr (mlift X u' (u'' - u')) := Fr_mlift hX u' (u'' - u')
  have hGXl : GTs u'' (mlift X u' (u'' - u')) := GTs_ax.lift u' X hX hGX u'' hu''
  have hCll : Fr (mlift C u (u'' - u)) := Fr_mlift hC u (u'' - u)
  have hGCll : GHs u'' (mlift C u (u'' - u)) := GHs_ax.lift u C hC h u'' (le_trans hu hu'')
  obtain ⟨Xl, hXleq⟩ : ∃ Xl, Xl = mlift X u' (u'' - u') := ⟨_, rfl⟩
  obtain ⟨Cll, hCleq⟩ : ∃ Cll, Cll = mlift C u (u'' - u) := ⟨_, rfl⟩
  rw [← hXleq] at hXl hGXl ⊢
  rw [← hCleq] at hCll hGCll ⊢
  -- 入れ子の関数 N V := Xl ++ h :: V↑1
  have hN_app : ∀ V Z : TrioSeq, Xl ++ ((1, u'' + 2, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (V ++ Z)
      = (Xl ++ ((1, u'' + 2, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 V) ++ shiftr01 1 0 Z := by
    intro V Z; rw [shiftr01_append0]; simp
  obtain ⟨R, hR⟩ : ∃ R : TrioSeq, R = Xl ++ ((1, u'' + 2, 0) : ℕ × ℕ × ℕ) ::
      shiftr01 1 0 (Cll ++ [((1, u'' + 2, 0) : ℕ × ℕ × ℕ)]) := ⟨_, rfl⟩
  rw [← hR]
  have eRX : R = (Xl ++ ((1, u'' + 2, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Cll) ++
      [((2, u'' + 2, 0) : ℕ × ℕ × ℕ)] := by
    rw [hR, hN_app, shift_col]
  have hRok : argOK R := by
    intro p hp
    rw [hR] at hp
    rcases List.mem_append.mp hp with hp | hp
    · have := hXl p hp; omega
    · have := Fr_node (u'' + 2) (Cll ++ [((1, u'' + 2, 0) : ℕ × ℕ × ℕ)]) p hp; omega
  have hRne : R ≠ [] := by rw [hR]; simp
  have hRlen : R.length - 1 = (Xl ++ ((1, u'' + 2, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Cll).length + 0 := by
    rw [eRX]; simp
  have eL : ∀ r, entry R r (R.length - 1) = entry [((2, u'' + 2, 0) : ℕ × ℕ × ℕ)] r 0 := by
    intro r; rw [hRlen]; conv_lhs => rw [eRX]
    rw [entry_append_right]
  have e0 : entry R 0 (R.length - 1) = 2 := by rw [eL]; rfl
  have e1 : entry R 1 (R.length - 1) = u'' + 2 := by rw [eL]; rfl
  have e2 : entry R 2 (R.length - 1) = 0 := by rw [eL]; rfl
  have hsr : srow R (R.length - 1) = 1 := by unfold srow; rw [e2, e1]; simp
  have hlast : R.length - 1 = Xl.length + 1 + Cll.length := by rw [hRlen]; simp [shiftr01]; omega
  have hnpR : ¬ hasParent R 1 (R.length - 1) := by
    rintro ⟨k, hk, -⟩
    have hk' : nextrel1 R k (R.length - 1) := by
      unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
    obtain ⟨-, -, hkl, hk1, hle0, -⟩ := hk'
    rw [e1] at hk1
    rcases Nat.lt_trichotomy k Xl.length with hlt | heq | hgt
    · have hrec := rtg0_rec hle0.2.2 Xl.length hlt (by omega)
      rw [hR, Small.entry_append_left hlt, show Xl.length = Xl.length + 0 from rfl,
        entry_append_right] at hrec
      have := getD_row0_ge hXl hlt
      have e : entry (((1, u'' + 2, 0) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (Cll ++ [((1, u'' + 2, 0) : ℕ × ℕ × ℕ)])) 0 0 = 1 := rfl
      rw [e] at hrec
      omega
    · subst heq
      rw [hR, show Xl.length = Xl.length + 0 from rfl, entry_append_right] at hk1
      have e : entry (((1, u'' + 2, 0) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (Cll ++ [((1, u'' + 2, 0) : ℕ × ℕ × ℕ)])) 1 0 = u'' + 2 := rfl
      rw [e] at hk1
      omega
    · have hrec := rtg0_rec hle0.2.2 (R.length - 1) hkl le_rfl
      rw [e0] at hrec
      obtain ⟨q, rfl⟩ : ∃ q, k = Xl.length + 1 + q := ⟨k - (Xl.length + 1), by omega⟩
      have hq : q < Cll.length := by omega
      rw [hR, show Xl.length + 1 + q = Xl.length + (q + 1) by omega, entry_append_right,
        entry_cons, entry0_shiftr01 (by simp; omega), Small.entry_append_left hq] at hrec
      have := getD_row0_ge hCll hq
      omega
  have hd : domT R (2 * (u'' + 1) + 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [e1, e2]; omega
    · rw [hsr]; exact hnpR
  have hRl : 0 < R.length := List.length_pos_iff.mpr hRne
  have hpM : hasParent (((0, u'' + 1, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length := by
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
    · rw [entry_cons_last hRne 1, e1]; show u'' + 1 < u'' + 2; omega
  have hdl : R.dropLast = Xl ++ ((1, u'' + 2, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 Cll := by
    rw [eRX, List.dropLast_concat]
  have htow : ∀ j, shiftr01 1 0 (tow (u'' + 1) 0 R (j + 1))
      = ((1, u'' + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0
        (Xl ++ ((1, u'' + 2, 0) : ℕ × ℕ × ℕ) ::
          shiftr01 1 0 (Cll ++ shiftr01 1 0 (tow (u'' + 1) 0 R j))) := by
    intro j
    rw [tow, graft_eq_shift, e0, hdl, hN_app, shiftr01_add0]
    simp [shiftr01]
  have hG : ∀ j, GHs u'' (Cll ++ shiftr01 1 0 (tow (u'' + 1) 0 R j)) ∧
      Fr (Cll ++ shiftr01 1 0 (tow (u'' + 1) 0 R j)) := by
    intro j
    induction j with
    | zero => simpa [tow, shiftr01] using ⟨hGCll, hCll⟩
    | succ j ih =>
        rw [htow]
        refine ⟨GHs_child hCll hGCll ?_, Fr_append hCll (Fr_node _ _)⟩
        have := ih.1 u'' le_rfl Xl hXl hGXl
        rwa [Nat.sub_self, mlift_zero] at this
  have eV : ((1, u'' + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 R
      = shiftr01 1 0 (((0, u'' + 1, 0) : ℕ × ℕ × ℕ) :: R) := by simp [shiftr01]
  rw [eV]
  have hlen2 : 2 ≤ (((0, u'' + 1, 0) : ℕ × ℕ × ℕ) :: R).length := by simp; omega
  have hpM' : hasParent (((0, u'' + 1, 0) : ℕ × ℕ × ℕ) :: R)
      (srow (((0, u'' + 1, 0) : ℕ × ℕ × ℕ) :: R) ((((0, u'' + 1, 0) : ℕ × ℕ × ℕ) :: R).length - 1))
      ((((0, u'' + 1, 0) : ℕ × ℕ × ℕ) :: R).length - 1) := by
    have hl : ((((0, u'' + 1, 0) : ℕ × ℕ × ℕ) :: R).length - 1) = R.length := by simp
    rw [hl, srow_cons_last hRne]; exact hpM
  refine hA.oper u'' Y _ hY (Fr_shift1 _) (fun _ => ?_) (by rw [shiftr01_length]; exact hlen2)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpM') (fun m hm => ?_)
  · rw [entry0_shiftr01 (by simp)]; rfl
  · have eO := oper_shift [] (((0, u'' + 1, 0) : ℕ × ℕ × ℕ) :: R) 1 m hlen2 hpM'
    simp only [List.nil_append] at eO
    rw [eO, oper_cons_tower1 hRok hRne hd hsr hpM]
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [htow]
    have h1 := (hG j).1 u'' le_rfl Xl hXl hGXl
    rw [Nat.sub_self, mlift_zero] at h1
    have := h1 ok hA u'' le_rfl Y hY hPY
    rwa [Nat.sub_self, mlift_zero] at this

#print axioms GHs_far

/-! ## h の下の h' の子の差し込み口 -/

def GHHs : ℕ → TrioSeq → Prop := nslot GHs 2

theorem GHHs_ax : SlotAx GHHs := nslot_ax GHs_ax (by omega)

theorem GHHs_nil (u : ℕ) : GHHs u [] := by
  intro u' _ X hX hGX
  have := GHs_far hX hGX
  simpa [mlift_nil, shiftr01] using this

def GHHF (u : ℕ) (C : TrioSeq) : Prop := GHHs u C ∧ Fr C

theorem GHHF_nil (u : ℕ) : GHHF u [] := ⟨GHHs_nil u, Fr_nil⟩

theorem GHHF_load {u : ℕ} {C Z : TrioSeq} (h : GHHF u C) (hZ : Z ∈ Wg (2 * u)) (hb : based Z) :
    GHHF u (C ++ shiftr01 1 0 Z) :=
  ⟨slot_load GHHs_ax h.2 h.1 Z hZ hb, Fr_append h.2 (Fr_shift1 Z)⟩

theorem GHHF_tie {u : ℕ} {C E : TrioSeq} (h : GHHF u C) (hE : GTF u E) :
    GHHF u (C ++ ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 E) := by
  refine ⟨?_, Fr_append h.2 (Fr_node _ _)⟩
  have := hE.1 GHHs GHHs_ax u le_rfl C h.2 h.1
  rwa [Nat.sub_self, mlift_zero] at this

/-- h の子に、子を持つ h'。 -/
theorem GHF_hh {u : ℕ} {C E : TrioSeq} (h : GHF u C) (hE : GHHF u E) :
    GHF u (C ++ ((1, u + 2, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 E) := by
  refine ⟨?_, Fr_append h.2 (Fr_node _ _)⟩
  have := hE.1 u le_rfl C h.2 h.1
  rwa [Nat.sub_self, mlift_zero] at this

/-- 行 882 の試し。 -/
theorem R882_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 2, 0), (4, 2, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0)
    (WordsG_consT (TF_tie (TF_nil 0) (GTF_h (GTF_nil 0) (GHF_hh (GHF_nil 0) (GHHF_nil 0))))
      (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

#print axioms R882_mem

end GxR
end TRIO
