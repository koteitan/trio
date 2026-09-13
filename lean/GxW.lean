/-
GxW.lean: 節点の下の語。

    BwN u Ls := ∀ σ ≥ 1, Gof σ u (rword 0 (u+σ) (Ls.map (mlift · (u+1) (σ-1))))

タイの下の字の潰れは、子の並びを段 u+1 で持ち上げた写しを行 1 が 1 ずつ上がる節点の入れ子に置く。
-/
import GxV

namespace TRIO
namespace GxW

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
open GxR
open GxT
open GxV

/-! ## 低い段での持ち上げ -/

open Classical in
theorem mlift_cons_root' {X : TrioSeq} (hX : ∀ x ∈ X, 1 ≤ x.1) {b r : ℕ} (hr : b < r) (t z : ℕ) :
    mlift (((0, r, z) : ℕ × ℕ × ℕ) :: X) b t = ((0, r + t, z) : ℕ × ℕ × ℕ) :: mlift X b t := by
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [mlift_length] at hi
  rw [mlift_getD hi]
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · have hc : coneV (((0, r, z) : ℕ × ℕ × ℕ) :: X) b 0 := by
      rw [coneV_iff_amin, amin_zero]; simpa [entry] using hr
    rw [if_pos hc]
    simp [entry]
  · obtain ⟨j, rfl⟩ : ∃ j, i = 1 + j := ⟨i - 1, by omega⟩
    have hj : j < X.length := by simp at hi; omega
    have e : ∀ q, entry (((0, r, z) : ℕ × ℕ × ℕ) :: X) q (1 + j) = entry X q j := by
      intro q; rw [show 1 + j = j + 1 by omega, entry_cons]
    rw [e 0, e 1, e 2]
    have eg : (((0, r + t, z) : ℕ × ℕ × ℕ) :: mlift X b t).getD (1 + j) (0, 0, 0)
        = (mlift X b t).getD j (0, 0, 0) := by
      rw [show 1 + j = j + 1 by omega]; rfl
    rw [eg, mlift_getD hj]
    have hiff := coneV_cons_iff (B := r) (z := z) (v := b) (fun p hp => hX p hp) hj
    by_cases hc : coneV X b j
    · rw [if_pos (hiff.mpr ⟨hr, hc⟩), if_pos hc]
    · rw [if_neg (fun h => hc (hiff.mp h).2), if_neg hc]

theorem mlift_rcol' {X : TrioSeq} (hX : ∀ x ∈ X, 1 ≤ x.1) {b v : ℕ} (hb : b ≤ v) (t : ℕ) :
    mlift (rcol 0 v X) b t = rcol 0 (v + t) (mlift X b t) := by
  have e1 : rcol 0 v X = shiftr01 1 0 (((0, v + 1, 1) : ℕ × ℕ × ℕ) :: X) := by
    simp [rcol, shiftr01]
  have e2 : rcol 0 (v + t) (mlift X b t)
      = shiftr01 1 0 (((0, v + t + 1, 1) : ℕ × ℕ × ℕ) :: mlift X b t) := by
    simp [rcol, shiftr01]
  rw [e1, e2, mlift_shift0, mlift_cons_root' hX (show b < v + 1 by omega),
    show v + 1 + t = v + t + 1 by omega]

theorem mlift_rword' {b v : ℕ} (hb : b ≤ v) (t : ℕ) : ∀ (L : List TrioSeq),
    (∀ X ∈ L, ∀ x ∈ X, 1 ≤ x.1) →
    mlift (rword 0 v L) b t = rword 0 (v + t) (L.map (fun X => mlift X b t))
  | [], _ => by simp [rword, mlift]
  | (X :: L'), hL => by
      rw [rword_cons, List.map_cons, rword_cons]
      have hrs : ∀ x ∈ rcol 0 v X, entry (rword 0 v L') 0 0 ≤ x.1 := by
        intro x hx
        have h1 := rcol_ge 0 v X x hx
        cases L' with
        | nil => simp [rword, entry]
        | cons Y L'' => rw [rword_cons]; simp [rcol, entry]; omega
      rw [mlift_append hrs, mlift_rcol' (hL X (by simp)) hb,
        mlift_rword' hb t L' (fun Y hY => hL Y (List.mem_cons_of_mem _ hY))]

/-- 段 u と段 u+1 の持ち上げの入れ替え。 -/
theorem mlift_comm (X : TrioSeq) (u s d : ℕ) :
    mlift (mlift X (u + 1) s) u d = mlift (mlift X u d) (u + 1 + d) s := by
  rw [mlift_eq_slift, mlift_eq_slift, mlift_eq_slift, mlift_eq_slift,
    slift_slift (stair_step (u + 1) s) (stair_step u d),
    slift_slift (stair_step u d) (stair_step (u + 1 + d) s)]
  congr 1
  funext m
  split_ifs <;> omega

#print axioms mlift_comm


theorem coneV_top1 {K : TrioSeq} (hK : Fr K) {u r : ℕ} (hr : u < r) :
    coneV (K ++ [((1, r, 1) : ℕ × ℕ × ℕ)]) u K.length := by
  intro y hy
  have hyle := rtg0_le hy
  rcases Nat.lt_or_ge y K.length with hlt | hge
  · exfalso
    have hrec := rtg0_rec hy K.length hlt le_rfl
    rw [Small.entry_append_left hlt, show K.length = K.length + 0 from rfl,
      entry_append_right] at hrec
    have h1 := getD_row0_ge hK hlt
    have e : entry [((1, r, 1) : ℕ × ℕ × ℕ)] 0 0 = 1 := rfl
    rw [e] at hrec
    omega
  · have hy' : y = K.length := by simp at hyle; omega
    subst hy'
    rw [show K.length = K.length + 0 from rfl, entry_append_right]
    show u < r; exact hr

/-! ## 節点の下の語 -/

def WF (Ls : List TrioSeq) : Prop := ∀ X ∈ Ls, ∀ x ∈ X, 1 ≤ x.1

def BwN (u : ℕ) (Ls : List TrioSeq) : Prop :=
  ∀ σ, 1 ≤ σ → Gof σ u (rword 0 (u + σ) (Ls.map (fun X => mlift X (u + 1) (σ - 1))))

theorem Fr_rword (v : ℕ) (Ls : List TrioSeq) : Fr (rword 0 v Ls) :=
  fun x hx => rword_ge 0 v Ls x hx

theorem BwN_nil (u : ℕ) : BwN u [] := by
  intro σ hσ
  simp only [List.map_nil, rword_nil]
  rcases Nat.eq_or_lt_of_le hσ with h | h
  · subst h; exact (Gof_one_iff u []).mpr (GTs_nil u)
  · exact Gof_nil (by omega) u

theorem BwN_snocz {u : ℕ} {Ls : List TrioSeq} (hL : WF Ls) (hB : BwN u Ls) :
    BwN u (Ls ++ [[]]) := by
  intro σ hσ
  rw [List.map_append, List.map_singleton, mlift_nil, rword_append, rword_singleton]
  have erc : rcol 0 (u + σ) ([] : TrioSeq) = [((1, u + σ + 1, 1) : ℕ × ℕ × ℕ)] := by
    simp [rcol, shiftr01]
  rw [erc, Gof_eq]
  intro Q hQ hF u' hu X hX hQX
  obtain ⟨d, hd⟩ : ∃ d, d = u' - u := ⟨_, rfl⟩
  rw [← hd]
  have hLσ : WF (Ls.map (fun X => mlift X (u + 1) (σ - 1))) := mlift_map_ge hL (u + 1) (σ - 1)
  -- 基準 u' での語の型紙
  obtain ⟨T, hT⟩ : ∃ T : ℕ → List TrioSeq,
      T = fun τ => Ls.map (fun X => mlift (mlift X u d) (u' + 1) (τ - 1)) := ⟨_, rfl⟩
  have hTWF : ∀ τ, WF (T τ) := by
    intro τ X hX
    rw [hT] at hX
    simp only [List.mem_map] at hX
    obtain ⟨Y, hY, rfl⟩ := hX
    exact mlift_ge (mlift_ge (hL Y hY) u d) (u' + 1) (τ - 1)
  have eLift : ∀ τ, 1 ≤ τ →
      (Ls.map (fun X => mlift X (u + 1) (τ - 1))).map (fun X => mlift X u d) = T τ := by
    intro τ _
    rw [hT, List.map_map]
    apply List.map_congr_left
    intro X _
    simp only [Function.comp_apply]
    rw [mlift_comm, show u + 1 + d = u' + 1 by omega]
  have eStep : ∀ τ, 1 ≤ τ → (T τ).map (fun X => mlift X (u' + τ) 1) = T (τ + 1) := by
    intro τ hτ
    rw [hT, List.map_map]
    apply List.map_congr_left
    intro X _
    simp only [Function.comp_apply]
    have := mlift_mlift (mlift X u d) (u' + 1) (τ - 1) 1
    rw [show u' + 1 + (τ - 1) = u' + τ by omega, show τ - 1 + 1 = τ + 1 - 1 by omega] at this
    exact this
  have hBase : ∀ τ, 1 ≤ τ → Gof τ u' (rword 0 (u' + τ) (T τ)) := by
    intro τ hτ
    have h1 := (Gof_ax hτ).lift u _ (Fr_rword _ _) (hB τ hτ) u' hu
    rw [← hd, mlift_rword' (by omega) d _ (mlift_map_ge hL (u + 1) (τ - 1)), eLift τ hτ,
      show u + τ + d = u' + τ by omega] at h1
    exact h1
  have claim : ∀ m τ, 1 ≤ τ →
      Gof τ u' (rword 0 (u' + τ) (T τ) ++
        shiftr01 1 0 (PzW (u' + τ + 1) (T (τ + 1)) m)) := by
    intro m
    induction m with
    | zero =>
        intro τ hτ
        simp only [PzW, List.range_zero, List.flatMap_nil, shiftr01, List.map_nil, List.append_nil]
        exact hBase τ hτ
    | succ m ih =>
        intro τ hτ
        rw [PzW_succ, show u' + τ + 1 = u' + (τ + 1) by omega, eStep (τ + 1) (by omega)]
        have eS : shiftr01 1 0 (((0, u' + (τ + 1), 0) : ℕ × ℕ × ℕ) ::
            (rword 0 (u' + (τ + 1)) (T (τ + 1)) ++
              shiftr01 1 0 (PzW (u' + (τ + 1) + 1) (T (τ + 1 + 1)) m)))
            = ((1, u' + (τ + 1), 0) : ℕ × ℕ × ℕ) ::
              shiftr01 1 0 (rword 0 (u' + (τ + 1)) (T (τ + 1)) ++
                shiftr01 1 0 (PzW (u' + (τ + 1) + 1) (T (τ + 1 + 1)) m)) := by
          simp [shiftr01]
        rw [eS]
        exact Gof_node (ρ := τ) (σ := τ + 1) hτ (by omega) (Fr_rword _ _) (hBase τ hτ)
          (ih (τ + 1) (by omega))
  -- 最後の字の単位
  have hcA : coneV (rword 0 (u + σ) (Ls.map (fun X => mlift X (u + 1) (σ - 1))) ++
      [((1, u + σ + 1, 1) : ℕ × ℕ × ℕ)]) u
      (rword 0 (u + σ) (Ls.map (fun X => mlift X (u + 1) (σ - 1)))).length :=
    coneV_top1 (Fr_rword _ _) (by omega)
  rw [mlift_snoc_cone _ _ hcA d, mlift_rword' (by omega) d _ hLσ, eLift σ hσ]
  have eL1 : (((1, u + σ + 1, 1) : ℕ × ℕ × ℕ).1, ((1, u + σ + 1, 1) : ℕ × ℕ × ℕ).2.1 + d,
      ((1, u + σ + 1, 1) : ℕ × ℕ × ℕ).2.2) = ((1, u' + σ + 1, 1) : ℕ × ℕ × ℕ) := by
    show ((1, u + σ + 1 + d, 1) : ℕ × ℕ × ℕ) = _
    rw [show u + σ + 1 + d = u' + σ + 1 by omega]
  rw [eL1, show u + σ + d = u' + σ by omega]
  obtain ⟨V, hV⟩ : ∃ V : TrioSeq, V = (((0, u' + σ, 0) : ℕ × ℕ × ℕ) :: rword 0 (u' + σ) (T σ)) ++
      [((1, u' + σ + 1, 1) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  have eU : ((1, u' + σ, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (rword 0 (u' + σ) (T σ) ++
      [((1, u' + σ + 1, 1) : ℕ × ℕ × ℕ)]) = shiftr01 1 0 V := by
    rw [hV]; simp [shiftr01]
  rw [eU]
  have hlen : 2 ≤ V.length := by rw [hV]; simp
  have hpV : hasParent V (srow V (V.length - 1)) (V.length - 1) := by
    have hn := natDom_zroot (u' + σ) (X := rword 0 (u' + σ) (T σ)) (rword_ge 0 _ _)
    rw [← hV] at hn
    rcases natDom_iff.mp hn with h | h
    · exfalso
      have hl : V.length - 1 = (((0, u' + σ, 0) : ℕ × ℕ × ℕ) :: rword 0 (u' + σ) (T σ)).length + 0 := by
        rw [hV]; simp
      rw [hl] at h
      unfold lev at h
      rw [hV, entry_append_right, entry_append_right] at h
      simp [entry] at h
    · exact h
  refine hQ.oper u' X (shiftr01 1 0 V) hX (Fr_shift1 V)
    (fun _ => by rw [entry0_shiftr01 (by rw [hV]; simp), hV]; rfl)
    (by rw [shiftr01_length]; exact hlen)
    (by rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]; exact hpV) (fun m hm => ?_)
  have eO := oper_shift [] V 1 m hlen hpV
  simp only [List.nil_append] at eO
  rw [eO, hV, oper_zword (u' + σ) (T σ) (hTWF σ) m]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [PzW_succ, eStep σ hσ]
  have eS : shiftr01 1 0 (((0, u' + σ, 0) : ℕ × ℕ × ℕ) ::
      (rword 0 (u' + σ) (T σ) ++ shiftr01 1 0 (PzW (u' + σ + 1) (T (σ + 1)) m')))
      = ((1, u' + σ, 0) : ℕ × ℕ × ℕ) ::
        shiftr01 1 0 (rword 0 (u' + σ) (T σ) ++ shiftr01 1 0 (PzW (u' + σ + 1) (T (σ + 1)) m')) := by
    simp [shiftr01]
  rw [eS]
  have h := (Gof_eq σ u' _).mp (claim m' σ hσ) Q hQ hF u' le_rfl X hX hQX
  rwa [Nat.sub_self, mlift_zero] at h

#print axioms BwN_snocz

end GxW
end TRIO
