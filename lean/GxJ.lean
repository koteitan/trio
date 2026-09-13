/-
GxJ.lean: 中身を mlift で持ち上げる語の頭の潰れ（型紙の語の基礎）。

    ((0,v,0) :: rword 0 v L ++ (1,v+1,1))⟦n⟧ = PzW v L n
    PzW v L n = Σ_k (k, v+k, 0) :: rword k (v+k) (L.map (mlift · v k))

字の頭は根の錐、中身の列は中身の中の `coneV`（行 0 祖先がすべて行 1 > v）のときだけ持ち上がる。
語の族 `BwT w L := ∀ u ≥ w, rword 0 u (L.map (mlift · w (u - w))) ∈ Wstarv u` は空の字の追加で閉じる。
-/
import GxI
import Lcone

namespace TRIO
namespace GxJ

open Wset
open Small
open GwS
open Gw
open GwU
open GwZ
open GxD
open GxG

/-! ## coneV と mlift の部品 -/

theorem coneV_shift0 {d : ℕ} {Z : TrioSeq} {v j : ℕ} :
    coneV (shiftr01 d 0 Z) v j ↔ coneV Z v j := by
  unfold coneV
  constructor
  · intro h y hy
    have := h y (rtg0_shiftr01.mpr hy)
    rwa [entry1_shiftr01] at this
  · intro h y hy
    rw [entry1_shiftr01]
    exact h y (rtg0_shiftr01.mp hy)

open Classical in
theorem mlift_shift0 (d : ℕ) (Z : TrioSeq) (v t : ℕ) :
    mlift (shiftr01 d 0 Z) v t = shiftr01 d 0 (mlift Z v t) := by
  refine list_ext_getD (by rw [mlift_length, shiftr01_length, shiftr01_length, mlift_length]) ?_
  intro i hi
  rw [mlift_length, shiftr01_length] at hi
  rw [mlift_getD (by rw [shiftr01_length]; exact hi),
    shiftr01_getD (by rw [mlift_length]; exact hi), mlift_getD hi,
    entry0_shiftr01 hi, entry1_shiftr01, entry2_shiftr01]
  by_cases hc : coneV Z v i
  · rw [if_pos (coneV_shift0.mpr hc), if_pos hc] <;> rfl
  · rw [if_neg (fun h => hc (coneV_shift0.mp h)), if_neg hc] <;> rfl

theorem coneV_append_left {A B : TrioSeq} {v j : ℕ} (hj : j < A.length) :
    coneV (A ++ B) v j ↔ coneV A v j := by
  rw [coneV_iff_amin, coneV_iff_amin]
  have h := amin_take (X := A ++ B) (l := A.length) (by simp) hj
  rw [List.take_left] at h
  rw [h]

theorem rtg0_append_unlift {A B : TrioSeq} {y b : ℕ} (hy : A.length ≤ y)
    (h : Relation.ReflTransGen (nextrel0 (A ++ B)) y b) :
    ∀ b', b = A.length + b' → Relation.ReflTransGen (nextrel0 B) (y - A.length) b' := by
  induction h with
  | refl => intro b' hb'; rw [show y - A.length = b' from by omega]
  | @tail w c hw hwc ih =>
      intro b' hb'
      subst hb'
      have hwy : y ≤ w := rtg0_le hw
      obtain ⟨w', rfl⟩ : ∃ w', w = A.length + w' := ⟨w - A.length, by omega⟩
      have hstep : nextrel0 B w' b' := (nextrel0_append_right A B w' b').1 hwc
      exact (ih w' rfl).tail hstep

theorem coneV_append_right {A B : TrioSeq} {v q : ℕ} (hq : q < B.length)
    (hrs : ∀ x ∈ A, entry B 0 0 ≤ x.1) :
    coneV (A ++ B) v (A.length + q) ↔ coneV B v q := by
  unfold coneV
  constructor
  · intro h y hy
    have := h (A.length + y) (rtg_nextrel0_lift A B hy)
    rwa [entry_append_right] at this
  · intro h y hy
    rcases Nat.lt_or_ge y A.length with hyA | hyA
    · exfalso
      have hw := window_of_rtg0 hy (by simp; omega) A.length hyA (by omega)
      rw [Small.entry_append_left hyA, show A.length = A.length + 0 from rfl,
        entry_append_right] at hw
      have hmem := GxF.getD_mem_P hyA (P := fun x => entry B 0 0 ≤ x.1) hrs
      have : entry B 0 0 ≤ entry A 0 y := hmem
      omega
    · have h1 := h (y - A.length) (rtg0_append_unlift hyA hy q rfl)
      rw [show y = A.length + (y - A.length) from by omega, entry_append_right]
      exact h1

open Classical in
theorem mlift_append {A B : TrioSeq} (hrs : ∀ x ∈ A, entry B 0 0 ≤ x.1) (v t : ℕ) :
    mlift (A ++ B) v t = mlift A v t ++ mlift B v t := by
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [mlift_length, List.length_append] at hi
  rw [mlift_getD (by rw [List.length_append]; omega)]
  rcases Nat.lt_or_ge i A.length with hiA | hiA
  · have eg : (mlift A v t ++ mlift B v t).getD i (0, 0, 0) = (mlift A v t).getD i (0, 0, 0) := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [mlift_length]; exact hiA)]
    rw [eg, mlift_getD hiA, Small.entry_append_left hiA, Small.entry_append_left hiA,
      Small.entry_append_left hiA]
    by_cases hc : coneV A v i
    · rw [if_pos ((coneV_append_left hiA).mpr hc), if_pos hc]
    · rw [if_neg (fun h => hc ((coneV_append_left hiA).mp h)), if_neg hc]
  · obtain ⟨q, rfl⟩ : ∃ q, i = A.length + q := ⟨i - A.length, by omega⟩
    have hq : q < B.length := by omega
    rw [getD_app_right _ _ (by rw [mlift_length]; omega), mlift_length,
      show A.length + q - A.length = q from by omega, mlift_getD hq,
      entry_append_right, entry_append_right, entry_append_right]
    by_cases hc : coneV B v q
    · rw [if_pos ((coneV_append_right hq hrs).mpr hc), if_pos hc]
    · rw [if_neg (fun h => hc ((coneV_append_right hq hrs).mp h)), if_neg hc]

open Classical in
theorem mlift_cons_plant {X : TrioSeq} (hX : ∀ x ∈ X, 1 ≤ x.1) (v t z : ℕ) :
    mlift (((0, v + 1, z) : ℕ × ℕ × ℕ) :: X) v t
      = ((0, v + 1 + t, z) : ℕ × ℕ × ℕ) :: mlift X v t := by
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [mlift_length] at hi
  rw [mlift_getD hi]
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · have hc : coneV (((0, v + 1, z) : ℕ × ℕ × ℕ) :: X) v 0 := by
      rw [coneV_iff_amin, amin_zero]; simp [entry]
    rw [if_pos hc]
    simp [entry]
  · obtain ⟨j, rfl⟩ : ∃ j, i = 1 + j := ⟨i - 1, by omega⟩
    have hj : j < X.length := by simp at hi; omega
    have e : ∀ r, entry (((0, v + 1, z) : ℕ × ℕ × ℕ) :: X) r (1 + j) = entry X r j := by
      intro r; rw [show 1 + j = j + 1 by omega, entry_cons]
    rw [e 0, e 1, e 2]
    have eg : (((0, v + 1 + t, z) : ℕ × ℕ × ℕ) :: mlift X v t).getD (1 + j) (0, 0, 0)
        = (mlift X v t).getD j (0, 0, 0) := by
      rw [show 1 + j = j + 1 by omega]; rfl
    rw [eg, mlift_getD hj]
    have hiff := coneV_cons_iff (B := v + 1) (z := z) (v := v) (fun p hp => hX p hp) hj
    by_cases hc : coneV X v j
    · rw [if_pos (hiff.mpr ⟨by omega, hc⟩), if_pos hc]
    · rw [if_neg (fun h => hc (hiff.mp h).2), if_neg hc]

theorem mlift_rcol {X : TrioSeq} (hX : ∀ x ∈ X, 1 ≤ x.1) (v t : ℕ) :
    mlift (rcol 0 v X) v t = rcol 0 (v + t) (mlift X v t) := by
  have e1 : rcol 0 v X = shiftr01 1 0 (((0, v + 1, 1) : ℕ × ℕ × ℕ) :: X) := by
    simp [rcol, shiftr01]
  have e2 : rcol 0 (v + t) (mlift X v t)
      = shiftr01 1 0 (((0, v + t + 1, 1) : ℕ × ℕ × ℕ) :: mlift X v t) := by
    simp [rcol, shiftr01]
  rw [e1, e2, mlift_shift0, mlift_cons_plant hX, show v + 1 + t = v + t + 1 by omega]

theorem mlift_nil (v t : ℕ) : mlift ([] : TrioSeq) v t = [] := by simp [mlift]

theorem mlift_ge {X : TrioSeq} (hX : ∀ x ∈ X, 1 ≤ x.1) (v t : ℕ) :
    ∀ x ∈ mlift X v t, 1 ≤ x.1 := by
  intro x hx
  simp only [mlift, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact GxF.getD_mem_P hi (P := fun x => 1 ≤ x.1) hX

theorem mlift_rword (v t : ℕ) : ∀ (L : List TrioSeq), (∀ X ∈ L, ∀ x ∈ X, 1 ≤ x.1) →
    mlift (rword 0 v L) v t = rword 0 (v + t) (L.map (fun X => mlift X v t))
  | [], _ => by simp [rword, mlift]
  | (X :: L'), hL => by
      rw [rword_cons, List.map_cons, rword_cons]
      have hrs : ∀ x ∈ rcol 0 v X, entry (rword 0 v L') 0 0 ≤ x.1 := by
        intro x hx
        have h1 := rcol_ge 0 v X x hx
        cases L' with
        | nil => simp [rword, entry]
        | cons Y L'' => rw [rword_cons]; simp [rcol, entry]; omega
      rw [mlift_append hrs, mlift_rcol (hL X (by simp)),
        mlift_rword v t L' (fun Y hY => hL Y (List.mem_cons_of_mem _ hY))]

theorem mlift_mlift (X : TrioSeq) (v t s : ℕ) :
    mlift (mlift X v t) (v + t) s = mlift X v (t + s) := by
  rw [mlift_eq_slift, mlift_eq_slift, mlift_eq_slift,
    slift_slift (stair_step v t) (stair_step (v + t) s)]
  congr 1
  funext m
  split_ifs <;> omega

theorem mlift_zero (X : TrioSeq) (v : ℕ) : mlift X v 0 = X := by
  classical
  refine list_ext_getD (by simp) ?_
  intro i hi
  rw [mlift_length] at hi
  rw [mlift_getD hi]
  simp only [ite_self, Nat.add_zero]
  exact (getD_eq_entries X i).symm

/-! ## 頭の潰れ -/

noncomputable def PzW (v : ℕ) (L : List TrioSeq) (n : ℕ) : TrioSeq :=
  (List.range n).flatMap (fun k => ((k, v + k, 0) : ℕ × ℕ × ℕ) ::
    rword k (v + k) (L.map (fun X => mlift X v k)))

open Classical in
theorem oper_zword (v : ℕ) (L : List TrioSeq) (hL : ∀ X ∈ L, ∀ x ∈ X, 1 ≤ x.1) (n : ℕ) :
    ((((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v L) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)])⟦n⟧
      = PzW v L n := by
  have h := oper_z1_mask [] 0 v (rword 0 v L) (rword_ge 0 v L) n
  have eM : (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v L) ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]
      = [] ++ (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v L ++ [((0 + 1, v + 1, 1) : ℕ × ℕ × ℕ)]) :=
    rfl
  rw [eM, h, List.nil_append]
  unfold PzW
  apply List.flatMap_congr
  intro k _
  simp only [Nat.zero_add, List.length_nil, List.nil_append]
  congr 1
  have hXge : ∀ x ∈ rword 0 v L, 1 ≤ x.1 := fun x hx => rword_ge 0 v L x hx
  have hR : argOK (rword 0 v L ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]) := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hXge p hp
    · simp only [List.mem_singleton] at hp; subst hp; simp
  have hmask : ∀ i, i < (rword 0 v L).length →
      (le1 (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v L ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]) 0 (1 + i)
        ↔ coneV (rword 0 v L) v i) := by
    intro i hi
    rw [show (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v L ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)])
        = ((0, v, 0) : ℕ × ℕ × ℕ) :: (rword 0 v L ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]) from rfl,
      le1_cons_iff_coneV hR (by simp; omega), coneV_append_left hi]
  have hmap : (List.range (rword 0 v L).length).map (fun i =>
        ((entry (rword 0 v L) 0 i + k, entry (rword 0 v L) 1 i +
          (if le1 (((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v L ++ [((1, v + 1, 1) : ℕ × ℕ × ℕ)]) 0
            (1 + i) then k else 0),
          entry (rword 0 v L) 2 i) : ℕ × ℕ × ℕ))
      = shiftr01 k 0 (mlift (rword 0 v L) v k) := by
    refine list_ext_getD (by simp [shiftr01]) ?_
    intro i hi
    simp only [List.length_map, List.length_range] at hi
    rw [shiftr01_getD (by rw [mlift_length]; exact hi), mlift_getD hi,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    simp only [Option.map_some, Option.getD_some]
    by_cases hc : coneV (rword 0 v L) v i
    · rw [if_pos ((hmask i hi).mpr hc), if_pos hc] <;> rfl
    · rw [if_neg (fun h => hc ((hmask i hi).mp h)), if_neg hc] <;> rfl
  rw [hmap, mlift_rword v k L hL, rword_shift, Nat.zero_add]

#print axioms oper_zword


/-! ## 型紙の語の族 -/

theorem PzW_succ (v : ℕ) (L : List TrioSeq) (n : ℕ) :
    PzW v L (n + 1) = ((0, v, 0) : ℕ × ℕ × ℕ) ::
      (rword 0 v L ++ shiftr01 1 0 (PzW (v + 1) (L.map (fun X => mlift X v 1)) n)) := by
  unfold PzW
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, GwV.shiftr01_flatMap]
  have e0 : (((0, v + 0, 0) : ℕ × ℕ × ℕ) :: rword 0 (v + 0) (L.map (fun X => mlift X v 0)))
      = ((0, v, 0) : ℕ × ℕ × ℕ) :: rword 0 v L := by
    simp [mlift_zero]
  rw [e0, List.cons_append]
  congr 2
  apply List.flatMap_congr
  intro k _
  have hf : ((fun X => mlift X (v + 1) k) ∘ fun X => mlift X v 1) = (fun X => mlift X v (k + 1)) := by
    funext X
    simp only [Function.comp_apply]
    rw [mlift_mlift, Nat.add_comm 1 k]
  have e1 : shiftr01 1 0 (((k, v + 1 + k, 0) : ℕ × ℕ × ℕ) ::
      rword k (v + 1 + k) ((L.map (fun X => mlift X v 1)).map (fun X => mlift X (v + 1) k)))
      = ((k + 1, v + (k + 1), 0) : ℕ × ℕ × ℕ) ::
        rword (k + 1) (v + (k + 1)) (L.map (fun X => mlift X v (k + 1))) := by
    rw [show ((k, v + 1 + k, 0) : ℕ × ℕ × ℕ) ::
          rword k (v + 1 + k) ((L.map (fun X => mlift X v 1)).map (fun X => mlift X (v + 1) k))
        = [((k, v + 1 + k, 0) : ℕ × ℕ × ℕ)] ++
          rword k (v + 1 + k) ((L.map (fun X => mlift X v 1)).map (fun X => mlift X (v + 1) k))
        from rfl, shiftr01_append0, rword_shift, List.map_map, hf,
      show v + 1 + k = v + (k + 1) by omega]
    simp [shiftr01]
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  rw [e1]

theorem mlift_map_ge {L : List TrioSeq} (hL : ∀ X ∈ L, ∀ x ∈ X, 1 ≤ x.1) (v t : ℕ) :
    ∀ X ∈ L.map (fun X => mlift X v t), ∀ x ∈ X, 1 ≤ x.1 := by
  intro X hX
  simp only [List.mem_map] at hX
  obtain ⟨Y, hY, rfl⟩ := hX
  exact mlift_ge (hL Y hY) v t

/-- 型紙の語: 段 w の中身の並び `L` を、段 u では `mlift · w (u - w)` で上げる。 -/
def BwT (w : ℕ) (L : List TrioSeq) : Prop :=
  ∀ u, w ≤ u → rword 0 u (L.map (fun X => mlift X w (u - w))) ∈ Wstarv u

theorem map_mlift_step {L : List TrioSeq} {w u : ℕ} (hu : w ≤ u) :
    (L.map (fun X => mlift X w (u - w))).map (fun X => mlift X u 1)
      = L.map (fun X => mlift X w (u + 1 - w)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro X _
  simp only [Function.comp_apply]
  have := mlift_mlift X w (u - w) 1
  rw [show w + (u - w) = u by omega] at this
  rw [this, show u - w + 1 = u + 1 - w by omega]

theorem PzW_Wg {w : ℕ} {L : List TrioSeq} (hB : BwT w L) :
    ∀ n u, w ≤ u → PzW u (L.map (fun X => mlift X w (u - w))) n ∈ Wg (2 * u) := by
  intro n
  induction n with
  | zero => intro u _; simpa [PzW] using Wg_nil (2 * u)
  | succ n ih =>
      intro u hu
      rw [PzW_succ, map_mlift_step hu]
      have hR := Wg_shift (ih (u + 1) (by omega)) 1
      refine hangv (hB u hu) (fun x hx => rword_ge 0 u _ x hx) hR (shift1_ge _) ?_ (2 * u) le_rfl
      cases n with
      | zero => simp [PzW, shiftr01, entry]
      | succ m => simp [PzW, List.range_succ_eq_map, shiftr01, entry]

theorem BwT_nil (w : ℕ) : BwT w [] := by
  intro u _ _ a ha
  show (((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u (([] : List TrioSeq).map _)) ∈ Wg a
  simp only [List.map_nil, rword_nil]
  exact Wg_mono ha (Om_mem_Wg u)

theorem BwT_snocz {w : ℕ} {L : List TrioSeq} (hL : ∀ X ∈ L, ∀ x ∈ X, 1 ≤ x.1) (hB : BwT w L) :
    BwT w (L ++ [[]]) := by
  intro u hu _ a ha
  have e : (((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u ((L ++ [[]]).map (fun X => mlift X w (u - w))))
      = (((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u (L.map (fun X => mlift X w (u - w)))) ++
        [((1, u + 1, 1) : ℕ × ℕ × ℕ)] := by
    rw [List.map_append, rword_append]
    simp [mlift_nil, rword, rcol, shiftr01]
  rw [e]
  refine A1g_intro (Or.inr (Or.inl ⟨natDom_zroot u (fun x hx => by
    have := rword_ge 0 u _ x hx; omega), fun n _ => ?_⟩))
  rw [oper_zword u _ (mlift_map_ge hL w (u - w)) n]
  exact Wg_mono ha (PzW_Wg hB n u hu)

#print axioms BwT_snocz

end GxJ
end TRIO
