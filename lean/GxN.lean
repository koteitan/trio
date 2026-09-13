/-
GxN.lean: 任意の深さの単位の閉包。

中身の木で、錐のタイ `(d+1, u+1, 0)` の下に子（荷や入れ子のタイ）を持つ形を扱う。
平らな列はタイの部分木を複写するので、単位を前の文脈によらず継げる形 `SC` で閉包を作る。

    GTall v K    := ∀ u ≥ v, GT u (mlift K v (u - v))
    PathCone u d Y : Y の右から見える行 0 ≤ d の列はすべて錐（行 1 > u）
    Att d u Y      : Y の開いた単位の列（深さ d まで）。各単位はどの文脈にも継げる
    SC d u U       : 深さ d の文脈なら、単位の並び U を d だけずらして継げる
-/
import GxL

namespace TRIO
namespace GxN

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

/-! ## GTall の規則 -/

theorem GTall_lift {v : ℕ} {K : TrioSeq} (h : GTall v K) {w : ℕ} (hvw : v ≤ w) :
    GTall w (mlift K v (w - v)) := by
  intro u hu
  have := h u (le_trans hvw hu)
  have e := mlift_mlift K v (w - v) (u - w)
  rw [show v + (w - v) = w by omega, show w - v + (u - w) = u - v by omega] at e
  rw [e]; exact this

theorem GT_of_GTall {v : ℕ} {K : TrioSeq} (h : GTall v K) : GT v K := by
  have := h v le_rfl
  rwa [Nat.sub_self, mlift_zero] at this

theorem GTall_nil (v : ℕ) : GTall v [] := by
  intro u _
  rw [mlift_nil]; exact GT_nil u

theorem GTall_oper {v : ℕ} {K : TrioSeq} (hlen : 2 ≤ K.length)
    (hp : hasParent K (srow K (K.length - 1)) (K.length - 1))
    (hIH : ∀ n, 1 ≤ n → GTall v (K⟦n⟧)) : GTall v K := by
  intro u hu
  have hS := stair_step v (u - v)
  have eK : mlift K v (u - v) = slift K (fun m => m + (if v < m then (u - v) else 0)) :=
    mlift_eq_slift K v (u - v)
  have hlen' : 2 ≤ (mlift K v (u - v)).length := by rw [mlift_length]; exact hlen
  have hp' : hasParent (mlift K v (u - v))
      (srow (mlift K v (u - v)) ((mlift K v (u - v)).length - 1))
      ((mlift K v (u - v)).length - 1) := by
    rw [mlift_length, eK, hasParent_slift hS, srow_slift hS (by omega)]; exact hp
  refine GT_oper hlen' hp' (fun n hn => ?_)
  have e2 : (mlift K v (u - v))⟦n⟧ = mlift (K⟦n⟧) v (u - v) := by
    rw [eK, mlift_eq_slift, slift_oper hS]
  rw [e2]; exact hIH n hn u hu

theorem GTall_flat {v : ℕ} {K : TrioSeq} {x : ℕ} (hx : 1 ≤ x) (hK : ∀ y ∈ K, 1 ≤ y.1)
    (hKx : ∀ y ∈ K, x ≤ y.1) (hG : GTall v K) : GTall v (K ++ [((x, 0, 0) : ℕ × ℕ × ℕ)]) := by
  intro u hu
  rw [mlift_snoc_flat K x v (u - v) hKx]
  exact GT_flat hx (mlift_row0 hK v (u - v)) (mlift_row0 hKx v (u - v)) (hG u hu)

theorem GTall_orph {v : ℕ} {K : TrioSeq} {h j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ v)
    (hnp : ¬ hasParent (K ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1
      ((K ++ [((h, j, 0) : ℕ × ℕ × ℕ)]).length - 1))
    (hzK : ∀ z ∈ Wg (2 * j - 1), based z → GTall v (K ++ shiftr01 h 0 z)) :
    GTall v (K ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
  intro u hu
  have hS := stair_step v (u - v)
  have hjv : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ v := hj
  rw [mlift_snoc_low K _ hjv (u - v)]
  refine GT_orph hj1 (le_trans hj hu) ?_ (fun z hz hbz => ?_)
  · rw [← mlift_snoc_low K _ hjv (u - v), mlift_eq_slift, hasParent_slift hS, slift_length]
    exact hnp
  · have := hzK z hz hbz u hu
    rwa [mlift_append_low (low_of_Wg (Wg_mono (by omega) hz) h hj)] at this

theorem rtg0_slift' {A : TrioSeq} {φ : ℕ → ℕ} {a b : ℕ} :
    Relation.ReflTransGen (nextrel0 (slift A φ)) a b ↔
      Relation.ReflTransGen (nextrel0 A) a b := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y w _ hyw ih => exact ih.tail (nextrel0_slift.1 hyw)
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y w _ hyw ih => exact ih.tail (nextrel0_slift.2 hyw)

open Classical in
theorem coneV_mlift {A : TrioSeq} {v j : ℕ} (hj : j < A.length) (hc : coneV A v j) (t : ℕ) :
    coneV (mlift A v t) (v + t) j := by
  intro y hy
  rw [mlift_eq_slift] at hy
  have hy' := rtg0_slift'.mp hy
  have hyj := rtg0_le hy'
  have hcy : coneV A v y := fun z hz => hc z (hz.trans hy')
  have hvy := hc y hy'
  show v + t < ((mlift A v t).getD y (0, 0, 0)).2.1
  rw [mlift_getD (by omega), if_pos hcy]
  show v + t < entry A 1 y + t
  omega

theorem GTall_tie {v : ℕ} {K : TrioSeq} {x : ℕ}
    (hcone : coneV (K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]) v K.length)
    (hload : ∀ u, v ≤ u → ∀ Z ∈ Wg (2 * u), based Z →
      GTall u (mlift K v (u - v) ++ shiftr01 x 0 Z)) :
    GTall v (K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]) := by
  intro u hu
  have eK : mlift (K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]) v (u - v)
      = mlift K v (u - v) ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_cone K _ hcone (u - v)]
    show _ ++ [((x, v + 1 + (u - v), 0) : ℕ × ℕ × ℕ)] = _
    rw [show v + 1 + (u - v) = u + 1 by omega]
  rw [eK]
  have hc' : coneV (mlift K v (u - v) ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) u
      (mlift K v (u - v)).length := by
    have := coneV_mlift (by simp) hcone (u - v)
    rw [eK, show v + (u - v) = u by omega] at this
    rw [mlift_length]; exact this
  refine GT_tie hc' (fun u' hu' Z hZ hbZ => ?_)
  have e := mlift_mlift K v (u - v) (u' - u)
  rw [show v + (u - v) = u by omega, show u - v + (u' - u) = u' - v by omega] at e
  rw [e]
  have := hload u' (le_trans hu hu') Z hZ hbZ u' le_rfl
  rwa [Nat.sub_self, mlift_zero] at this

theorem GTall_loadTop {v : ℕ} {K : TrioSeq} (hK : ∀ y ∈ K, 1 ≤ y.1) (hG : GTall v K)
    {Z : TrioSeq} (hZ : Z ∈ Wg (2 * v)) (hb : based Z) : GTall v (K ++ shiftr01 1 0 Z) := by
  intro u hu
  rw [mlift_append_low (low_of_Wg hZ 1 le_rfl)]
  exact GT_loadTop (mlift_row0 hK v (u - v)) (hG u hu) Z (Wg_mono (by omega) hZ) hb

#print axioms GTall_tie

/-! ## 右から見える錐の道 -/

def PathCone (u d : ℕ) (Y : TrioSeq) : Prop :=
  ∀ y, y < Y.length → (∀ k, y < k → k < Y.length → entry Y 0 y < entry Y 0 k) →
    entry Y 0 y ≤ d → u < entry Y 1 y

theorem getD_row0_ge {B : TrioSeq} {c i : ℕ} (hB : ∀ b ∈ B, c ≤ b.1) (hi : i < B.length) :
    c ≤ entry B 0 i := by
  have hmem : B.getD i (0, 0, 0) ∈ B := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi
  exact hB _ hmem

theorem PathCone_append {u d : ℕ} {Y B : TrioSeq} (hB : ∀ b ∈ B, d + 1 ≤ b.1)
    (h : PathCone u d Y) : PathCone u d (Y ++ B) := by
  intro y hy hvis hd
  rcases Nat.lt_or_ge y Y.length with hlt | hge
  · rw [Small.entry_append_left hlt] at hd ⊢
    refine h y hlt (fun k hk1 hk2 => ?_) hd
    have := hvis k hk1 (by simp; omega)
    rwa [Small.entry_append_left hlt, Small.entry_append_left hk2] at this
  · exfalso
    obtain ⟨i, rfl⟩ : ∃ i, y = Y.length + i := ⟨y - Y.length, by omega⟩
    rw [entry_append_right] at hd
    have hi : i < B.length := by simp at hy; omega
    have := getD_row0_ge hB hi
    omega

theorem coneV_of_PathCone {u d : ℕ} {Y : TrioSeq} (h : PathCone u d Y) {y : ℕ}
    (hy : y < Y.length) (hvis : ∀ k, y < k → k < Y.length → entry Y 0 y < entry Y 0 k)
    (hd : entry Y 0 y ≤ d) : coneV Y u y := by
  intro z hz
  have hzy := rtg0_le hz
  refine h z (by omega) (fun k hk1 hk2 => ?_) ?_
  · rcases Nat.lt_or_ge y k with hyk | hky
    · have := hvis k hyk hk2
      rcases Nat.eq_or_lt_of_le hzy with rfl | hzy'
      · exact this
      · have := rtg0_rec hz y hzy' le_rfl
        omega
    · exact rtg0_rec hz k hk1 hky
  · rcases Nat.eq_or_lt_of_le hzy with rfl | hzy'
    · exact hd
    · have := rtg0_rec hz y hzy' le_rfl
      omega

open Classical in
theorem PathCone_lift {u d : ℕ} {Y : TrioSeq} (h : PathCone u d Y) {u' : ℕ} (hu : u ≤ u') :
    PathCone u' d (mlift Y u (u' - u)) := by
  intro y hy hvis hd
  rw [mlift_length] at hy
  have e0 : ∀ k, k < Y.length → entry (mlift Y u (u' - u)) 0 k = entry Y 0 k := by
    intro k hk
    show ((mlift Y u (u' - u)).getD k (0, 0, 0)).1 = _
    rw [mlift_getD hk]
  have hvis' : ∀ k, y < k → k < Y.length → entry Y 0 y < entry Y 0 k := by
    intro k hk1 hk2
    have := hvis k hk1 (by rw [mlift_length]; exact hk2)
    rwa [e0 y hy, e0 k hk2] at this
  rw [e0 y hy] at hd
  have hc := coneV_of_PathCone h hy hvis' hd
  have := h y hy hvis' hd
  show u' < ((mlift Y u (u' - u)).getD y (0, 0, 0)).2.1
  rw [mlift_getD hy, if_pos hc]
  show u' < entry Y 1 y + (u' - u)
  omega

theorem coneV_pathB {u d : ℕ} {Y B : TrioSeq} (hP : PathCone u d Y)
    (hB0 : B ≠ [] → entry B 0 0 = d + 1) {i : ℕ} (hi : i < B.length) :
    coneV (Y ++ B) u (Y.length + i) ↔ coneV B u i := by
  constructor
  · intro h k hk
    have := h (Y.length + k) (rtg0_append_lift hk)
    rwa [entry_append_right] at this
  · intro h y hy
    rcases Nat.lt_or_ge y Y.length with hlt | hge
    · rw [Small.entry_append_left hlt]
      have hBne : B ≠ [] := by intro hh; rw [hh] at hi; simp at hi
      refine hP y hlt (fun k hk1 hk2 => ?_) ?_
      · have := rtg0_rec hy k hk1 (by omega)
        rwa [Small.entry_append_left hlt, Small.entry_append_left hk2] at this
      · have := rtg0_rec hy Y.length hlt (by omega)
        rw [Small.entry_append_left hlt, show Y.length = Y.length + 0 from rfl,
          entry_append_right, hB0 hBne] at this
        omega
    · have h2 := rtg0_append_unlift hge hy i rfl
      have := h (y - Y.length) h2
      rw [show y = Y.length + (y - Y.length) by omega, entry_append_right]
      exact this

open Classical in
theorem mlift_pathB {u d : ℕ} {Y B : TrioSeq} (hP : PathCone u d Y)
    (hB0 : B ≠ [] → entry B 0 0 = d + 1) (t : ℕ) :
    mlift (Y ++ B) u t = mlift Y u t ++ mlift B u t := by
  unfold mlift
  rw [List.length_append, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    rw [Small.entry_append_left hj, Small.entry_append_left hj, Small.entry_append_left hj,
      if_congr (coneV_append_left hj) rfl rfl]
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp_apply]
    rw [entry_append_right, entry_append_right, entry_append_right,
      if_congr (coneV_pathB hP hB0 hi) rfl rfl]

#print axioms mlift_pathB


/-! ## 開いた単位の文脈 Att と単位の閉包 SC -/

def RootP (d u : ℕ) (P : TrioSeq) : Prop :=
  P ≠ [] ∧ entry P 0 0 = d + 1 ∧ u < entry P 1 0 ∧
    ∀ i, 1 ≤ i → i < P.length → d + 2 ≤ entry P 0 i

def UnitOKp (A : ℕ → TrioSeq → Prop) (d u : ℕ) (P : TrioSeq) : Prop :=
  ∀ u', u ≤ u' → ∀ Y : TrioSeq, (∀ y ∈ Y, 1 ≤ y.1) → A u' Y → PathCone u' d Y → GTall u' Y →
    GTall u' (Y ++ mlift P u (u' - u))

def Att : ℕ → ℕ → TrioSeq → Prop
  | 0, _, _ => True
  | (d + 1), u, Y => ∃ Y' P : TrioSeq, Y = Y' ++ P ∧ Att d u Y' ∧ GTall u Y' ∧
      (∀ y ∈ Y', 1 ≤ y.1) ∧ PathCone u d Y' ∧ RootP d u P ∧ UnitOKp (Att d) d u P

def SC (d u : ℕ) (U : TrioSeq) : Prop := UnitOKp (Att d) d u (shiftr01 d 0 U)

theorem RootP_ge {d u : ℕ} {P : TrioSeq} (h : RootP d u P) : ∀ y ∈ P, d + 1 ≤ y.1 := by
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  have e : P[i] = P.getD i (0, 0, 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  rw [e]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have := h.2.1; show d + 1 ≤ entry P 0 0; omega
  · have := h.2.2.2 i hpos hi; show d + 1 ≤ entry P 0 i; omega

theorem PathCone_root {d u : ℕ} {P : TrioSeq} (h : RootP d u P) : PathCone u (d + 1) P := by
  intro y hy _ hd
  rcases Nat.eq_zero_or_pos y with rfl | hpos
  · exact h.2.2.1
  · have := h.2.2.2 y hpos hy; omega

theorem PathCone_open {d u : ℕ} {Y P : TrioSeq} (hY : PathCone u d Y) (hP : RootP d u P) :
    PathCone u (d + 1) (Y ++ P) := by
  intro y hy hvis hd
  have hPlen : 0 < P.length := List.length_pos_iff.mpr hP.1
  rcases Nat.lt_or_ge y Y.length with hlt | hge
  · have h1 := hvis Y.length hlt (by simp; omega)
    rw [Small.entry_append_left hlt, show Y.length = Y.length + 0 from rfl, entry_append_right,
      hP.2.1] at h1
    rw [Small.entry_append_left hlt]
    refine hY y hlt (fun k hk1 hk2 => ?_) (by omega)
    have := hvis k hk1 (by simp; omega)
    rwa [Small.entry_append_left hlt, Small.entry_append_left hk2] at this
  · obtain ⟨i, rfl⟩ : ∃ i, y = Y.length + i := ⟨y - Y.length, by omega⟩
    have hi : i < P.length := by simp at hy; omega
    rw [entry_append_right] at hd ⊢
    exact PathCone_root hP i hi (fun k hk1 hk2 => by
      have := hvis (Y.length + k) (by omega) (by simp; omega)
      rwa [entry_append_right, entry_append_right] at this) hd

open Classical in
theorem RootP_lift {d u : ℕ} {P : TrioSeq} (h : RootP d u P) {w : ℕ} (hw : u ≤ w) :
    RootP d w (mlift P u (w - u)) := by
  have hPlen : 0 < P.length := List.length_pos_iff.mpr h.1
  have hc : coneV P u 0 := by
    intro y hy
    have := rtg0_le hy
    have hy0 : y = 0 := by omega
    subst hy0; exact h.2.2.1
  refine ⟨by intro hh; have := congrArg List.length hh; rw [mlift_length, List.length_nil] at this; omega, ?_, ?_, ?_⟩
  · show ((mlift P u (w - u)).getD 0 (0, 0, 0)).1 = d + 1
    rw [mlift_getD hPlen]; exact h.2.1
  · show w < ((mlift P u (w - u)).getD 0 (0, 0, 0)).2.1
    rw [mlift_getD hPlen, if_pos hc]
    show w < entry P 1 0 + (w - u)
    have := h.2.2.1; omega
  · intro i hi1 hi2
    rw [mlift_length] at hi2
    show d + 2 ≤ ((mlift P u (w - u)).getD i (0, 0, 0)).1
    rw [mlift_getD hi2]; exact h.2.2.2 i hi1 hi2

theorem UnitOKp_lift {A : ℕ → TrioSeq → Prop} {d u : ℕ} {P : TrioSeq} (h : UnitOKp A d u P)
    {w : ℕ} (hw : u ≤ w) : UnitOKp A d w (mlift P u (w - u)) := by
  intro u' hu' Y hge hA hPC hG
  have e := mlift_mlift P u (w - u) (u' - w)
  rw [show u + (w - u) = w by omega, show w - u + (u' - w) = u' - u by omega] at e
  rw [e]
  exact h u' (le_trans hw hu') Y hge hA hPC hG

theorem Att_lift : ∀ (d : ℕ) {u : ℕ} {Y : TrioSeq}, Att d u Y → ∀ {w : ℕ}, u ≤ w →
    Att d w (mlift Y u (w - u)) := by
  intro d
  induction d with
  | zero => intro _ _ _ _ _; trivial
  | succ d ih =>
      intro u Y hA w hw
      obtain ⟨Y', P, rfl, hA', hG, hge, hPC, hR, hU⟩ := hA
      exact ⟨mlift Y' u (w - u), mlift P u (w - u), mlift_pathB hPC (fun _ => hR.2.1) _,
        ih hA' hw, GTall_lift hG hw, mlift_row0 hge u (w - u), PathCone_lift hPC hw,
        RootP_lift hR hw, UnitOKp_lift hU hw⟩

theorem Att_close {d u : ℕ} {Y W : TrioSeq} (hA : Att (d + 1) u Y)
    (hW0 : W ≠ [] → entry W 0 0 = d + 2) (hWge : ∀ x ∈ W, d + 2 ≤ x.1)
    (hWU : UnitOKp (Att (d + 1)) (d + 1) u W) : Att (d + 1) u (Y ++ W) := by
  obtain ⟨Y', P, rfl, hA', hG, hge, hPC, hR, hU⟩ := hA
  have hPlen : 0 < P.length := List.length_pos_iff.mpr hR.1
  refine ⟨Y', P ++ W, by rw [List.append_assoc], hA', hG, hge, hPC, ?_, ?_⟩
  · refine ⟨by simp [hR.1], ?_, ?_, ?_⟩
    · rw [Small.entry_append_left hPlen]; exact hR.2.1
    · rw [Small.entry_append_left hPlen]; exact hR.2.2.1
    · intro i hi1 hi2
      rcases Nat.lt_or_ge i P.length with hlt | hge2
      · rw [Small.entry_append_left hlt]; exact hR.2.2.2 i hi1 hlt
      · obtain ⟨k, rfl⟩ : ∃ k, i = P.length + k := ⟨i - P.length, by omega⟩
        rw [entry_append_right]
        exact getD_row0_ge hWge (by simp at hi2; omega)
  · intro u' hu' Y2 hge2 hA2 hPC2 hG2
    rw [mlift_pathB (PathCone_root hR) hW0, ← List.append_assoc]
    have h1 := hU u' hu' Y2 hge2 hA2 hPC2 hG2
    have hR' := RootP_lift hR hu'
    have hA3 : Att (d + 1) u' (Y2 ++ mlift P u (u' - u)) :=
      ⟨Y2, mlift P u (u' - u), rfl, hA2, hG2, hge2, hPC2, hR', UnitOKp_lift hU hu'⟩
    have hge3 : ∀ y ∈ Y2 ++ mlift P u (u' - u), 1 ≤ y.1 := by
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hge2 y hy
      · have := mlift_row0 (RootP_ge hR) u (u' - u) y hy; omega
    exact hWU u' hu' _ hge3 hA3 (PathCone_open hPC2 hR') h1

theorem Att_extend : ∀ (d : ℕ) {u : ℕ} {Y W : TrioSeq}, Att d u Y →
    (W ≠ [] → entry W 0 0 = d + 1) → (∀ x ∈ W, d + 1 ≤ x.1) → UnitOKp (Att d) d u W →
    Att d u (Y ++ W)
  | 0, _, _, _, _, _, _, _ => trivial
  | (d + 1), _, _, _, hA, hW0, hWge, hWU => Att_close hA hW0 hWge hWU

theorem mlift_raw {u : ℕ} {Z : TrioSeq} (hZ : Z ∈ Wg (2 * u)) (s t : ℕ) :
    mlift (shiftr01 s 0 Z) u t = shiftr01 s 0 Z := by
  have := mlift_append_low (A := []) (low_of_Wg hZ s le_rfl) t
  simpa [mlift_nil] using this

theorem PathCone_anc {w D : ℕ} {A B : TrioSeq} (hPC : PathCone w D A)
    (hB0 : B ≠ [] → entry B 0 0 = D + 1) {k b : ℕ} (hk : k < A.length) (hb : b < B.length)
    (h : Relation.ReflTransGen (nextrel0 (A ++ B)) k (A.length + b)) : w < entry A 1 k := by
  have hBne : B ≠ [] := by intro hh; rw [hh] at hb; simp at hb
  refine hPC k hk (fun k' hk1 hk2 => ?_) ?_
  · have := rtg0_rec h k' hk1 (by omega)
    rwa [Small.entry_append_left hk, Small.entry_append_left hk2] at this
  · have := rtg0_rec h A.length hk (by omega)
    rw [Small.entry_append_left hk, show A.length = A.length + 0 from rfl, entry_append_right,
      hB0 hBne] at this
    omega

theorem noParent_ctx {A B : TrioSeq} {b j : ℕ} (hb : b < B.length)
    (hpre : ∀ k, k < A.length →
      Relation.ReflTransGen (nextrel0 (A ++ B)) k (A.length + b) → j ≤ entry A 1 k)
    (hlast : entry B 1 b = j) (hnp : ¬ hasParent B 1 b) :
    ¬ hasParent (A ++ B) 1 (A.length + b) := by
  rintro ⟨k, hk, -⟩
  by_cases hkA : A.length ≤ k
  · obtain ⟨q, rfl⟩ : ∃ q, k = A.length + q := ⟨k - A.length, by omega⟩
    have h1 := (nextR_append_right A B 1 q b).1 hk
    have h3 : nextrel1 B q b := by
      unfold nextR at h1; rwa [if_neg (by omega), if_pos rfl] at h1
    exact hnp (H12Export.hasParent1_of_le0_witness hb h3.2.2.2.2.1.2.2 h3.2.2.2.1)
  · have hk' : nextrel1 (A ++ B) k (A.length + b) := by
      unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
    obtain ⟨-, -, -, hk1, hle0, -⟩ := hk'
    have hkA' : k < A.length := by omega
    have := hpre k hkA' hle0.2.2
    rw [Small.entry_append_left hkA', entry_append_right, hlast] at hk1
    omega

#print axioms Att_close


/-! ## 開いた単位の下の荷 -/

theorem LoadUnder {d u : ℕ} {P : TrioSeq} (hR : RootP d u P) (hU : UnitOKp (Att d) d u P) :
    ∀ Z ∈ Wg (2 * u), based Z → UnitOKp (Att d) d u (P ++ shiftr01 (d + 2) 0 Z) := by
  have key : Wg (2 * u) ⊆ {Z : TrioSeq | Z ∈ Wg (2 * u) ∧
      (based Z → UnitOKp (Att d) d u (P ++ shiftr01 (d + 2) 0 Z))} := by
    refine A2g' ?_
    intro Z hA
    have hZW : Z ∈ Wg (2 * u) := A1g_intro (Aopg_mono_X hA (fun U hU => hU.1))
    refine ⟨hZW, ?_⟩
    intro hb
    have hb0 : entry Z 0 0 = 0 := hb
    by_cases hZnil : Z = []
    · subst hZnil; simpa [shiftr01] using hU
    have hZlen : 0 < Z.length := List.length_pos_iff.mpr hZnil
    set c := Z.getLast hZnil with hc
    have hsplit : Z = Z.dropLast ++ [c] := (List.dropLast_append_getLast hZnil).symm
    have hclast : ∀ r, entry Z r (Z.length - 1) = entry [c] r 0 := by
      intro r
      have h := entry_append_right Z.dropLast [c] r 0
      rw [← hsplit] at h
      rw [show Z.length - 1 = Z.dropLast.length + 0 by simp]
      exact h
    have hlev0 : lev Z (Z.length - 1) = 0 → c.2.1 = 0 ∧ c.2.2 = 0 := by
      intro hz
      unfold lev at hz
      rw [hclast 1, hclast 2] at hz
      have e1 : entry [c] 1 0 = c.2.1 := rfl
      have e2 : entry [c] 2 0 = c.2.2 := rfl
      rw [e1, e2] at hz
      omega
    have hc10 : Z.length = 1 → c.1 = 0 := by
      intro hZ1
      have : entry Z 0 (Z.length - 1) = c.1 := hclast 0
      rw [show Z.length - 1 = 0 by omega, hb0] at this; omega
    have hdlW : Z.dropLast ∈ Wg (2 * u) := Wg_dropLast hZW
    -- 根の高さの平らな列: P の部分木の複写
    have hflat : c.2.1 = 0 → c.2.2 = 0 → c.1 = 0 →
        UnitOKp (Att d) d u (P ++ shiftr01 (d + 2) 0 Z.dropLast) →
        UnitOKp (Att d) d u (P ++ shiftr01 (d + 2) 0 Z) := by
      intro h1 h2 h0 hIHd u' hu' Y hge hAY hPC hG
      have hceq : c = ((0, 0, 0) : ℕ × ℕ × ℕ) := Prod.ext h0 (Prod.ext h1 h2)
      have hQR : RootP d u' (mlift P u (u' - u)) := RootP_lift hR hu'
      have hQlen : 0 < (mlift P u (u' - u)).length := List.length_pos_iff.mpr hQR.1
      obtain ⟨M, hM⟩ : ∃ M, M = mlift P u (u' - u) ++ shiftr01 (d + 2) 0 Z.dropLast := ⟨_, rfl⟩
      have eMl : mlift (P ++ shiftr01 (d + 2) 0 Z.dropLast) u (u' - u) = M := by
        rw [mlift_append_low (low_of_Wg hdlW (d + 2) le_rfl), hM]
      have eC : mlift (P ++ shiftr01 (d + 2) 0 Z) u (u' - u)
          = M ++ [((d + 2, 0, 0) : ℕ × ℕ × ℕ)] := by
        rw [mlift_append_low (low_of_Wg hZW (d + 2) le_rfl), hM]
        conv_lhs => rw [hsplit, hceq]
        rw [shiftr01_append0, shift_col, Nat.zero_add, List.append_assoc]
      have hMne : M ≠ [] := by simp [hM, hQR.1]
      have hM0 : entry M 0 0 = d + 1 := by
        rw [hM, Small.entry_append_left hQlen]; exact hQR.2.1
      have hMge : ∀ x ∈ M, d + 1 ≤ x.1 := by
        intro x hx
        rw [hM] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact RootP_ge hQR x hx
        · simp only [shiftr01, List.mem_map] at hx
          obtain ⟨p, -, rfl⟩ := hx
          dsimp only; omega
      have hMtail : ∀ r, 1 ≤ r → r < M.length → d + 2 ≤ entry M 0 r := by
        intro r hr1 hr2
        rcases Nat.lt_or_ge r (mlift P u (u' - u)).length with hlt | hge2
        · rw [hM, Small.entry_append_left hlt]; exact hQR.2.2.2 r hr1 hlt
        · obtain ⟨k, rfl⟩ : ∃ k, r = (mlift P u (u' - u)).length + k :=
            ⟨r - (mlift P u (u' - u)).length, by omega⟩
          have hk : k < Z.dropLast.length := by
            rw [hM, List.length_append, shiftr01_length] at hr2; omega
          rw [hM, entry_append_right, entry0_shiftr01 hk]
          omega
      have hUM : UnitOKp (Att d) d u' M := by
        have := UnitOKp_lift hIHd hu'
        rwa [eMl] at this
      rw [eC, ← List.append_assoc]
      have hrep : ∀ n, (∀ y ∈ Y ++ (List.range n).flatMap (fun _ => M), 1 ≤ y.1) ∧
          Att d u' (Y ++ (List.range n).flatMap (fun _ => M)) ∧
          PathCone u' d (Y ++ (List.range n).flatMap (fun _ => M)) ∧
          GTall u' (Y ++ (List.range n).flatMap (fun _ => M)) := by
        intro n
        induction n with
        | zero =>
            simp only [List.range_zero, List.flatMap_nil, List.append_nil]
            exact ⟨hge, hAY, hPC, hG⟩
        | succ n ih =>
            obtain ⟨g1, g2, g3, g4⟩ := ih
            have e : Y ++ (List.range (n + 1)).flatMap (fun _ => M)
                = (Y ++ (List.range n).flatMap (fun _ => M)) ++ M := by
              rw [List.range_succ, List.flatMap_append]; simp [List.append_assoc]
            rw [e]
            refine ⟨?_, Att_extend d g2 (fun _ => hM0) hMge hUM, PathCone_append hMge g3, ?_⟩
            · intro y hy
              rcases List.mem_append.mp hy with hy | hy
              · exact g1 y hy
              · have := hMge y hy; omega
            · have := hUM u' le_rfl _ g1 g2 g3 g4
              rwa [Nat.sub_self, mlift_zero] at this
      have hlenC : 2 ≤ (Y ++ M ++ [((d + 2, 0, 0) : ℕ × ℕ × ℕ)]).length := by
        have : 0 < M.length := List.length_pos_iff.mpr hMne
        simp; omega
      have hidx : (Y ++ M ++ [((d + 2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1 = (Y ++ M).length + 0 := by
        simp
      have eL : ∀ r, entry (Y ++ M ++ [((d + 2, 0, 0) : ℕ × ℕ × ℕ)]) r
          ((Y ++ M ++ [((d + 2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1)
          = entry [((d + 2, 0, 0) : ℕ × ℕ × ℕ)] r 0 := by
        intro r; rw [hidx, entry_append_right]
      have hsr : srow (Y ++ M ++ [((d + 2, 0, 0) : ℕ × ℕ × ℕ)])
          ((Y ++ M ++ [((d + 2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) = 0 := by
        unfold srow; rw [eL, eL]; rfl
      have hpC : hasParent (Y ++ M ++ [((d + 2, 0, 0) : ℕ × ℕ × ℕ)])
          (srow (Y ++ M ++ [((d + 2, 0, 0) : ℕ × ℕ × ℕ)])
            ((Y ++ M ++ [((d + 2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1))
          ((Y ++ M ++ [((d + 2, 0, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
        rw [hsr]
        have hML : 0 < M.length := List.length_pos_iff.mpr hMne
        refine (hasParent_zero_iff (by omega)).mpr ⟨Y.length, by simp; omega, ?_⟩
        rw [eL, Small.entry_append_left (show Y.length < (Y ++ M).length by simp; omega),
          show Y.length = Y.length + 0 from rfl, entry_append_right, hM0]
        show d + 1 < d + 2; omega
      refine GTall_oper hlenC hpC (fun n _ => ?_)
      rw [oper_snoc00'' Y hMne (by rw [hM0]; omega) hMtail n]
      exact (hrep n).2.2.2
    -- 荷の中に親がある列
    have hoper : 2 ≤ Z.length → hasParent Z (srow Z (Z.length - 1)) (Z.length - 1) →
        (∀ n, 1 ≤ n → UnitOKp (Att d) d u (P ++ shiftr01 (d + 2) 0 (Z⟦n⟧)) ∧
          Z⟦n⟧ ∈ Wg (2 * u)) →
        UnitOKp (Att d) d u (P ++ shiftr01 (d + 2) 0 Z) := by
      intro hlen2 hp hIH u' hu' Y hge hAY hPC hG
      rw [mlift_append_low (low_of_Wg hZW (d + 2) le_rfl), ← List.append_assoc]
      have hlenC : 2 ≤ (Y ++ mlift P u (u' - u) ++ shiftr01 (d + 2) 0 Z).length := by
        simp [shiftr01]; omega
      have hidx : (Y ++ mlift P u (u' - u) ++ shiftr01 (d + 2) 0 Z).length - 1
          = (Y ++ mlift P u (u' - u)).length + (Z.length - 1) := by
        simp [shiftr01]; omega
      have hpC : hasParent (Y ++ mlift P u (u' - u) ++ shiftr01 (d + 2) 0 Z)
          (srow (Y ++ mlift P u (u' - u) ++ shiftr01 (d + 2) 0 Z)
            ((Y ++ mlift P u (u' - u) ++ shiftr01 (d + 2) 0 Z).length - 1))
          ((Y ++ mlift P u (u' - u) ++ shiftr01 (d + 2) 0 Z).length - 1) := by
        rw [hidx, srow_append_right, srow_shiftr01]
        exact hasParent_append_right_of _ _ (hasParent_shiftr01.mpr hp)
      refine GTall_oper hlenC hpC (fun n hn => ?_)
      rw [oper_shift (Y ++ mlift P u (u' - u)) Z (d + 2) n hlen2 hp]
      obtain ⟨hIHn, hWn⟩ := hIH n hn
      have := hIHn u' hu' Y hge hAY hPC hG
      rwa [mlift_append_low (low_of_Wg hWn (d + 2) le_rfl), ← List.append_assoc] at this
    -- 孤児
    have horph : ∀ m', m' < 2 * u → domT Z m' → entry Z 2 (Z.length - 1) = 0 →
        (∀ z ∈ Wg m', based z → graft Z z ∈ Wg (2 * u) ∧
          (based (graft Z z) → UnitOKp (Att d) d u (P ++ shiftr01 (d + 2) 0 (graft Z z)))) →
        UnitOKp (Att d) d u (P ++ shiftr01 (d + 2) 0 Z) := by
      intro m' hm hd h20 hgr u' hu' Y hge hAY hPC hG
      have hlev := hd.1
      unfold lev at hlev
      have hj1 : 1 ≤ entry Z 1 (Z.length - 1) := by omega
      have hjv : entry Z 1 (Z.length - 1) ≤ u := by omega
      have hm' : m' = 2 * entry Z 1 (Z.length - 1) - 1 := by omega
      subst hm'
      have hsr : srow Z (Z.length - 1) = 1 := by
        unfold srow; rw [if_neg (by omega), if_pos (by omega)]
      have hnp : ¬ hasParent Z 1 (Z.length - 1) := fun hh => hd.2 (by rw [hsr]; exact hh)
      have hc1' : c.2.1 = entry Z 1 (Z.length - 1) := (hclast 1).symm
      have hc20 : c.2.2 = 0 := by have := hclast 2; rw [h20] at this; exact this.symm
      generalize hjdef : entry Z 1 (Z.length - 1) = j at hj1 hjv hc1' hgr hnp
      have hQR : RootP d u' (mlift P u (u' - u)) := RootP_lift hR hu'
      rw [mlift_append_low (low_of_Wg hZW (d + 2) le_rfl), ← List.append_assoc]
      have eZ : shiftr01 (d + 2) 0 Z
          = shiftr01 (d + 2) 0 Z.dropLast ++ [((c.1 + (d + 2), j, 0) : ℕ × ℕ × ℕ)] := by
        have hcj : c = ((c.1, j, 0) : ℕ × ℕ × ℕ) := Prod.ext rfl (Prod.ext hc1' hc20)
        conv_lhs => rw [hsplit, hcj]
        rw [shiftr01_append0, shift_col]
      have hb' : Z.length - 1 < (shiftr01 (d + 2) 0 Z).length := by
        rw [shiftr01_length]; omega
      have hNP := noParent_ctx (A := Y ++ mlift P u (u' - u)) (B := shiftr01 (d + 2) 0 Z)
        (b := Z.length - 1) (j := j) hb'
        (fun k hk hrt => by
          have := PathCone_anc (PathCone_open hPC hQR) (B := shiftr01 (d + 2) 0 Z)
            (fun _ => by rw [entry0_shiftr01 hZlen, hb0]; omega) hk hb' hrt
          omega)
        (by rw [entry1_shiftr01]; exact hjdef)
        (fun hh => hnp (hasParent_shiftr01.mp hh))
      have eIdx : ((Y ++ mlift P u (u' - u)) ++ shiftr01 (d + 2) 0 Z).length - 1
          = (Y ++ mlift P u (u' - u)).length + (Z.length - 1) := by
        simp [shiftr01]; omega
      rw [eZ, ← List.append_assoc]
      refine GTall_orph hj1 (le_trans hjv hu') ?_ (fun z hz hbz => ?_)
      · rw [List.append_assoc, ← eZ, eIdx]; exact hNP
      · obtain ⟨hgW, hgU⟩ := hgr z hz hbz
        have h := hgU (based_graft_arg hZnil hb hbz) u' hu' Y hge hAY hPC hG
        have e : graft Z z = Z.dropLast ++ shiftr01 c.1 0 z := by
          rw [graft_eq_shift, hclast 0]; rfl
        rw [mlift_append_low (low_of_Wg hgW (d + 2) le_rfl), e, shiftr01_append0, shiftr01_add0,
          ← List.append_assoc, ← List.append_assoc] at h
        exact h
    rcases hA with ⟨hl, hw0⟩ | ⟨hnat, hop⟩ | ⟨m', hm, hd, h20, hgr⟩
    · have hZ1 : Z.length = 1 := by omega
      have hz : lev Z (Z.length - 1) = 0 := by rw [hZ1]; exact hw0
      have hdl : Z.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
      exact hflat (hlev0 hz).1 (hlev0 hz).2 (hc10 hZ1) (by rw [hdl]; simpa [shiftr01] using hU)
    · by_cases hp : 2 ≤ Z.length ∧ hasParent Z (srow Z (Z.length - 1)) (Z.length - 1)
      · exact hoper hp.1 hp.2 (fun n hn => ⟨(hop n hn).2 (based_oper hn hb), (hop n hn).1⟩)
      · have hlev : lev Z (Z.length - 1) = 0 := by
          rcases natDom_iff.mp hnat with h | h
          · exact h
          · exfalso
            have hZ1 : Z.length = 1 := by
              by_contra hne; exact hp ⟨by omega, h⟩
            rw [hZ1] at h
            obtain ⟨j0, hj0, -⟩ := h
            exact absurd (nextR_index_lt hj0) (Nat.not_lt_zero j0)
        obtain ⟨h1, h2⟩ := hlev0 hlev
        have hsr0 : srow Z (Z.length - 1) = 0 := by
          unfold srow; rw [hclast 1, hclast 2]
          show (if 0 < c.2.2 then 2 else if 0 < c.2.1 then 1 else 0) = 0
          simp [h1, h2]
        by_cases hZ1 : Z.length = 1
        · have hdl : Z.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
          exact hflat h1 h2 (hc10 hZ1) (by rw [hdl]; simpa [shiftr01] using hU)
        · have h0 : c.1 = 0 := by
            by_contra hne
            have hc10' : entry Z 0 (Z.length - 1) = c.1 := hclast 0
            exact hp ⟨by omega, by
              rw [hsr0]
              exact (hasParent_zero_iff (by omega)).mpr ⟨0, by omega, by rw [hb0, hc10']; omega⟩⟩
          have h1' := (hop 1 le_rfl).2 (based_oper le_rfl hb)
          rw [oper_one_eq_dropLast (by omega)] at h1'
          exact hflat h1 h2 h0 h1'
    · exact horph m' hm hd h20 (fun z hz hbz => hgr z hz hbz)
  intro Z hZ hb
  exact (key hZ).2 hb

#print axioms LoadUnder


/-! ## 単位の規則 -/

theorem SC_nil (d u : ℕ) : SC d u [] := by
  intro u' _ Y _ _ _ hG
  simpa [shiftr01, mlift_nil] using hG

theorem SC_load (d : ℕ) {u : ℕ} {Z : TrioSeq} (hZ : Z ∈ Wg (2 * u)) (hb : based Z) :
    SC d u (shiftr01 1 0 Z) := by
  intro u' hu' Y hge hAY hPC hG
  have e : shiftr01 d 0 (shiftr01 1 0 Z) = shiftr01 (d + 1) 0 Z := by
    rw [shiftr01_add0, Nat.add_comm 1 d]
  rw [e, mlift_raw hZ]
  have hZ' : Z ∈ Wg (2 * u') := Wg_mono (by omega) hZ
  cases d with
  | zero => simpa using GTall_loadTop hge hG hZ' hb
  | succ d =>
      obtain ⟨Y', P, rfl, hA', hG', hge', hPC', hR, hU⟩ := hAY
      have h := LoadUnder hR hU Z hZ' hb u' le_rfl Y' hge' hA' hPC' hG'
      rw [Nat.sub_self, mlift_zero, ← List.append_assoc] at h
      exact h

theorem tie_ctx {d u : ℕ} {Y : TrioSeq} (hge : ∀ y ∈ Y, 1 ≤ y.1) (hAY : Att d u Y)
    (hPC : PathCone u d Y) (hG : GTall u Y) :
    GTall u (Y ++ [((d + 1, u + 1, 0) : ℕ × ℕ × ℕ)]) := by
  refine GTall_tie (x := d + 1) ?_ (fun u'' hu'' Z hZ hbZ => ?_)
  · have h := (coneV_pathB (B := [((d + 1, u + 1, 0) : ℕ × ℕ × ℕ)]) hPC (fun _ => rfl)
      (i := 0) (by simp)).mpr (by
        intro y hy
        have := rtg0_le hy
        have hy0 : y = 0 := by omega
        subst hy0; show u < u + 1; omega)
    simpa using h
  · have h := SC_load d (u := u'') hZ hbZ u'' le_rfl (mlift Y u (u'' - u))
      (mlift_row0 hge u (u'' - u)) (Att_lift d hAY hu'') (PathCone_lift hPC hu'')
      (GTall_lift hG hu'')
    rw [Nat.sub_self, mlift_zero] at h
    have e3 : shiftr01 d 0 (shiftr01 1 0 Z) = shiftr01 (d + 1) 0 Z := by
      rw [shiftr01_add0, Nat.add_comm 1 d]
    rwa [e3] at h

theorem mlift_tie (d u t : ℕ) :
    mlift [((d + 1, u + 1, 0) : ℕ × ℕ × ℕ)] u t = [((d + 1, u + t + 1, 0) : ℕ × ℕ × ℕ)] := by
  have hc0 : coneV ([] ++ [((d + 1, u + 1, 0) : ℕ × ℕ × ℕ)]) u ([] : TrioSeq).length := by
    intro y hy
    have := rtg0_le hy
    have hy0 : y = 0 := by simp at this; omega
    subst hy0; show u < u + 1; omega
  have := mlift_snoc_cone [] ((d + 1, u + 1, 0) : ℕ × ℕ × ℕ) hc0 t
  simp only [List.nil_append, mlift_nil] at this
  rw [this]
  show [((d + 1, u + 1 + t, 0) : ℕ × ℕ × ℕ)] = _
  rw [show u + 1 + t = u + t + 1 by omega]

theorem SC_tie (d u : ℕ) : SC d u [((1, u + 1, 0) : ℕ × ℕ × ℕ)] := by
  intro u' hu' Y hge hAY hPC hG
  have e1 : shiftr01 d 0 [((1, u + 1, 0) : ℕ × ℕ × ℕ)] = [((d + 1, u + 1, 0) : ℕ × ℕ × ℕ)] := by
    rw [shift_col, Nat.add_comm 1 d]
  rw [e1, mlift_tie, show u + (u' - u) + 1 = u' + 1 by omega]
  exact tie_ctx hge hAY hPC hG

theorem SC_child {d u : ℕ} {C : TrioSeq} (hC : SC (d + 1) u C)
    (hC0 : C ≠ [] → entry C 0 0 = 1) :
    SC d u (((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 C) := by
  intro u' hu' Y hge hAY hPC hG
  have e1 : shiftr01 d 0 (((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 C)
      = [((d + 1, u + 1, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 (d + 1) 0 C := by
    rw [show ((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 C
        = [((1, u + 1, 0) : ℕ × ℕ × ℕ)] ++ shiftr01 1 0 C from rfl,
      shiftr01_append0, shift_col, shiftr01_add0, Nat.add_comm 1 d]
  have hRT : RootP d u [((d + 1, u + 1, 0) : ℕ × ℕ × ℕ)] :=
    ⟨by simp, rfl, by show u < u + 1; omega, fun i h1 h2 => by simp at h2; omega⟩
  have hB0 : shiftr01 (d + 1) 0 C ≠ [] → entry (shiftr01 (d + 1) 0 C) 0 0 = d + 1 + 1 := by
    intro hne
    have hCne : C ≠ [] := by intro h; apply hne; subst h; rfl
    rw [entry0_shiftr01 (List.length_pos_iff.mpr hCne), hC0 hCne]; omega
  rw [e1, mlift_pathB (PathCone_root hRT) hB0, mlift_tie, mlift_shift0,
    show u + (u' - u) + 1 = u' + 1 by omega, ← List.append_assoc]
  have hT := tie_ctx hge hAY hPC hG
  have hRT' : RootP d u' [((d + 1, u' + 1, 0) : ℕ × ℕ × ℕ)] :=
    ⟨by simp, rfl, by show u' < u' + 1; omega, fun i h1 h2 => by simp at h2; omega⟩
  have hUT : UnitOKp (Att d) d u' [((d + 1, u' + 1, 0) : ℕ × ℕ × ℕ)] := by
    intro u'' hu'' Y2 hge2 hA2 hPC2 hG2
    rw [mlift_tie, show u' + (u'' - u') + 1 = u'' + 1 by omega]
    exact tie_ctx hge2 hA2 hPC2 hG2
  have hA2 : Att (d + 1) u' (Y ++ [((d + 1, u' + 1, 0) : ℕ × ℕ × ℕ)]) :=
    ⟨Y, _, rfl, hAY, hG, hge, hPC, hRT', hUT⟩
  have hge2 : ∀ y ∈ Y ++ [((d + 1, u' + 1, 0) : ℕ × ℕ × ℕ)], 1 ≤ y.1 := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hge y hy
    · simp at hy; subst hy; show 1 ≤ d + 1; omega
  have h := hC u' hu' _ hge2 hA2 (PathCone_open hPC hRT') hT
  rwa [mlift_shift0] at h

theorem SC_seq {d u : ℕ} {U V : TrioSeq} (hU : SC d u U) (hV : SC d u V)
    (hU0 : U ≠ [] → entry U 0 0 = 1) (hUge : ∀ x ∈ U, 1 ≤ x.1)
    (hV0 : V ≠ [] → entry V 0 0 = 1) : SC d u (U ++ V) := by
  intro u' hu' Y hge hAY hPC hG
  have hrs : ∀ x ∈ shiftr01 d 0 U, entry (shiftr01 d 0 V) 0 0 ≤ x.1 := by
    intro x hx
    simp only [shiftr01, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have := hUge p hp
    by_cases hVn : V = []
    · subst hVn; simp [shiftr01, entry]
    · rw [entry0_shiftr01 (List.length_pos_iff.mpr hVn), hV0 hVn]; dsimp only; omega
  rw [shiftr01_append0, mlift_append hrs, ← List.append_assoc]
  have h1 := hU u' hu' Y hge hAY hPC hG
  have hWge : ∀ x ∈ mlift (shiftr01 d 0 U) u (u' - u), d + 1 ≤ x.1 := by
    refine mlift_row0 (fun x hx => ?_) u (u' - u)
    simp only [shiftr01, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have := hUge p hp; dsimp only; omega
  have hW0 : mlift (shiftr01 d 0 U) u (u' - u) ≠ [] →
      entry (mlift (shiftr01 d 0 U) u (u' - u)) 0 0 = d + 1 := by
    intro hne
    have hUne : U ≠ [] := by intro h; apply hne; subst h; simp [shiftr01, mlift_nil]
    have hl : 0 < (shiftr01 d 0 U).length := by
      rw [shiftr01_length]; exact List.length_pos_iff.mpr hUne
    show ((mlift (shiftr01 d 0 U) u (u' - u)).getD 0 (0, 0, 0)).1 = d + 1
    rw [mlift_getD hl]
    show entry (shiftr01 d 0 U) 0 0 = d + 1
    rw [entry0_shiftr01 (List.length_pos_iff.mpr hUne), hU0 hUne]; omega
  have hA2 := Att_extend d hAY hW0 hWge (UnitOKp_lift hU hu')
  have hge2 : ∀ y ∈ Y ++ mlift (shiftr01 d 0 U) u (u' - u), 1 ≤ y.1 := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hge y hy
    · have := hWge y hy; omega
  exact hV u' hu' _ hge2 hA2 (PathCone_append hWge hPC) h1

/-! ## 森と語 -/

def Forest (U : TrioSeq) : Prop := (U ≠ [] → entry U 0 0 = 1) ∧ ∀ x ∈ U, 1 ≤ x.1

def SCF (d u : ℕ) (U : TrioSeq) : Prop := SC d u U ∧ Forest U

theorem SCF_nil (d u : ℕ) : SCF d u [] :=
  ⟨SC_nil d u, fun h => absurd rfl h, fun _ h => by simp at h⟩

theorem SCF_load (d : ℕ) {u : ℕ} {Z : TrioSeq} (hZ : Z ∈ Wg (2 * u)) (hb : based Z) :
    SCF d u (shiftr01 1 0 Z) := by
  refine ⟨SC_load d hZ hb, fun hne => ?_, fun x hx => ?_⟩
  · have hZne : Z ≠ [] := by intro h; apply hne; subst h; rfl
    rw [entry0_shiftr01 (List.length_pos_iff.mpr hZne)]
    have : entry Z 0 0 = 0 := hb
    omega
  · simp only [shiftr01, List.mem_map] at hx
    obtain ⟨p, -, rfl⟩ := hx
    dsimp only; omega

theorem SCF_child {d u : ℕ} {C : TrioSeq} (hC : SCF (d + 1) u C) :
    SCF d u (((1, u + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 C) := by
  refine ⟨SC_child hC.1 hC.2.1, fun _ => rfl, fun x hx => ?_⟩
  simp only [List.mem_cons, shiftr01, List.mem_map] at hx
  rcases hx with rfl | ⟨p, -, rfl⟩
  · show 1 ≤ 1; omega
  · dsimp only; omega

theorem SCF_seq {d u : ℕ} {U V : TrioSeq} (hU : SCF d u U) (hV : SCF d u V) :
    SCF d u (U ++ V) := by
  refine ⟨SC_seq hU.1 hV.1 hU.2.1 hU.2.2 hV.2.1, fun hne => ?_, fun x hx => ?_⟩
  · by_cases hUn : U = []
    · subst hUn; simpa using hV.2.1 (by simpa using hne)
    · rw [Small.entry_append_left (List.length_pos_iff.mpr hUn)]; exact hU.2.1 hUn
  · rcases List.mem_append.mp hx with hx | hx
    · exact hU.2.2 x hx
    · exact hV.2.2 x hx

theorem GTall_of_SCF0 {u : ℕ} {K : TrioSeq} (h : SCF 0 u K) : GTall u K := by
  have := h.1 u le_rfl [] (fun _ h => by simp at h) trivial (fun y hy => by simp at hy)
    (GTall_nil u)
  rw [Nat.sub_self, mlift_zero, List.nil_append] at this
  have e : shiftr01 0 0 K = K := by simp [shiftr01]
  rwa [e] at this

theorem GT_of_SCF0 {u : ℕ} {K : TrioSeq} (h : SCF 0 u K) : GT u K :=
  GT_of_GTall (GTall_of_SCF0 h)

def WordsG (v : ℕ) (Ls : List TrioSeq) : Prop := ∀ K ∈ Ls, GT v K ∧ ∀ y ∈ K, 1 ≤ y.1

theorem WordsG_nil (v : ℕ) : WordsG v [] := fun _ h => by simp at h

theorem WordsG_cons {v : ℕ} {K : TrioSeq} {Ls : List TrioSeq} (h1 : SCF 0 v K)
    (h2 : WordsG v Ls) : WordsG v (K :: Ls) := by
  intro K' h
  simp only [List.mem_cons] at h
  rcases h with rfl | h
  · exact ⟨GT_of_SCF0 h1, h1.2.2⟩
  · exact h2 K' h

theorem BwT_wordsG {v : ℕ} : ∀ (Ls : List TrioSeq), WordsG v Ls → BwT v Ls := by
  intro Ls
  induction Ls using List.reverseRecOn with
  | nil => intro _; exact BwT_nil v
  | append_singleton Ls K ih =>
      intro hW
      have hK := hW K (by simp)
      exact hK.1 Ls (fun X hX => (hW X (List.mem_append_left _ hX)).2)
        (ih (fun X hX => hW X (List.mem_append_left _ hX)))

theorem starOK_wordsG {v : ℕ} {Ls : List TrioSeq} (h : WordsG v Ls) :
    StarOK v (rword 0 v Ls) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hB := BwT_wordsG Ls h v le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

/-- 行 612 の試し。 -/
theorem R612_mem : ([(0, 0, 0), (1, 1, 1), (2, 1, 0), (3, 0, 0)] : TrioSeq) ∈ W 0 := by
  have h := GxB.Wg0_sub_W0 (Wg_of_starOK (starOK_wordsG (v := 0)
    (WordsG_cons (SCF_seq (SCF_child (d := 0) (u := 0)
      (SCF_seq (SCF_load 1 (Om_mem_Wg 0) rfl) (SCF_nil 1 0))) (SCF_nil 0 0))
      (WordsG_nil 0))))
  simpa [shiftr01, rword, rcol] using h

#print axioms R612_mem

end GxN
end TRIO
