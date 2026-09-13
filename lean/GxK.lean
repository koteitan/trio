/-
GxK.lean: 中身の閉包 `GT v K`（どの語 L の後にも中身 K の字を足せる）とその規則。

    GT v K := ∀ L, BwT v L → BwT v (L ++ [K])

規則は中身の最後の列の展開の場合分けに対応する。
- `GT_nil`   : 空の中身（z の字の崩壊）。
- `GT_oper`  : 中身の中に親がある（`slift_oper` で持ち上げと展開が交換する）。
- `GT_flat`  : 頭の直上の平らな列 `(x,0,0)`（字の複写）。
- `GT_orph`  : 行 1 が段以下の孤児（接ぎ木）。
-/
import GxJ
import Aexp
import Gamma

namespace TRIO
namespace GxK

open Wset
open Small
open GwS
open Gw
open GwU
open GwZ
open GxD
open GxG
open GxJ

def GT (v : ℕ) (K : TrioSeq) : Prop :=
  ∀ L : List TrioSeq, (∀ X ∈ L, ∀ x ∈ X, 1 ≤ x.1) → BwT v L → BwT v (L ++ [K])

def GTall (v : ℕ) (K : TrioSeq) : Prop := ∀ u, v ≤ u → GT u (mlift K v (u - v))

theorem BwT_lift {v : ℕ} {L : List TrioSeq} (hB : BwT v L) {u : ℕ} (hu : v ≤ u) :
    BwT u (L.map (fun X => mlift X v (u - v))) := by
  intro u' hu'
  rw [List.map_map]
  have e : ((fun X => mlift X u (u' - u)) ∘ fun X => mlift X v (u - v))
      = (fun X => mlift X v (u' - v)) := by
    funext X
    simp only [Function.comp_apply]
    have := mlift_mlift X v (u - v) (u' - u)
    rw [show v + (u - v) = u by omega, show u - v + (u' - u) = u' - v by omega] at this
    exact this
  rw [e]
  exact hB u' (le_trans hu hu')

theorem GT_nil (v : ℕ) : GT v [] := fun _ hL hB => BwT_snocz hL hB

/-! ## 中身の中に親がある列 -/

theorem GT_oper {v : ℕ} {K : TrioSeq} (hlen : 2 ≤ K.length)
    (hp : hasParent K (srow K (K.length - 1)) (K.length - 1))
    (hIH : ∀ n, 1 ≤ n → GT v (K⟦n⟧)) : GT v K := by
  intro L hL hB u hu _ a ha
  have hS := stair_step v (u - v)
  have eK : mlift K v (u - v) = slift K (fun m => m + (if v < m then (u - v) else 0)) :=
    mlift_eq_slift K v (u - v)
  rw [List.map_append, List.map_singleton, rword0_snoc]
  have hlen' : 2 ≤ (mlift K v (u - v)).length := by rw [mlift_length]; exact hlen
  have hp' : hasParent (mlift K v (u - v))
      (srow (mlift K v (u - v)) ((mlift K v (u - v)).length - 1))
      ((mlift K v (u - v)).length - 1) := by
    rw [mlift_length, eK, hasParent_slift hS, srow_slift hS (by omega)]
    exact hp
  refine A1g_intro (Or.inr (Or.inl ⟨natDom_append_shift _ _ 1
    (by intro h; rw [h] at hlen'; simp at hlen') hp', fun n hn => ?_⟩))
  rw [oper_shift _ _ 1 n hlen' hp']
  have e2 : (mlift K v (u - v))⟦n⟧ = mlift (K⟦n⟧) v (u - v) := by
    rw [eK, mlift_eq_slift, slift_oper hS]
  rw [e2]
  have h := hIH n hn L hL hB u hu (argOK_rword u _) a ha
  rw [List.map_append, List.map_singleton, rword0_snoc] at h
  exact h

/-! ## 頭の直上の平らな列 -/

open Classical in
theorem mlift_snoc_flat (K : TrioSeq) (x v t : ℕ) (hx : ∀ y ∈ K, x ≤ y.1) :
    mlift (K ++ [((x, 0, 0) : ℕ × ℕ × ℕ)]) v t = mlift K v t ++ [((x, 0, 0) : ℕ × ℕ × ℕ)] := by
  rw [mlift_append (fun y hy => by show x ≤ y.1; exact hx y hy)]
  congr 1
  have hc : ¬ coneV [((x, 0, 0) : ℕ × ℕ × ℕ)] v 0 := fun h => by
    have := h 0 Relation.ReflTransGen.refl
    simp [entry] at this
  simp only [mlift, List.length_singleton, List.range_one, List.map_cons, List.map_nil]
  rw [if_neg hc]
  rfl

theorem mlift_row0 {K : TrioSeq} {x : ℕ} (hx : ∀ y ∈ K, x ≤ y.1) (v t : ℕ) :
    ∀ y ∈ mlift K v t, x ≤ y.1 := by
  intro y hy
  simp only [mlift, List.mem_map, List.mem_range] at hy
  obtain ⟨j, hj, rfl⟩ := hy
  show x ≤ entry K 0 j
  have hmem : K.getD j (0, 0, 0) ∈ K := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
  exact hx _ hmem

theorem BwT_rep {v : ℕ} {K : TrioSeq} (hK : ∀ x ∈ K, 1 ≤ x.1) (hG : GT v K)
    {L : List TrioSeq} (hL : ∀ X ∈ L, ∀ x ∈ X, 1 ≤ x.1) (hB : BwT v L) :
    ∀ n, BwT v (L ++ List.replicate n K)
  | 0 => by simpa using hB
  | (n + 1) => by
      have hLn : ∀ X ∈ L ++ List.replicate n K, ∀ x ∈ X, 1 ≤ x.1 := by
        intro X hX
        rcases List.mem_append.mp hX with hX | hX
        · exact hL X hX
        · rw [List.eq_of_mem_replicate hX]; exact hK
      have h := hG _ hLn (BwT_rep hK hG hL hB n)
      rwa [List.append_assoc, ← List.replicate_succ'] at h

theorem GT_flat {v : ℕ} {K : TrioSeq} {x : ℕ} (hx : 1 ≤ x) (hK : ∀ y ∈ K, 1 ≤ y.1)
    (hKx : ∀ y ∈ K, x ≤ y.1) (hG : GT v K) : GT v (K ++ [((x, 0, 0) : ℕ × ℕ × ℕ)]) := by
  intro L hL hB u hu _ a ha
  have hTx : ∀ y ∈ mlift K v (u - v), x ≤ y.1 := mlift_row0 hKx v (u - v)
  rw [List.map_append, List.map_singleton, mlift_snoc_flat K x v (u - v) hKx]
  have hhead : entry (rcol 0 u (mlift K v (u - v))) 0 0 < 0 + 1 + x := by
    show 0 + 1 < 0 + 1 + x; omega
  have htail : ∀ r, 1 ≤ r → r < (rcol 0 u (mlift K v (u - v))).length →
      0 + 1 + x ≤ entry (rcol 0 u (mlift K v (u - v))) 0 r := by
    intro r hr1 hrl
    obtain ⟨w, rfl⟩ : ∃ w, r = w + 1 := ⟨r - 1, by omega⟩
    have hw : w < (mlift K v (u - v)).length := by rw [rcol_length] at hrl; omega
    rw [entry_rcol_succ, entry0_shiftr01 hw]
    have hmem : (mlift K v (u - v)).getD w (0, 0, 0) ∈ mlift K v (u - v) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw]
      exact List.getElem_mem hw
    have := hTx _ hmem
    show 0 + 1 + x ≤ ((mlift K v (u - v)).getD w (0, 0, 0)).1 + (0 + 1)
    omega
  have e : (((0, u, 0) : ℕ × ℕ × ℕ) ::
      rword 0 u (L.map (fun X => mlift X v (u - v)) ++
        [mlift K v (u - v) ++ [((x, 0, 0) : ℕ × ℕ × ℕ)]]))
      = (((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u (L.map (fun X => mlift X v (u - v))))
        ++ rcol 0 u (mlift K v (u - v)) ++ [((0 + 1 + x, 0, 0) : ℕ × ℕ × ℕ)] := by
    have e1 : shiftr01 (0 + 1) 0 [((x, 0, 0) : ℕ × ℕ × ℕ)]
        = [((0 + 1 + x, 0, 0) : ℕ × ℕ × ℕ)] := by
      simp only [shiftr01, List.map_cons, List.map_nil, List.cons.injEq, and_true]
      exact Prod.ext (by first | (dsimp only; omega) | dsimp only | omega | rfl)
        (Prod.ext (by first | (dsimp only; omega) | dsimp only | omega | rfl) rfl)
    rw [rword_append, rword_singleton, rcol, rcol, shiftr01_append0, e1]
    simp [List.append_assoc]
  rw [e]
  refine A1g_intro (Or.inr (Or.inl ⟨natDom_iff.mpr (Or.inl ?_), fun n hn => ?_⟩))
  · unfold lev
    rw [show ((((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u (L.map (fun X => mlift X v (u - v))))
        ++ rcol 0 u (mlift K v (u - v)) ++ [((0 + 1 + x, 0, 0) : ℕ × ℕ × ℕ)]).length - 1
        = ((((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u (L.map (fun X => mlift X v (u - v))))
          ++ rcol 0 u (mlift K v (u - v))).length + 0
        from by simp; omega,
      entry_append_right, entry_append_right]
    simp [entry]
  · rw [oper_snoc00'' _ (rcol_ne 0 u _) hhead htail n]
    have e2 : (((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u (L.map (fun X => mlift X v (u - v)))) ++
        (List.range n).flatMap (fun _ => rcol 0 u (mlift K v (u - v)))
        = ((0, u, 0) : ℕ × ℕ × ℕ) ::
          rword 0 u ((L ++ List.replicate n K).map (fun X => mlift X v (u - v))) := by
      rw [List.map_append, List.map_replicate, rword_append, rword_replicate]; simp
    rw [e2]
    exact BwT_rep hK hG hL hB n u hu (argOK_rword u _) a ha

#print axioms GT_flat

/-! ## 孤児 -/

open Classical in
theorem mlift_snoc_low (K : TrioSeq) (c : ℕ × ℕ × ℕ) {v : ℕ} (hc : c.2.1 ≤ v) (t : ℕ) :
    mlift (K ++ [c]) v t = mlift K v t ++ [c] := by
  unfold mlift
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    rw [Small.entry_append_left hj, Small.entry_append_left hj, Small.entry_append_left hj,
      if_congr (coneV_append_left hj) rfl rfl]
  · have e : ∀ r, entry (K ++ [c]) r K.length = entry [c] r 0 := fun r => by
      simpa using entry_append_right K [c] r 0
    have hn : ¬ coneV (K ++ [c]) v K.length := fun h => by
      have := h K.length Relation.ReflTransGen.refl
      rw [e] at this
      have e1 : entry [c] 1 0 = c.2.1 := rfl
      omega
    simp only [List.map_cons, List.map_nil]
    rw [if_neg hn, e, e, e]
    rfl

theorem rtg0_append_lift {A B : TrioSeq} {k i : ℕ}
    (h : Relation.ReflTransGen (nextrel0 B) k i) :
    Relation.ReflTransGen (nextrel0 (A ++ B)) (A.length + k) (A.length + i) := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih => exact ih.tail ((nextrel0_append_right A B b c).2 hbc)

open Classical in
theorem mlift_append_low {A B : TrioSeq} {v : ℕ}
    (hB : ∀ i, i < B.length → ∃ k, Relation.ReflTransGen (nextrel0 B) k i ∧ entry B 1 k ≤ v)
    (t : ℕ) : mlift (A ++ B) v t = mlift A v t ++ B := by
  unfold mlift
  rw [List.length_append, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    rw [Small.entry_append_left hj, Small.entry_append_left hj, Small.entry_append_left hj,
      if_congr (coneV_append_left hj) rfl rfl]
  · apply List.ext_getElem (by simp)
    intro i h1 _
    have hi : i < B.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
    obtain ⟨k, hk, hk1⟩ := hB i hi
    have hn : ¬ coneV (A ++ B) v (A.length + i) := fun hc => by
      have := hc (A.length + k) (rtg0_append_lift hk)
      rw [entry_append_right] at this
      omega
    rw [if_neg hn, entry_append_right, entry_append_right, entry_append_right]
    have eg : B.getD i (0, 0, 0) = B[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    show ((B.getD i (0, 0, 0)).1, (B.getD i (0, 0, 0)).2.1 + 0, (B.getD i (0, 0, 0)).2.2) = B[i]
    rw [eg]
    rfl

theorem low_of_Wg {j : ℕ} {z : TrioSeq} (hz : z ∈ Wg (2 * j)) (h : ℕ) {v : ℕ} (hjv : j ≤ v) :
    ∀ i, i < (shiftr01 h 0 z).length →
      ∃ k, Relation.ReflTransGen (nextrel0 (shiftr01 h 0 z)) k i ∧
        entry (shiftr01 h 0 z) 1 k ≤ v := by
  intro i hi
  rw [shiftr01_length] at hi
  have hR := Wg_RiseOkv hz
  by_cases hle : entry z 1 i ≤ j
  · exact ⟨i, .refl, by rw [entry1_shiftr01]; omega⟩
  · obtain ⟨k, -, hk, hk1⟩ := hR i hi (by omega)
    exact ⟨k, rtg0_shiftr01.mpr hk, by rw [entry1_shiftr01]; omega⟩

theorem GT_orph {v : ℕ} {K : TrioSeq} {h j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ v)
    (hnp : ¬ hasParent (K ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1
      ((K ++ [((h, j, 0) : ℕ × ℕ × ℕ)]).length - 1))
    (hzK : ∀ z ∈ Wg (2 * j - 1), based z → GT v (K ++ shiftr01 h 0 z)) :
    GT v (K ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
  intro L hL hB u hu _ a ha
  have hS := stair_step v (u - v)
  have hjv : (((h, j, 0) : ℕ × ℕ × ℕ)).2.1 ≤ v := hj
  rw [List.map_append, List.map_singleton, mlift_snoc_low K _ hjv (u - v), rword0_snoc]
  have hnpT : ¬ hasParent (mlift K v (u - v) ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1
      ((mlift K v (u - v) ++ [((h, j, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
    rw [← mlift_snoc_low K _ hjv (u - v), mlift_eq_slift, hasParent_slift hS, slift_length]
    exact hnp
  obtain ⟨P, hP⟩ : ∃ P : TrioSeq,
      P = (((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u (L.map (fun X => mlift X v (u - v)))) ++
        [((1, u + 1, 1) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  obtain ⟨hPlen, hP0, hPL1, hPL0, hPmid⟩ := P_facts u (L.map (fun X => mlift X v (u - v)))
  rw [← hP] at hPlen hP0 hPL1 hPL0 hPmid ⊢
  set T0 := mlift K v (u - v) with hT0
  have hnp' := noParent_letter (P := P) (T := T0 ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) (v := u) (j := j)
    (by omega) hPlen hP0 hPL1 hPL0 hPmid (by simp)
    (by
      rw [show (T0 ++ [((h, j, 0) : ℕ × ℕ × ℕ)]).length - 1 = T0.length + 0 by simp,
        entry_append_right]
      rfl) hnpT
  have eS : shiftr01 1 0 (T0 ++ [((h, j, 0) : ℕ × ℕ × ℕ)])
      = shiftr01 1 0 T0 ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)] := by
    rw [shiftr01_append0, shift_col]
  have hidx : P.length + ((T0 ++ [((h, j, 0) : ℕ × ℕ × ℕ)]).length - 1)
      = (P ++ shiftr01 1 0 T0).length := by simp [shiftr01]
  rw [eS, hidx, ← List.append_assoc] at hnp'
  rw [eS, ← List.append_assoc]
  have hLL : ((P ++ shiftr01 1 0 T0) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]).length - 1
      = (P ++ shiftr01 1 0 T0).length := by simp
  have eL : ∀ r, entry ((P ++ shiftr01 1 0 T0) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]) r
      (P ++ shiftr01 1 0 T0).length = entry [((h + 1, j, 0) : ℕ × ℕ × ℕ)] r 0 := by
    intro r
    simpa using entry_append_right (P ++ shiftr01 1 0 T0) [((h + 1, j, 0) : ℕ × ℕ × ℕ)] r 0
  have e1 : entry [((h + 1, j, 0) : ℕ × ℕ × ℕ)] 1 0 = j := rfl
  have e2 : entry [((h + 1, j, 0) : ℕ × ℕ × ℕ)] 2 0 = 0 := rfl
  have e0 : entry [((h + 1, j, 0) : ℕ × ℕ × ℕ)] 0 0 = h + 1 := rfl
  have hsr : srow ((P ++ shiftr01 1 0 T0) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)])
      (P ++ shiftr01 1 0 T0).length = 1 := by
    unfold srow; rw [eL, eL, e2, e1]; simp; omega
  have hdom : domT ((P ++ shiftr01 1 0 T0) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]) (2 * j - 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [hLL, eL, eL, e1, e2]; omega
    · rw [hLL, hsr]; exact hnp'
  refine A1g_intro (Or.inr (Or.inr ⟨2 * j - 1, by omega, hdom, by rw [hLL, eL, e2],
    fun z hz hbz => ?_⟩))
  have hg : graft ((P ++ shiftr01 1 0 T0) ++ [((h + 1, j, 0) : ℕ × ℕ × ℕ)]) z
      = P ++ shiftr01 1 0 (T0 ++ shiftr01 h 0 z) := by
    rw [graft_eq_shift, List.dropLast_concat, hLL, eL, e0, shiftr01_append0, shiftr01_add0,
      List.append_assoc]
  have eZ : T0 ++ shiftr01 h 0 z = mlift (K ++ shiftr01 h 0 z) v (u - v) := by
    rw [hT0, mlift_append_low (low_of_Wg (Wg_mono (by omega) hz) h hj)]
  rw [hg, eZ, hP, ← rword0_snoc]
  have hh := hzK z hz hbz L hL hB u hu (argOK_rword u _) a ha
  rwa [List.map_append, List.map_singleton] at hh

#print axioms GT_orph


/-! ## 錐のタイ（根からの塔） -/

open Classical in
theorem mlift_snoc_cone (K : TrioSeq) (c : ℕ × ℕ × ℕ) {v : ℕ}
    (hc : coneV (K ++ [c]) v K.length) (t : ℕ) :
    mlift (K ++ [c]) v t = mlift K v t ++ [((c.1, c.2.1 + t, c.2.2) : ℕ × ℕ × ℕ)] := by
  unfold mlift
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    rw [Small.entry_append_left hj, Small.entry_append_left hj, Small.entry_append_left hj,
      if_congr (coneV_append_left hj) rfl rfl]
  · have e : ∀ r, entry (K ++ [c]) r K.length = entry [c] r 0 := fun r => by
      simpa using entry_append_right K [c] r 0
    simp only [List.map_cons, List.map_nil]
    rw [if_pos hc, e, e, e]
    rfl

theorem noParent_of_coneV {A : TrioSeq} {v b : ℕ} (hc : coneV A v b)
    (hb1 : entry A 1 b ≤ v + 1) : ¬ hasParent A 1 b := by
  rintro ⟨k, hk, -⟩
  have hk' : nextrel1 A k b := by
    unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
  obtain ⟨-, -, -, hk1, hle0, -⟩ := hk'
  have := hc k hle0.2.2
  omega

theorem noParent_head {P T : TrioSeq} {v j : ℕ} (hj : j ≤ v + 1) (hPlen : 1 ≤ P.length)
    (hPL1 : entry P 1 (P.length - 1) = v + 1) (hPL0 : entry P 0 (P.length - 1) = 1)
    (hPmid : ∀ k, k < P.length - 1 → 1 ≤ entry P 0 k)
    (hTne : T ≠ []) (hlast : entry T 1 (T.length - 1) = j)
    (hnp : ¬ hasParent T 1 (T.length - 1)) :
    ¬ hasParent (P ++ shiftr01 1 0 T) 1 (P.length + (T.length - 1)) := by
  have hTl : 0 < T.length := List.length_pos_iff.mpr hTne
  rintro ⟨k, hk, -⟩
  by_cases hkP : P.length ≤ k
  · obtain ⟨q, rfl⟩ : ∃ q, k = P.length + q := ⟨k - P.length, by omega⟩
    have h1 := (nextR_append_right P (shiftr01 1 0 T) 1 q (T.length - 1)).1 hk
    have h2 := nextR_shiftr01.mp h1
    have h3 : nextrel1 T q (T.length - 1) := by
      unfold nextR at h2; rwa [if_neg (by omega), if_pos rfl] at h2
    exact hnp (H12Export.hasParent1_of_le0_witness (by omega) h3.2.2.2.2.1.2.2 h3.2.2.2.1)
  · have hk' : nextrel1 (P ++ shiftr01 1 0 T) k (P.length + (T.length - 1)) := by
      unfold nextR at hk; rwa [if_neg (by omega), if_pos rfl] at hk
    obtain ⟨-, -, hkl, hk1, hle0, -⟩ := hk'
    have hkP' : k < P.length := by omega
    have eL1 : entry (P ++ shiftr01 1 0 T) 1 (P.length + (T.length - 1)) = j := by
      rw [entry_append_right, entry1_shiftr01, hlast]
    rw [Small.entry_append_left hkP', eL1] at hk1
    by_cases hkL : k = P.length - 1
    · rw [hkL, hPL1] at hk1; omega
    · have hrec := rtg0_rec hle0.2.2 (P.length - 1) (by omega) (by omega)
      rw [Small.entry_append_left hkP', Small.entry_append_left (by omega), hPL0] at hrec
      have := hPmid k (by omega)
      omega

theorem GT_tie {v : ℕ} {K : TrioSeq} {x : ℕ}
    (hcone : coneV (K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]) v K.length)
    (hload : ∀ u, v ≤ u → ∀ Z ∈ Wg (2 * u), based Z →
      GT u (mlift K v (u - v) ++ shiftr01 x 0 Z)) :
    GT v (K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]) := by
  intro L hL hB u hu _ a ha
  have hS := stair_step v (u - v)
  have eK : mlift (K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]) v (u - v)
      = mlift K v (u - v) ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)] := by
    rw [mlift_snoc_cone K _ hcone (u - v)]
    show _ ++ [((x, v + 1 + (u - v), 0) : ℕ × ℕ × ℕ)] = _
    rw [show v + 1 + (u - v) = u + 1 by omega]
  rw [List.map_append, List.map_singleton, eK]
  obtain ⟨Lu, hLu⟩ : ∃ Lu, Lu = L.map (fun X => mlift X v (u - v)) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = mlift K v (u - v) := ⟨_, rfl⟩
  rw [← hLu, ← hT]
  obtain ⟨P, hP⟩ : ∃ P : TrioSeq, P = rword 0 u Lu ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)] := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : TrioSeq, R = P ++ shiftr01 1 0 (T ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) :=
    ⟨_, rfl⟩
  have eM : ((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u (Lu ++ [T ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]])
      = ((0, u, 0) : ℕ × ℕ × ℕ) :: R := by
    rw [rword0_snoc, hR, hP]; rfl
  have hRw : R = rword 0 u (Lu ++ [T ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]]) := by
    have := eM; simp only [List.cons.injEq, true_and] at this; exact this.symm
  have hRok : argOK R := by rw [hRw]; exact argOK_rword u _
  have hRne : R ≠ [] := by simp [hR, hP]
  have eRX : R = (P ++ shiftr01 1 0 T) ++ [((x + 1, u + 1, 0) : ℕ × ℕ × ℕ)] := by
    rw [hR, shiftr01_append0, shift_col, List.append_assoc]
  have hRlen : R.length - 1 = (P ++ shiftr01 1 0 T).length := by rw [eRX]; simp
  have eL : ∀ r, entry R r (R.length - 1) = entry [((x + 1, u + 1, 0) : ℕ × ℕ × ℕ)] r 0 := by
    intro r
    rw [hRlen]
    rw [eRX]
    simpa using entry_append_right (P ++ shiftr01 1 0 T) [((x + 1, u + 1, 0) : ℕ × ℕ × ℕ)] r 0
  have e0 : entry R 0 (R.length - 1) = x + 1 := by rw [eL]; rfl
  have e1 : entry R 1 (R.length - 1) = u + 1 := by rw [eL]; rfl
  have e2 : entry R 2 (R.length - 1) = 0 := by rw [eL]; rfl
  have hsr : srow R (R.length - 1) = 1 := by unfold srow; rw [e2, e1]; simp
  have hPlen : 1 ≤ P.length := by simp [hP]
  have hPL : P.length - 1 = (rword 0 u Lu).length + 0 := by simp [hP]
  have hPL1 : entry P 1 (P.length - 1) = u + 1 := by rw [hPL, hP, entry_append_right]; rfl
  have hPL0 : entry P 0 (P.length - 1) = 1 := by rw [hPL, hP, entry_append_right]; rfl
  have hPmid : ∀ k, k < P.length - 1 → 1 ≤ entry P 0 k := by
    intro k hk
    rw [hPL] at hk
    rw [hP, Small.entry_append_left (by omega)]
    have hmem : (rword 0 u Lu).getD k (0, 0, 0) ∈ rword 0 u Lu := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _
    have := rword_ge 0 u Lu _ hmem
    show 1 ≤ ((rword 0 u Lu).getD k (0, 0, 0)).1
    omega
  have hnpK : ¬ hasParent (K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]) 1 K.length :=
    noParent_of_coneV hcone (by
      rw [show K.length = K.length + 0 from rfl, entry_append_right]
      show v + 1 ≤ v + 1; exact le_rfl)
  have hnpT : ¬ hasParent (T ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) 1
      ((T ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
    rw [hT, ← eK, mlift_eq_slift, hasParent_slift hS, slift_length]
    simpa using hnpK
  have hnpR : ¬ hasParent R 1 (R.length - 1) := by
    have h := noParent_head (P := P) (T := T ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]) (v := u)
      (j := u + 1) le_rfl hPlen hPL1 hPL0 hPmid (by simp)
      (by rw [show (T ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]).length - 1 = T.length + 0 by simp,
        entry_append_right]; rfl) hnpT
    have hidx : R.length - 1 = P.length + ((T ++ [((x, u + 1, 0) : ℕ × ℕ × ℕ)]).length - 1) := by
      rw [hR]; simp [shiftr01]
    rw [hidx]
    rw [hR]
    exact h
  have hd : domT R (2 * u + 1) := by
    refine ⟨?_, ?_⟩
    · unfold lev; rw [e1, e2]; omega
    · rw [hsr]; exact hnpR
  have hRl : 0 < R.length := List.length_pos_iff.mpr hRne
  have hpM : hasParent (((0, u, 0) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length := by
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
    · rw [entry_cons_last hRne 1, e1]; show u < u + 1; omega
  have hnat : natDom (((0, u, 0) : ℕ × ℕ × ℕ) :: R) := by
    refine natDom_iff.mpr (Or.inr ?_)
    have hl : ((((0, u, 0) : ℕ × ℕ × ℕ) :: R).length - 1) = R.length := by simp
    rw [hl, srow_cons_last hRne]
    exact hpM
  have hdl : R.dropLast = P ++ shiftr01 1 0 T := by rw [eRX, List.dropLast_concat]
  have htow : ∀ k, tow u 0 R k ∈ Wg (2 * u) := by
    intro k
    induction k with
    | zero => simpa [tow] using Wg_nil (2 * u)
    | succ k ih =>
        have e : tow u 0 R (k + 1) = ((0, u, 0) : ℕ × ℕ × ℕ) ::
            rword 0 u (Lu ++ [T ++ shiftr01 x 0 (tow u 0 R k)]) := by
          rw [tow, graft_eq_shift, e0, hdl, rword0_snoc, shiftr01_append0, shiftr01_add0, hP]
          simp [List.append_assoc]
        rw [e]
        have hG := hload u hu (tow u 0 R k) ih (based_tow u 0 R k)
        rw [← hT] at hG
        have hLu1 : ∀ X ∈ Lu, ∀ x ∈ X, 1 ≤ x.1 := by rw [hLu]; exact mlift_map_ge hL v (u - v)
        have hBu := hG Lu hLu1 (by rw [hLu]; exact BwT_lift hB hu) u le_rfl
          (argOK_rword u _) (2 * u) le_rfl
        rw [Nat.sub_self] at hBu
        simpa only [mlift_zero, List.map_id'] using hBu
  rw [eM]
  refine A1g_intro (Or.inr (Or.inl ⟨hnat, fun n _ => ?_⟩))
  rw [oper_cons_tower1 hRok hRne hd hsr hpM]
  exact Wg_mono ha (htow n)

#print axioms GT_tie


/-! ## 頭の直上の荷（Wg の元を 1 段ずらして足す） -/

theorem GT_loadTop {u : ℕ} {K : TrioSeq} (hK : ∀ y ∈ K, 1 ≤ y.1) (hG : GT u K) :
    ∀ T ∈ Wg (2 * u), based T → GT u (K ++ shiftr01 1 0 T) := by
  have key : Wg (2 * u) ⊆ {T : TrioSeq | T ∈ Wg (2 * u) ∧
      (based T → GT u (K ++ shiftr01 1 0 T))} := by
    refine A2g' ?_
    intro T hA
    have hTW : T ∈ Wg (2 * u) := A1g_intro (Aopg_mono_X hA (fun U hU => hU.1))
    refine ⟨hTW, ?_⟩
    intro hb
    have hb0 : entry T 0 0 = 0 := hb
    by_cases hTnil : T = []
    · subst hTnil; simpa [shiftr01] using hG
    have hTlen : 0 < T.length := List.length_pos_iff.mpr hTnil
    have hge1 : ∀ y ∈ K ++ shiftr01 1 0 T.dropLast, 1 ≤ y.1 := by
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hK y hy
      · simp only [shiftr01, List.mem_map] at hy
        obtain ⟨p, -, rfl⟩ := hy
        dsimp only; omega
    have hrs : rsum K (shiftr01 1 0 T) := by
      intro y hy
      rw [entry0_shiftr01 (by omega), hb0]
      rcases List.mem_append.mp hy with hy | hy
      · exact hK y hy
      · simp only [shiftr01, List.mem_map] at hy
        obtain ⟨p, -, rfl⟩ := hy
        dsimp only; omega
    set c := T.getLast hTnil with hc
    have hsplit : T = T.dropLast ++ [c] := (List.dropLast_append_getLast hTnil).symm
    have hclast : ∀ r, entry T r (T.length - 1) = entry [c] r 0 := by
      intro r
      have h := entry_append_right T.dropLast [c] r 0
      rw [← hsplit] at h
      rw [show T.length - 1 = T.dropLast.length + 0 by simp]
      exact h
    have eC : K ++ shiftr01 1 0 T
        = (K ++ shiftr01 1 0 T.dropLast) ++ [((c.1 + 1, c.2.1, c.2.2) : ℕ × ℕ × ℕ)] := by
      conv_lhs => rw [hsplit]
      rw [shiftr01_append0, List.append_assoc]
      simp [shiftr01]
    have hflat : c.2.1 = 0 → c.2.2 = 0 → c.1 = 0 → GT u (K ++ shiftr01 1 0 T.dropLast) →
        GT u (K ++ shiftr01 1 0 T) := by
      intro h1 h2 h0 hGd
      rw [eC]
      have hceq : ((c.1 + 1, c.2.1, c.2.2) : ℕ × ℕ × ℕ) = ((1, 0, 0) : ℕ × ℕ × ℕ) :=
        Prod.ext (by simp [h0]) (Prod.ext h1 h2)
      rw [hceq]
      exact GT_flat le_rfl hge1 hge1 hGd
    have hdrop1 : T.length = 1 → GT u (K ++ shiftr01 1 0 T.dropLast) := by
      intro hT1
      have hdl : T.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
      rw [hdl]; simpa [shiftr01] using hG
    have hc10 : T.length = 1 → c.1 = 0 := by
      intro hT1
      have : entry T 0 (T.length - 1) = c.1 := hclast 0
      rw [show T.length - 1 = 0 by omega, hb0] at this; omega
    have hlev0 : lev T (T.length - 1) = 0 → c.2.1 = 0 ∧ c.2.2 = 0 := by
      intro hz
      unfold lev at hz
      rw [hclast 1, hclast 2] at hz
      have e1 : entry [c] 1 0 = c.2.1 := rfl
      have e2 : entry [c] 2 0 = c.2.2 := rfl
      rw [e1, e2] at hz
      omega
    rcases hA with ⟨hl, hw0⟩ | ⟨hnat, hop⟩ | ⟨m', hm, hd, h20, hgr⟩
    · have hT1 : T.length = 1 := by omega
      have hz : lev T (T.length - 1) = 0 := by rw [hT1]; exact hw0
      exact hflat (hlev0 hz).1 (hlev0 hz).2 (hc10 hT1) (hdrop1 hT1)
    · by_cases hp : 2 ≤ T.length ∧ hasParent T (srow T (T.length - 1)) (T.length - 1)
      · obtain ⟨hlen2, hp⟩ := hp
        have hlenC : 2 ≤ (K ++ shiftr01 1 0 T).length := by simp [shiftr01]; omega
        have hidx : (K ++ shiftr01 1 0 T).length - 1 = K.length + (T.length - 1) := by
          simp [shiftr01]; omega
        have hpC : hasParent (K ++ shiftr01 1 0 T)
            (srow (K ++ shiftr01 1 0 T) ((K ++ shiftr01 1 0 T).length - 1))
            ((K ++ shiftr01 1 0 T).length - 1) := by
          rw [hidx, srow_append_right, srow_shiftr01,
            hasParent_append_gen (by rw [shiftr01_length]; omega) hrs, hasParent_shiftr01]
          exact hp
        refine GT_oper hlenC hpC (fun n hn => ?_)
        rw [oper_shift K T 1 n hlen2 hp]
        exact (hop n hn).2 (based_oper hn hb)
      · have hlev : lev T (T.length - 1) = 0 := by
          rcases natDom_iff.mp hnat with h | h
          · exact h
          · exfalso
            have hT1 : T.length = 1 := by
              by_contra hne; exact hp ⟨by omega, h⟩
            rw [hT1] at h
            obtain ⟨j0, hj0, -⟩ := h
            exact absurd (nextR_index_lt hj0) (Nat.not_lt_zero j0)
        obtain ⟨h1, h2⟩ := hlev0 hlev
        have hsr0 : srow T (T.length - 1) = 0 := by
          unfold srow; rw [hclast 1, hclast 2]
          show (if 0 < c.2.2 then 2 else if 0 < c.2.1 then 1 else 0) = 0
          simp [h1, h2]
        by_cases hT1 : T.length = 1
        · exact hflat h1 h2 (hc10 hT1) (hdrop1 hT1)
        · have h0 : c.1 = 0 := by
            by_contra hne
            have hc10' : entry T 0 (T.length - 1) = c.1 := hclast 0
            exact hp ⟨by omega, by
              rw [hsr0]
              exact (hasParent_zero_iff (by omega)).mpr ⟨0, by omega, by rw [hb0, hc10']; omega⟩⟩
          have h1' := (hop 1 le_rfl).2 (based_oper le_rfl hb)
          rw [oper_one_eq_dropLast (by omega)] at h1'
          exact hflat h1 h2 h0 h1'
    · have hlev := hd.1
      unfold lev at hlev
      have h20' : entry T 2 (T.length - 1) = 0 := h20
      have hj1 : 1 ≤ entry T 1 (T.length - 1) := by omega
      have hjv : entry T 1 (T.length - 1) ≤ u := by omega
      have hm' : m' = 2 * entry T 1 (T.length - 1) - 1 := by omega
      subst hm'
      have hsr : srow T (T.length - 1) = 1 := by
        unfold srow; rw [if_neg (by omega), if_pos (by omega)]
      have hnp : ¬ hasParent T 1 (T.length - 1) := fun hh => hd.2 (by rw [hsr]; exact hh)
      have hc1' : c.2.1 = entry T 1 (T.length - 1) := (hclast 1).symm
      have hc20 : c.2.2 = 0 := by have := hclast 2; rw [h20'] at this; exact this.symm
      generalize hjdef : entry T 1 (T.length - 1) = j at hj1 hjv hc1' hgr hnp
      have eC' : K ++ shiftr01 1 0 T
          = (K ++ shiftr01 1 0 T.dropLast) ++ [((c.1 + 1, j, 0) : ℕ × ℕ × ℕ)] := by
        rw [eC, hc1', hc20]
      rw [eC']
      refine GT_orph hj1 hjv ?_ ?_
      · intro hh
        apply hnp
        have hidx2 : (K ++ shiftr01 1 0 T).length - 1 = K.length + (T.length - 1) := by
          simp [shiftr01] <;> omega
        first
          | (rw [hidx2, hasParent_append_gen (by rw [shiftr01_length]; omega) hrs,
              hasParent_shiftr01] at hh; exact hh)
          | (rw [← eC', hidx2, hasParent_append_gen (by rw [shiftr01_length]; omega) hrs,
              hasParent_shiftr01] at hh; exact hh)
      · intro z hz hbz
        have h1 := (hgr z hz hbz).2 (based_graft_arg hTnil hb hbz)
        have e : graft T z = T.dropLast ++ shiftr01 c.1 0 z := by
          rw [graft_eq_shift, hclast 0]; rfl
        rw [e, shiftr01_append0, shiftr01_add0, ← List.append_assoc] at h1
        exact h1
  intro T hT hb
  exact (key hT).2 hb

#print axioms GT_loadTop

end GxK
end TRIO
