/-
GzJ.lean: 最上段の「遠い字と荷の語」の並び。

    fwTop v us = (1,v+1,1) :: unitsC v us        （最上段の語の中身、us は荷だけ）
    rword 0 u (uss.map (fwTop u)) = GzH.farU u (u+1) uss

最上段の潰れの写しは閾値が根の段 v なので、行 1 が v+1 のタイは写しで持ち上がる。
よって接頭辞の語の単位は荷だけ（NoTie）。最後の語だけ、最後に子のないタイを 1 個置ける。

GTC C v K : 接頭辞を組 C に限った GT。GxK の GT_oper / GT_orph / GT_flat / GT_tie と
GT_loadTop を、接頭辞 L ごとに示す形のまま C つきに写した。
-/
import GzI

namespace TRIO
namespace GzJ

open Wset Small GwS Gw GwU GwZ GxD GxG GxJ GxK GxL GxN GxP GxR GxT GxV GxW GxY
open GyA GyB GyC GyD GyE GyF GyG GyH GyI GyJ GyK GzD GzF GzH GzI

/-! ## 接頭辞の組つきの GT -/

def GTC (C : ℕ → List TrioSeq → Prop) (v : ℕ) (K : TrioSeq) : Prop :=
  ∀ L : List TrioSeq, C v L → (∀ X ∈ L, ∀ x ∈ X, 1 ≤ x.1) → BwT v L → BwT v (L ++ [K])

theorem GTC_oper {C : ℕ → List TrioSeq → Prop} {v : ℕ} {K : TrioSeq} (hlen : 2 ≤ K.length)
    (hp : hasParent K (srow K (K.length - 1)) (K.length - 1))
    (hIH : ∀ n, 1 ≤ n → GTC C v (K⟦n⟧)) : GTC C v K := by
  intro L hC hL hB u hu _ a ha
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
  have h := hIH n hn L hC hL hB u hu (argOK_rword u _) a ha
  rw [List.map_append, List.map_singleton, rword0_snoc] at h
  exact h

theorem BwTC_rep {C : ℕ → List TrioSeq → Prop} {v : ℕ} {K : TrioSeq} (hK : ∀ x ∈ K, 1 ≤ x.1)
    (hG : GTC C v K) (hCK : ∀ L, C v L → C v (L ++ [K]))
    {L : List TrioSeq} (hC : C v L) (hL : ∀ X ∈ L, ∀ x ∈ X, 1 ≤ x.1) (hB : BwT v L) :
    ∀ n, C v (L ++ List.replicate n K) ∧ BwT v (L ++ List.replicate n K)
  | 0 => by simpa using And.intro hC hB
  | (n + 1) => by
      have hLn : ∀ X ∈ L ++ List.replicate n K, ∀ x ∈ X, 1 ≤ x.1 := by
        intro X hX
        rcases List.mem_append.mp hX with hX | hX
        · exact hL X hX
        · rw [List.eq_of_mem_replicate hX]; exact hK
      obtain ⟨hCn, hBn⟩ := BwTC_rep hK hG hCK hC hL hB n
      have h := hG _ hCn hLn hBn
      have hc := hCK _ hCn
      rw [List.append_assoc, ← List.replicate_succ'] at h hc
      exact ⟨hc, h⟩

theorem GTC_flat {C : ℕ → List TrioSeq → Prop} {v : ℕ} {K : TrioSeq} {x : ℕ} (hx : 1 ≤ x)
    (hK : ∀ y ∈ K, 1 ≤ y.1) (hKx : ∀ y ∈ K, x ≤ y.1) (hG : GTC C v K)
    (hCK : ∀ L, C v L → C v (L ++ [K])) : GTC C v (K ++ [((x, 0, 0) : ℕ × ℕ × ℕ)]) := by
  intro L hC hL hB u hu _ a ha
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
    exact (BwTC_rep hK hG hCK hC hL hB n).2 u hu (argOK_rword u _) a ha

theorem GTC_orph {C : ℕ → List TrioSeq → Prop} {v : ℕ} {K : TrioSeq} {h j : ℕ}
    (hj1 : 1 ≤ j) (hj : j ≤ v)
    (hnp : ¬ hasParent (K ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) 1
      ((K ++ [((h, j, 0) : ℕ × ℕ × ℕ)]).length - 1))
    (hzK : ∀ z ∈ Wg (2 * j - 1), based z → GTC C v (K ++ shiftr01 h 0 z)) :
    GTC C v (K ++ [((h, j, 0) : ℕ × ℕ × ℕ)]) := by
  intro L hC hL hB u hu _ a ha
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
  have hh := hzK z hz hbz L hC hL hB u hu (argOK_rword u _) a ha
  rwa [List.map_append, List.map_singleton] at hh

theorem GTC_tie {C : ℕ → List TrioSeq → Prop} {v : ℕ} {K : TrioSeq} {x : ℕ}
    (hcone : coneV (K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]) v K.length)
    (hload : ∀ u, v ≤ u → ∀ Z ∈ Wg (2 * u), based Z →
      GTC C u (mlift K v (u - v) ++ shiftr01 x 0 Z))
    (hClift : ∀ L, C v L → ∀ u, v ≤ u → C u (L.map (fun X => mlift X v (u - v)))) :
    GTC C v (K ++ [((x, v + 1, 0) : ℕ × ℕ × ℕ)]) := by
  intro L hC hL hB u hu _ a ha
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
        have hBu := hG Lu (by rw [hLu]; exact hClift L hC u hu) hLu1
          (by rw [hLu]; exact BwT_lift hB hu) u le_rfl (argOK_rword u _) (2 * u) le_rfl
        rw [Nat.sub_self] at hBu
        simpa only [mlift_zero, List.map_id'] using hBu
  rw [eM]
  refine A1g_intro (Or.inr (Or.inl ⟨hnat, fun n _ => ?_⟩))
  rw [oper_cons_tower1 hRok hRne hd hsr hpM]
  exact Wg_mono ha (htow n)

theorem GTC_loadTop {C : ℕ → List TrioSeq → Prop} {u : ℕ} {K : TrioSeq}
    (hK : ∀ y ∈ K, 1 ≤ y.1) (hG : GTC C u K)
    (hCK : ∀ T' ∈ Wg (2 * u), based T' → ∀ L, C u L → C u (L ++ [K ++ shiftr01 1 0 T'])) :
    ∀ T ∈ Wg (2 * u), based T → GTC C u (K ++ shiftr01 1 0 T) := by
  have key : Wg (2 * u) ⊆ {T : TrioSeq | T ∈ Wg (2 * u) ∧
      (based T → GTC C u (K ++ shiftr01 1 0 T))} := by
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
    have hflat : c.2.1 = 0 → c.2.2 = 0 → c.1 = 0 → T.dropLast ∈ Wg (2 * u) →
        GTC C u (K ++ shiftr01 1 0 T.dropLast) → GTC C u (K ++ shiftr01 1 0 T) := by
      intro h1 h2 h0 hdW hGd
      rw [eC]
      have hceq : ((c.1 + 1, c.2.1, c.2.2) : ℕ × ℕ × ℕ) = ((1, 0, 0) : ℕ × ℕ × ℕ) :=
        Prod.ext (by simp [h0]) (Prod.ext h1 h2)
      rw [hceq]
      exact GTC_flat le_rfl hge1 hge1 hGd (hCK _ hdW (based_dropLast hb))
    have hdrop1 : T.length = 1 → GTC C u (K ++ shiftr01 1 0 T.dropLast) := by
      intro hT1
      have hdl : T.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
      rw [hdl]; simpa [shiftr01] using hG
    have hdropW : T.length = 1 → T.dropLast ∈ Wg (2 * u) := by
      intro hT1
      have hdl : T.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
      rw [hdl]; exact Wg_nil _
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
      exact hflat (hlev0 hz).1 (hlev0 hz).2 (hc10 hT1) (hdropW hT1) (hdrop1 hT1)
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
        refine GTC_oper hlenC hpC (fun n hn => ?_)
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
        · exact hflat h1 h2 (hc10 hT1) (hdropW hT1) (hdrop1 hT1)
        · have h0 : c.1 = 0 := by
            by_contra hne
            have hc10' : entry T 0 (T.length - 1) = c.1 := hclast 0
            exact hp ⟨by omega, by
              rw [hsr0]
              exact (hasParent_zero_iff (by omega)).mpr ⟨0, by omega, by rw [hb0, hc10']; omega⟩⟩
          have h1' := hop 1 le_rfl
          rw [oper_one_eq_dropLast (by omega)] at h1'
          exact hflat h1 h2 h0 h1'.1 (h1'.2 (based_dropLast hb))
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
      refine GTC_orph hj1 hjv ?_ ?_
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

/-! ## 最上段の遠い字と荷の語 -/

theorem RawUs_nil (v : ℕ) : RawUs v [] := fun _ h => by simp at h

theorem RawUs_cons {v : ℕ} {us : List (Option TrioSeq)} {uss : List (List (Option TrioSeq))}
    (h1 : RawU v us) (h2 : RawUs v uss) : RawUs v (us :: uss) := by
  intro us' h
  simp only [List.mem_cons] at h
  rcases h with rfl | h
  · exact h1
  · exact h2 us' h

def fwTop (v : ℕ) (us : List (Option TrioSeq)) : TrioSeq :=
  ((1, v + 1, 1) : ℕ × ℕ × ℕ) :: unitsC v us

def NoTie (us : List (Option TrioSeq)) : Prop := none ∉ us

def TopC (v : ℕ) (L : List TrioSeq) : Prop :=
  ∃ uss : List (List (Option TrioSeq)), RawUs v uss ∧ (∀ us ∈ uss, NoTie us) ∧
    L = uss.map (fwTop v)

theorem Fr_fwTop (v : ℕ) (us : List (Option TrioSeq)) : ∀ x ∈ fwTop v us, 1 ≤ x.1 :=
  Fr_FLunits v (v + 1) us

theorem Fr_map_fwTop (v : ℕ) (uss : List (List (Option TrioSeq))) :
    ∀ X ∈ uss.map (fwTop v), ∀ x ∈ X, 1 ≤ x.1 := by
  intro X hX
  simp only [List.mem_map] at hX
  obtain ⟨us, -, rfl⟩ := hX
  exact Fr_fwTop v us

theorem mlift_fwTop {v : ℕ} {us : List (Option TrioSeq)} (hR : RawU v us) (d : ℕ) :
    mlift (fwTop v us) v d = fwTop (v + d) us := by
  unfold fwTop
  have e := mlift_units_base (b := v) (X := [((1, v + 1, 1) : ℕ × ℕ × ℕ)])
    (Fr_single le_rfl _ _) us hR d
  simp only [List.singleton_append] at e
  rw [e, mlift_one (show v < v + 1 by omega)]
  simp only [List.singleton_append, show v + 1 + d = v + d + 1 by omega]

theorem map_mlift_fwTop {v u : ℕ} (hu : v ≤ u) {uss : List (List (Option TrioSeq))}
    (hR : RawUs v uss) :
    (uss.map (fwTop v)).map (fun X => mlift X v (u - v)) = uss.map (fwTop u) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro us hus
  simp only [Function.comp_apply]
  rw [mlift_fwTop (hR us hus), show v + (u - v) = u by omega]

theorem TopC_lift : ∀ (L : List TrioSeq) (v : ℕ), TopC v L → ∀ u, v ≤ u →
    TopC u (L.map (fun X => mlift X v (u - v))) := by
  intro L v hC u hu
  obtain ⟨uss, hR, hNT, rfl⟩ := hC
  exact ⟨uss, RawUs_mono hu hR, hNT, map_mlift_fwTop hu hR⟩

theorem unitsC_noTie {us : List (Option TrioSeq)} (h : NoTie us) (v w : ℕ) :
    unitsC v us = unitsC w us := by
  induction us using List.reverseRecOn with
  | nil => rfl
  | append_singleton us o ih =>
      rw [unitsC_snoc, unitsC_snoc, ih (fun hn => h (List.mem_append_left _ hn))]
      cases o with
      | none => exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) h
      | some Z => rfl

theorem farU_noTie (b b' r : ℕ) : ∀ uss : List (List (Option TrioSeq)),
    (∀ us ∈ uss, NoTie us) → farU b r uss = farU b' r uss
  | [] => fun _ => rfl
  | us :: uss => fun h => by
      rw [farU_cons, farU_cons, farU_noTie b b' r uss (fun us' hus' => h us' (by simp [hus']))]
      unfold fwU
      rw [unitsC_noTie (h us (by simp)) b b']

theorem rword_fwTop (u : ℕ) : ∀ uss : List (List (Option TrioSeq)),
    rword 0 u (uss.map (fwTop u)) = farU u (u + 1) uss
  | [] => rfl
  | us :: uss => by
      show rcol 0 u (fwTop u us) ++ rword 0 u (uss.map (fwTop u))
        = fwU u (u + 1) us ++ farU u (u + 1) uss
      rw [rword_fwTop u uss]
      rfl

theorem mlift_farU_noTie {b c r : ℕ} {uss : List (List (Option TrioSeq))}
    (hNT : ∀ us ∈ uss, NoTie us) (hR : RawUs b uss) (hbc : b ≤ c) (hcr : c < r) (j : ℕ) :
    mlift (farU b r uss) c j = farU b (r + j) uss := by
  rcases Nat.lt_or_ge b c with h | h
  · exact mlift_farU_high (by omega) hcr j uss hR
  · rw [show c = b by omega, mlift_farU_base (show b < r by omega) j uss hR,
      farU_noTie (b + j) b (r + j) uss hNT]

theorem mlift_PUL {b c : ℕ} (hbc : b ≤ c) {uss : List (List (Option TrioSeq))}
    (hNT : ∀ us ∈ uss, NoTie us) (hR : RawUs b uss) (j : ℕ) :
    mlift (farU b (c + 1) uss ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c j
      = farU b (c + 1 + j) uss ++ [((1, c + 1 + j, 1) : ℕ × ℕ × ℕ)] := by
  rw [mlift_app (Fr_farU _ _ uss) (fun _ => rfl), mlift_farU_noTie hNT hR hbc (by omega) j,
    mlift_one (show c < c + 1 by omega)]

theorem farU_flatL {b : ℕ} {uss : List (List (Option TrioSeq))} (hNT : ∀ us ∈ uss, NoTie us)
    (hR : RawUs b uss) :
    ∀ m c, b ≤ c → (List.range (m + 1)).flatMap (fun j =>
      shiftr01 (j * 2) 0 (((0, c + j, 0) : ℕ × ℕ × ℕ) ::
        mlift (farU b (c + 1) uss ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c j))
      = ((0, c, 0) : ℕ × ℕ × ℕ) :: towU b uss (c + 1) m
  | 0, c, hc => by simp [mlift_PUL hc hNT hR, towU]
  | m + 1, c, hc => by
      rw [flatMap_range_cons _ (m + 1)]
      have e : ∀ j, shiftr01 ((j + 1) * 2) 0 (((0, c + (j + 1), 0) : ℕ × ℕ × ℕ) ::
          mlift (farU b (c + 1) uss ++ [((1, c + 1, 1) : ℕ × ℕ × ℕ)]) c (j + 1))
          = shiftr01 2 0 (shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift (farU b (c + 1 + 1) uss ++ [((1, c + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (c + 1) j)) := by
        intro j
        rw [mlift_PUL hc hNT hR, mlift_PUL (c := c + 1) (by omega) hNT hR, shift_shift,
          show c + (j + 1) = c + 1 + j by omega, show c + 1 + (j + 1) = c + 1 + 1 + j by omega,
          show (j + 1) * 2 = j * 2 + 2 by omega]
      simp only [e]
      rw [← shift_flatMap 2 (fun j => shiftr01 (j * 2) 0 (((0, c + 1 + j, 0) : ℕ × ℕ × ℕ) ::
            mlift (farU b (c + 1 + 1) uss ++ [((1, c + 1 + 1, 1) : ℕ × ℕ × ℕ)]) (c + 1) j)),
        farU_flatL hNT hR m (c + 1) (by omega)]
      have eT : shiftr01 1 0 (((1, c + 1, 0) : ℕ × ℕ × ℕ) :: shiftr01 1 0 (towU b uss (c + 1 + 1) m))
          = shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towU b uss (c + 1 + 1) m) := by
        rw [show shiftr01 2 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towU b uss (c + 1 + 1) m)
            = shiftr01 (1 + 1) 0 (((0, c + 1, 0) : ℕ × ℕ × ℕ) :: towU b uss (c + 1 + 1) m) from rfl,
          ← shift_shift]
        rfl
      rw [towU, eT]
      simp [mlift_PUL hc hNT hR]

theorem Fr_towU (b : ℕ) (uss : List (List (Option TrioSeq))) : ∀ m r, Fr (towU b uss r m)
  | 0, r => by rw [towU]; exact Fr_append (Fr_farU _ _ _) (Fr_single le_rfl _ _)
  | m + 1, r => by rw [towU]; exact Fr_append (Fr_farU _ _ _) (Fr_letter _ _)

/-! ## 最上段の潰れ -/

theorem towTop_Wg {u : ℕ} {uss : List (List (Option TrioSeq))} (hR : RawUs u uss)
    (hB : BwT u (uss.map (fwTop u))) :
    ∀ m, (((0, u, 0) : ℕ × ℕ × ℕ) :: towU u uss (u + 1) m) ∈ Wg (2 * u) := by
  have key : ∀ Cm, GT u Cm →
      (((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u (uss.map (fwTop u) ++ [Cm])) ∈ Wg (2 * u) := by
    intro Cm hG
    refine Wg_of_starOK ⟨?_, fun p hp => rword_ge 0 u _ p hp⟩
    have := hG _ (Fr_map_fwTop u uss) hB u le_rfl
    rw [Nat.sub_self] at this
    simpa only [mlift_zero, List.map_id'] using this
  intro m
  cases m with
  | zero =>
      have := key [] (GT_nil u)
      rw [rword_append, rword_fwTop, rword_singleton] at this
      rw [towU]
      simpa [rcol, shiftr01] using this
  | succ m =>
      have hG := towU_GpT (FarCU_all u uss) m [] 1 (fun _ => 0) u le_rfl hR (by simp) (by simp)
        le_rfl
      rw [liftOff_zeroF] at hG
      have hTF := TF_tieG (u := u) (TF_nil u) (GF_of_GPF ⟨hG, Fr_towU u uss m _⟩)
      have := key _ (GT_of_GTall hTF.1)
      rw [rword_append, rword_fwTop, rword_singleton] at this
      rw [towU]
      simpa [rcol, shiftr01] using this

theorem GTC_top_nil (v : ℕ) : GTC TopC v (fwTop v []) := by
  intro L hC hL hB u hu _ a ha
  obtain ⟨uss, hR, hNT, rfl⟩ := hC
  have hRu : RawUs u uss := RawUs_mono hu hR
  have e1 := map_mlift_fwTop hu hR
  have e : rword 0 u ((uss.map (fwTop v) ++ [fwTop v []]).map (fun X => mlift X v (u - v)))
      = (farU u (u + 1) uss ++ [((1, u + 1, 1) : ℕ × ℕ × ℕ)]) ++ [((2, u + 1, 1) : ℕ × ℕ × ℕ)] := by
    rw [List.map_append, e1, List.map_singleton, mlift_fwTop (RawU_nil v),
      show v + (u - v) = u by omega, rword_append, rword_fwTop, rword_singleton]
    simp [rcol, fwTop, unitsC, shiftr01]
  show (((0, u, 0) : ℕ × ℕ × ℕ) :: rword 0 u ((uss.map (fwTop v) ++ [fwTop v []]).map
    (fun X => mlift X v (u - v)))) ∈ Wg a
  rw [e]
  obtain ⟨hP, hcone⟩ := farU_P u u uss
  refine A1g_intro (Or.inr (Or.inl ⟨zcone_natDom hP (show 1 ≤ 2 by omega) hcone,
    fun k hk => ?_⟩))
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [oper_zcone hP (show 1 ≤ 2 by omega) hcone (m + 1), farU_flatL hNT hRu m u le_rfl]
  have hBu : BwT u (uss.map (fwTop u)) := by
    have := BwT_lift hB hu
    rwa [e1] at this
  exact Wg_mono ha (towTop_Wg hRu hBu m)

/-! ## 最上段の荷と、並びの全体 -/

theorem GTC_top_load {v : ℕ} {us : List (Option TrioSeq)} (hNT : NoTie us) (hRus : RawU v us)
    (hG : GTC TopC v (fwTop v us)) :
    ∀ T ∈ Wg (2 * v), based T → GTC TopC v (fwTop v (us ++ [some T])) := by
  intro T hT hbT
  have e : fwTop v (us ++ [some T]) = fwTop v us ++ shiftr01 1 0 T := by
    simp [fwTop, unitsC_snoc, unitC]
  rw [e]
  refine GTC_loadTop (Fr_fwTop v us) hG ?_ T hT hbT
  intro T' hT' hbT' L hC
  obtain ⟨uss, hR, hNTs, rfl⟩ := hC
  refine ⟨uss ++ [us ++ [some T']], ?_, ?_, ?_⟩
  · intro us' hus'
    rcases List.mem_append.mp hus' with hus' | hus'
    · exact hR us' hus'
    · simp at hus'; subst hus'
      intro Z hZ
      rcases List.mem_append.mp hZ with hZ | hZ
      · exact hRus Z hZ
      · simp at hZ; subst hZ; exact ⟨hT', hbT'⟩
  · intro us' hus'
    rcases List.mem_append.mp hus' with hus' | hus'
    · exact hNTs us' hus'
    · simp at hus'; subst hus'
      intro hn
      rcases List.mem_append.mp hn with hn | hn
      · exact hNT hn
      · simp at hn
  · simp [fwTop, unitsC_snoc, unitC]

theorem GTC_top_units (v : ℕ) : ∀ us : List (Option TrioSeq), NoTie us → RawU v us →
    GTC TopC v (fwTop v us) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => intro _ _; exact GTC_top_nil v
  | append_singleton us o ih =>
      intro hNT hR
      have hNT' : NoTie us := fun h => hNT (List.mem_append_left _ h)
      cases o with
      | none => exact absurd (List.mem_append_right _ (List.mem_singleton_self _)) hNT
      | some Z =>
          have hZ := hR Z (by simp)
          exact GTC_top_load hNT' (RawU_prefix hR) (ih hNT' (RawU_prefix hR)) Z hZ.1 hZ.2

theorem BwT_topFar {v : ℕ} : ∀ uss : List (List (Option TrioSeq)), RawUs v uss →
    (∀ us ∈ uss, NoTie us) → BwT v (uss.map (fwTop v)) := by
  intro uss
  induction uss using List.reverseRecOn with
  | nil => intro _ _; exact BwT_nil v
  | append_singleton uss us ih =>
      intro hR hNT
      have hR' : RawUs v uss := fun us' h => hR us' (List.mem_append_left _ h)
      have hNT' : ∀ us' ∈ uss, NoTie us' := fun us' h => hNT us' (List.mem_append_left _ h)
      rw [List.map_append, List.map_singleton]
      exact GTC_top_units v us (hNT us (by simp)) (hR us (by simp)) _ ⟨uss, hR', hNT', rfl⟩
        (Fr_map_fwTop v uss) (ih hR' hNT')

theorem BwT_topFarTie {v : ℕ} (uss : List (List (Option TrioSeq))) (hR : RawUs v uss)
    (hNT : ∀ us ∈ uss, NoTie us) (us : List (Option TrioSeq)) (hRus : RawU v us)
    (hNTus : NoTie us) :
    BwT v (uss.map (fwTop v) ++ [fwTop v (us ++ [none])]) := by
  have e : fwTop v (us ++ [none]) = fwTop v us ++ [((1, v + 1, 0) : ℕ × ℕ × ℕ)] := by
    simp [fwTop, unitsC_snoc, unitC]
  rw [e]
  refine GTC_tie (C := TopC) (coneV_top (Fr_fwTop v us) v) (fun u hu Z hZ hbZ => ?_)
    (fun L hC u hu => TopC_lift L v hC u hu) _ ⟨uss, hR, hNT, rfl⟩ (Fr_map_fwTop v uss)
    (BwT_topFar uss hR hNT)
  rw [mlift_fwTop hRus, show v + (u - v) = u by omega]
  have hR' : RawU u (us ++ [some Z]) := by
    intro Z' hZ'
    rcases List.mem_append.mp hZ' with hZ' | hZ'
    · exact RawU_mono hu hRus Z' hZ'
    · simp at hZ'; subst hZ'; exact ⟨hZ, hbZ⟩
  have hNT' : NoTie (us ++ [some Z]) := by
    intro hn
    rcases List.mem_append.mp hn with hn | hn
    · exact hNTus hn
    · simp at hn
  have := GTC_top_units u (us ++ [some Z]) hNT' hR'
  have e2 : fwTop u (us ++ [some Z]) = fwTop u us ++ shiftr01 1 0 Z := by
    simp [fwTop, unitsC_snoc, unitC]
  rwa [e2] at this

theorem BwT_append_words {v : ℕ} {L : List TrioSeq} (hL : ∀ X ∈ L, ∀ x ∈ X, 1 ≤ x.1)
    (hB : BwT v L) : ∀ Ls : List TrioSeq, WordsG v Ls → BwT v (L ++ Ls) := by
  intro Ls
  induction Ls using List.reverseRecOn with
  | nil => intro _; simpa using hB
  | append_singleton Ls K ih =>
      intro hW
      have hK := hW K (by simp)
      rw [← List.append_assoc]
      refine hK.1 _ (fun X hX => ?_) (ih (fun X hX => hW X (List.mem_append_left _ hX)))
      rcases List.mem_append.mp hX with h | h
      · exact hL X h
      · exact (hW X (List.mem_append_left _ h)).2

theorem starOK_topFar {v : ℕ} (uss : List (List (Option TrioSeq))) (hR : RawUs v uss)
    (hNT : ∀ us ∈ uss, NoTie us) {Ls : List TrioSeq} (hW : WordsG v Ls) :
    StarOK v (rword 0 v (uss.map (fwTop v) ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hB := BwT_append_words (Fr_map_fwTop v uss) (BwT_topFar uss hR hNT) Ls hW v le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

theorem starOK_topFarTie {v : ℕ} (uss : List (List (Option TrioSeq))) (hR : RawUs v uss)
    (hNT : ∀ us ∈ uss, NoTie us) (us : List (Option TrioSeq)) (hRus : RawU v us)
    (hNTus : NoTie us) {Ls : List TrioSeq} (hW : WordsG v Ls) :
    StarOK v (rword 0 v (uss.map (fwTop v) ++ [fwTop v (us ++ [none])] ++ Ls)) := by
  refine ⟨?_, fun p hp => rword_ge 0 v _ p hp⟩
  have hFr : ∀ X ∈ uss.map (fwTop v) ++ [fwTop v (us ++ [none])], ∀ x ∈ X, 1 ≤ x.1 := by
    intro X hX
    rcases List.mem_append.mp hX with h | h
    · exact Fr_map_fwTop v uss X h
    · simp at h; subst h; exact Fr_fwTop v _
  have hB := BwT_append_words hFr (BwT_topFarTie uss hR hNT us hRus hNTus) Ls hW v le_rfl
  rw [Nat.sub_self] at hB
  simpa only [mlift_zero, List.map_id'] using hB

end GzJ
end TRIO
