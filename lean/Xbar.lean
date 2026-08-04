/-
Xbar.lean: 連接ミラー（trio 版 Buchholz 2.4(a) の深さ付き形）。

`T` の最終列の親が `T` 内にあるとき、前置 `A` は展開に関与しない:

    (A ++ T)⟦n⟧ = A ++ T⟦n⟧

これが GraftAll 機械の (a)-枝（ミラー枝）と γ/β 装置の作業馬。
`graft` 版の系 `oper_graft_inner` も出す。
-/
import Wset

namespace TRIO

open Wset

section AppendMirror

variable {A T : TrioSeq}

/-- A parented trailing column is not all-zero. -/
theorem nextR_nonzero {T : TrioSeq} {i q j : ℕ} (hq : nextR T i q j)
    (hi : i = srow T j) :
    ¬ (entry T 0 j = 0 ∧ entry T 1 j = 0 ∧ entry T 2 j = 0) := by
  rintro ⟨h0, h1, h2⟩
  have hsr : srow T j = 0 := by unfold srow; rw [if_neg (by omega), if_neg (by omega)]
  rw [hi, hsr] at hq
  unfold nextR at hq
  rw [if_pos rfl] at hq
  have := hq.2.2.2.1
  omega

/-- The parent transports across a prefix append (no root hypothesis). -/
theorem parent_append_right_of (A T : TrioSeq) {i j : ℕ}
    (hp : hasParent T i j) :
    parent (A ++ T) i (A.length + j) = A.length + parent T i j := by
  have hAp : hasParent (A ++ T) i (A.length + j) := hasParent_append_right_of A T hp
  have hnr := parent_nextR hAp
  have hnrT := parent_nextR hp
  have hge := nextR_src_ge hnrT hnr
  obtain ⟨y', hy'⟩ : ∃ y', parent (A ++ T) i (A.length + j) = A.length + y' :=
    ⟨parent (A ++ T) i (A.length + j) - A.length, by omega⟩
  rw [hy'] at hnr ⊢
  have := hp.unique ((nextR_append_right A T i y' j).1 hnr) hnrT
  omega

/-- **The append mirror**: when the trailing column of `T` has its parent
inside `T`, a prefix `A` passes through the expansion untouched. -/
theorem oper_append_inner (n : ℕ) (hT : T ≠ [])
    (hL : T.length - 1 ≠ 0)
    (hp : hasParent T (srow T (T.length - 1)) (T.length - 1)) :
    (A ++ T)⟦n⟧ = A ++ T⟦n⟧ := by
  classical
  have hTlen : 0 < T.length := List.length_pos_iff.mpr hT
  set x := T.length - 1 with hx
  have hCx : (A ++ T).length - 1 = A.length + x := by
    rw [List.length_append]; omega
  have hsr : srow (A ++ T) ((A ++ T).length - 1) = srow T x := by
    rw [hCx, srow_append_right]
  have hznT := nextR_nonzero (parent_nextR hp) rfl
  have hzn : ¬ (entry (A ++ T) 0 ((A ++ T).length - 1) = 0 ∧
      entry (A ++ T) 1 ((A ++ T).length - 1) = 0 ∧
      entry (A ++ T) 2 ((A ++ T).length - 1) = 0) := by
    rw [hCx, entry_append_right, entry_append_right, entry_append_right]
    exact hznT
  have hpC : hasParent (A ++ T) (srow (A ++ T) ((A ++ T).length - 1))
      ((A ++ T).length - 1) := by
    rw [hsr, hCx]
    exact hasParent_append_right_of A T hp
  have hLC : (A ++ T).length - 1 ≠ 0 := by rw [hCx]; omega
  set q := parent T (srow T x) x with hq
  have hqlt : q < x := nextR_index_lt (parent_nextR hp)
  have hparC : parent (A ++ T) (srow (A ++ T) ((A ++ T).length - 1))
      ((A ++ T).length - 1) = A.length + q := by
    rw [hsr, hCx]
    exact parent_append_right_of A T hp
  rw [oper_gcopies n hLC hzn hpC, oper_gcopies n hL hznT hp, hparC, hsr, hCx,
    ← hq]
  rw [take_append_right, List.append_assoc]
  congr 1
  congr 1
  have hlen : A.length + x - (A.length + q) = x - q := by omega
  rw [hlen]
  have he0 : entry (A ++ T) 0 (A.length + x) = entry T 0 x := entry_append_right A T 0 x
  have he0' : entry (A ++ T) 0 (A.length + q) = entry T 0 q := entry_append_right A T 0 q
  have he1 : entry (A ++ T) 1 (A.length + x) = entry T 1 x := entry_append_right A T 1 x
  have he1' : entry (A ++ T) 1 (A.length + q) = entry T 1 q := entry_append_right A T 1 q
  have hd0 : (if 0 < srow T x then entry (A ++ T) 0 (A.length + x)
      - entry (A ++ T) 0 (A.length + q) else 0)
      = (if 0 < srow T x then entry T 0 x - entry T 0 q else 0) := by
    rw [he0, he0']
  have hd1 : (if 1 < srow T x then entry (A ++ T) 1 (A.length + x)
      - entry (A ++ T) 1 (A.length + q) else 0)
      = (if 1 < srow T x then entry T 1 x - entry T 1 q else 0) := by
    rw [he1, he1']
  rw [hd0, hd1]
  -- the guarded copies over the shifted window coincide columnwise
  unfold gcopies
  refine List.flatMap_congr ?_
  intro k _
  unfold gcopy
  have hrange : List.range' (A.length + q) (x - q)
      = (List.range' q (x - q)).map (A.length + ·) := by
    rw [List.range'_eq_map_range, List.range'_eq_map_range, List.map_map]
    refine List.map_congr_left ?_
    intro j _
    simp only [Function.comp_apply]
    omega
  rw [hrange, List.map_map]
  refine List.map_congr_left ?_
  intro j hj
  simp only [Function.comp_apply]
  rw [entry_append_right, entry_append_right, entry_append_right]
  by_cases hg : le0 T q j
  · have hgC : le0 (A ++ T) (A.length + q) (A.length + j) :=
      (le0_append_right A T q j).2 hg
    by_cases hg1 : le1 T q j
    · rw [if_pos ((le1_append_right A T q j).2 hg1), if_pos hg1]
    · rw [if_neg (fun hc => hg1 ((le1_append_right A T q j).1 hc)), if_neg hg1]
  · by_cases hg1 : le1 T q j
    · rw [if_pos ((le1_append_right A T q j).2 hg1), if_pos hg1]
    · rw [if_neg (fun hc => hg1 ((le1_append_right A T q j).1 hc)), if_neg hg1]

/-- **The append `Pred`-mirror**: a trailing column with no parent in the
whole block peels off, leaving the prefix untouched. -/
theorem oper_append_pred (n : ℕ) (hT : T ≠ [])
    (hL : (A ++ T).length - 1 ≠ 0)
    (hnp : ¬ hasParent (A ++ T) (srow (A ++ T) ((A ++ T).length - 1))
      ((A ++ T).length - 1)) :
    (A ++ T)⟦n⟧ = A ++ T.dropLast := by
  classical
  have hdl : (A ++ T).dropLast = A ++ T.dropLast :=
    List.dropLast_append_of_ne_nil hT
  have hlen2 : 1 < (A ++ T).length := by
    have := List.length_append (as := A) (bs := T)
    omega
  by_cases hz : entry (A ++ T) 0 ((A ++ T).length - 1) = 0 ∧
      entry (A ++ T) 1 ((A ++ T).length - 1) = 0 ∧
      entry (A ++ T) 2 ((A ++ T).length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL hz]
    unfold Pred
    rw [if_neg (by omega), hdl]
  · rw [oper_eq_pred_of_noParent n hL hz hnp]
    unfold Pred
    rw [if_neg (by omega), hdl]

end AppendMirror

/-- **The graft mirror**: when the argument's trailing column keeps its parent
inside the argument, the expansion recurses into the argument. -/
theorem oper_graft_inner {M y : TrioSeq} (n : ℕ) (hM : M ≠ []) (hy : y ≠ [])
    (hyL : y.length - 1 ≠ 0)
    (hp : hasParent y (srow y (y.length - 1)) (y.length - 1)) :
    (graft M y)⟦n⟧ = graft M (y⟦n⟧) := by
  classical
  set c := entry M 0 (M.length - 1) with hc
  have hg : ∀ w : TrioSeq, graft M w = M.dropLast ++ shiftr01 c 0 w := by
    intro w
    unfold graft shiftr01
    refine congrArg _ (List.map_congr_left ?_)
    intro p _
    exact Prod.ext rfl (Prod.ext (by dsimp only; omega) rfl)
  have hylen : 0 < y.length := List.length_pos_iff.mpr hy
  have hsL : (shiftr01 c 0 y).length - 1 ≠ 0 := by rw [shiftr01_length]; exact hyL
  have hsne : shiftr01 c 0 y ≠ [] := by
    cases y with
    | nil => exact absurd rfl hy
    | cons a l => simp [shiftr01]
  have hsp : hasParent (shiftr01 c 0 y)
      (srow (shiftr01 c 0 y) ((shiftr01 c 0 y).length - 1))
      ((shiftr01 c 0 y).length - 1) := by
    rw [shiftr01_length, srow_shiftr01]
    exact hasParent_shiftr01.mpr hp
  rw [hg y, hg (y⟦n⟧), oper_append_inner n hsne hsL hsp, oper_shiftr01]


/-- srow of the graft block's trailing column is the argument's. -/
theorem srow_graft_last {M y : TrioSeq} (hM : M ≠ []) (hy : y ≠ []) :
    srow (graft M y) ((graft M y).length - 1) = srow y (y.length - 1) := by
  classical
  set c := entry M 0 (M.length - 1) with hc
  have hg : graft M y = M.dropLast ++ shiftr01 c 0 y := by
    unfold graft shiftr01
    refine congrArg _ (List.map_congr_left ?_)
    intro p _
    exact Prod.ext rfl (Prod.ext (by dsimp only; omega) rfl)
  have hylen : 0 < y.length := List.length_pos_iff.mpr hy
  have hlen : (M.dropLast ++ shiftr01 c 0 y).length - 1
      = M.dropLast.length + (y.length - 1) := by
    rw [List.length_append, shiftr01_length]
    omega
  rw [hg, hlen, srow_append_right, srow_shiftr01]

/-- **The graft `Pred`-mirror**. -/
theorem oper_graft_pred {M y : TrioSeq} (n : ℕ) (hM : M ≠ []) (hy : y ≠ [])
    (hL : (graft M y).length - 1 ≠ 0)
    (hnp : ¬ hasParent (graft M y)
      (srow (graft M y) ((graft M y).length - 1)) ((graft M y).length - 1)) :
    (graft M y)⟦n⟧ = graft M y.dropLast := by
  classical
  set c := entry M 0 (M.length - 1) with hc
  have hg : ∀ w : TrioSeq, graft M w = M.dropLast ++ shiftr01 c 0 w := by
    intro w
    unfold graft shiftr01
    refine congrArg _ (List.map_congr_left ?_)
    intro p _
    exact Prod.ext rfl (Prod.ext (by dsimp only; omega) rfl)
  have hsne : shiftr01 c 0 y ≠ [] := by
    cases y with
    | nil => exact absurd rfl hy
    | cons a l => simp [shiftr01]
  rw [hg y] at hL hnp ⊢
  rw [oper_append_pred n hsne hL hnp, shiftr01_dropLast, ← hg]


/-- **The blocked-case characterization**: if the argument's trailing column has
no parent within the argument but the graft block has one, that parent lies in
the context part.  With `oper_graft_inner` and `oper_graft_pred` this gives the
full trichotomy for the expansion of a graft block. -/
theorem blocked_parent_lt {M y : TrioSeq} (hM : M ≠ []) (hy : y ≠ [])
    (hni : ¬ hasParent y (srow y (y.length - 1)) (y.length - 1))
    (hpG : hasParent (graft M y)
      (srow (graft M y) ((graft M y).length - 1)) ((graft M y).length - 1)) :
    parent (graft M y) (srow (graft M y) ((graft M y).length - 1))
      ((graft M y).length - 1) < M.length - 1 := by
  classical
  set c := entry M 0 (M.length - 1) with hc
  have hg : graft M y = M.dropLast ++ shiftr01 c 0 y := by
    unfold graft shiftr01
    refine congrArg _ (List.map_congr_left ?_)
    intro p _
    exact Prod.ext rfl (Prod.ext (by dsimp only; omega) rfl)
  have hylen : 0 < y.length := List.length_pos_iff.mpr hy
  have hMlen : 0 < M.length := List.length_pos_iff.mpr hM
  set A : TrioSeq := M.dropLast with hA
  set T : TrioSeq := shiftr01 c 0 y with hT
  have hAlen : A.length = M.length - 1 := by rw [hA, List.length_dropLast]
  have hTlen : T.length = y.length := by rw [hT, shiftr01_length]
  set x := y.length - 1 with hx
  have hGx : (graft M y).length - 1 = A.length + x := by
    rw [hg, List.length_append, hTlen]
    omega
  have hsrT : srow T x = srow y x := by rw [hT]; exact srow_shiftr01 y x
  have hsrG : srow (graft M y) ((graft M y).length - 1) = srow y x :=
    srow_graft_last hM hy
  have hniT : ¬ hasParent T (srow y x) x := by
    rw [hT, ← hsrT, hT, srow_shiftr01]
    intro h
    exact hni (hasParent_shiftr01.mp h)
  by_contra hge
  push_neg at hge
  rw [← hAlen] at hge
  have hnr := parent_nextR hpG
  obtain ⟨p', hp'⟩ : ∃ p', parent (graft M y)
      (srow (graft M y) ((graft M y).length - 1)) ((graft M y).length - 1)
      = A.length + p' :=
    ⟨parent (graft M y) (srow (graft M y) ((graft M y).length - 1))
      ((graft M y).length - 1) - A.length, by omega⟩
  rw [hp', hsrG, hGx] at hnr
  have hnrG : nextR (A ++ T) (srow y x) (A.length + p') (A.length + x) := by
    rw [← hg]
    exact hnr
  have hnrT : nextR T (srow y x) p' x :=
    (nextR_append_right A T (srow y x) p' x).1 hnrG
  refine hniT ⟨p', hnrT, ?_⟩
  intro q hq
  have hqG : nextR (graft M y) (srow y x) (A.length + q) (A.length + x) := by
    rw [hg]
    exact (nextR_append_right A T (srow y x) q x).2 hq
  have huniq := hpG.unique (by rw [hsrG, hGx]; exact hqG) (parent_nextR hpG)
  rw [hp'] at huniq
  omega

end TRIO
