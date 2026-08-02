/-
ArgDom.lean: 引数支配（ホスト非依存の共終性核）。

核の比較器は**心材シフト** `hshift w1 e f`: 行 0 は一様に `+e`、行 1 は
「木の経路上で行 1 が `w1` を超え続ける心材」でのみ `+f`（遮断された
部分木は行 0 のみシフト）。ホスト内では経路補題によりガード付き写像
`(e0 j + e, e1 j + [le1 N r j]·f, e2 j)` と一致する。
-/
import Cofinality

namespace TRIO

open Three
open Classical

/-- The heartwood shift: row 0 uniformly `+e`; row 1 `+f` on the heartwood
(the tree region reachable through columns with row 1 above `w1`). -/
def hshift (w1 e f : ℕ) : TrioSeq → TrioSeq
  | [] => []
  | p :: rest =>
      if w1 < p.2.1 then
        (p.1 + e, p.2.1 + f, p.2.2)
          :: (hshift w1 e f (rest.takeWhile fun q => p.1 < q.1)
              ++ hshift w1 e f (rest.dropWhile fun q => p.1 < q.1))
      else
        (p.1 + e, p.2.1, p.2.2)
          :: (shiftr01 e 0 (rest.takeWhile fun q => p.1 < q.1)
              ++ hshift w1 e f (rest.dropWhile fun q => p.1 < q.1))
  termination_by M => M.length
  decreasing_by
  · exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)

@[simp] theorem hshift_nil (w1 e f : ℕ) : hshift w1 e f [] = [] := by
  rw [hshift]

theorem hshift_cons (w1 e f : ℕ) (p : ℕ × ℕ × ℕ) (rest : TrioSeq) :
    hshift w1 e f (p :: rest)
      = if w1 < p.2.1 then
          (p.1 + e, p.2.1 + f, p.2.2)
            :: (hshift w1 e f (rest.takeWhile fun q => p.1 < q.1)
                ++ hshift w1 e f (rest.dropWhile fun q => p.1 < q.1))
        else
          (p.1 + e, p.2.1, p.2.2)
            :: (shiftr01 e 0 (rest.takeWhile fun q => p.1 < q.1)
                ++ hshift w1 e f (rest.dropWhile fun q => p.1 < q.1)) := by
  rw [hshift]

/-- **The host bridge**: inside a host `M`, the heartwood shift of a sibling
forest `[a, a+l)` under a guarded tree parent `pa` is the guarded map. -/
theorem hshift_gseg {M : TrioSeq} {r e f : ℕ} :
    ∀ (l : ℕ), ∀ {a pa : ℕ}, le1 M r pa → pa < a → a + l ≤ M.length →
      (∀ j, a ≤ j → j < a + l → entry M 0 pa < entry M 0 j) →
      (∀ j, pa < j → j < a → entry M 0 a ≤ entry M 0 j) →
      (List.range' a l).map (fun j =>
          ((entry M 0 j + e,
            entry M 1 j + (if le1 M r j then f else 0),
            entry M 2 j) : ℕ × ℕ × ℕ))
        = hshift (entry M 1 r) e f ((List.range' a l).map fun j =>
            ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)) := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l IH =>
    intro a pa hpa ha hlen hup hpre
    rcases l with - | l
    · show ([] : TrioSeq) = hshift _ e f []
      rw [hshift_nil]
    have hedge : nextrel0 M pa a := by
      refine ⟨by omega, by omega, ha, hup a le_rfl (by omega), ?_⟩
      intro x ⟨hx1, hx2⟩
      exact hpre x hx1 hx2
    have hguard : le1 M r a ↔ entry M 1 r < entry M 1 a := le1_step hpa hedge
    set q : ℕ → Bool := fun j => decide (entry M 0 a < entry M 0 j) with hqdef
    obtain ⟨m, hm, ht, hd, hall, hend⟩ := range'_split_takeWhile q l (a + 1)
    have hqs : ((fun x : ℕ × ℕ × ℕ => decide (entry M 0 a < x.1))
          ∘ fun j => ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)) = q := by
      funext j
      simp only [Function.comp_apply, hqdef]
    -- unfold both sides one step
    simp only [List.range'_succ, List.map_cons]
    rw [hshift_cons]
    simp only [List.takeWhile_map, List.dropWhile_map, hqs, ht, hd]
    have hlsplit : List.range' (a + 1) l
        = List.range' (a + 1) m ++ List.range' (a + 1 + m) (l - m) := by
      rw [← ht, ← hd, List.takeWhile_append_dropWhile]
    rw [hlsplit, List.map_append]
    -- the tail recursion is common to both branches
    have htail : (List.range' (a + 1 + m) (l - m)).map (fun j =>
          ((entry M 0 j + e,
            entry M 1 j + (if le1 M r j then f else 0),
            entry M 2 j) : ℕ × ℕ × ℕ))
        = hshift (entry M 1 r) e f ((List.range' (a + 1 + m) (l - m)).map fun j =>
            ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)) := by
      rcases Nat.eq_or_lt_of_le hm with rfl | hmL
      · rw [Nat.sub_self]
        show ([] : TrioSeq) = hshift _ e f []
        rw [hshift_nil]
      · have hqe := hend hmL
        have he0 : entry M 0 (a + 1 + m) ≤ entry M 0 a := by
          have : q (a + 1 + m) = false := hqe
          simp only [hqdef, decide_eq_false_iff_not, Nat.not_lt] at this
          exact this
        refine IH (l - m) (by omega) hpa (by omega) (by omega) ?_ ?_
        · intro j h1 h2
          exact hup j (by omega) (by omega)
        · intro j h1 h2
          rcases Nat.lt_or_ge j a with hja | hja
          · exact le_trans he0 (hpre j h1 hja)
          · rcases Nat.eq_or_lt_of_le hja with rfl | hja'
            · exact he0
            · have := hall j (by omega) (by omega)
              simp only [hqdef, decide_eq_true_eq] at this
              exact le_trans he0 this.le
    by_cases hthr : entry M 1 r < entry M 1 a
    · rw [if_pos hthr, if_pos (hguard.2 hthr)]
      have hsub : (List.range' (a + 1) m).map (fun j =>
            ((entry M 0 j + e,
              entry M 1 j + (if le1 M r j then f else 0),
              entry M 2 j) : ℕ × ℕ × ℕ))
          = hshift (entry M 1 r) e f ((List.range' (a + 1) m).map fun j =>
              ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)) := by
        refine IH m (by omega) (hguard.2 hthr) (by omega) (by omega) ?_ ?_
        · intro j h1 h2
          have := hall j h1 (by omega)
          simp only [hqdef, decide_eq_true_eq] at this
          exact this
        · intro j h1 h2
          omega
      rw [hsub, htail]
    · rw [if_neg hthr, if_neg (fun h => hthr (hguard.1 h)), Nat.add_zero]
      have hnog : ∀ j, a + 1 ≤ j → j < a + 1 + m → ¬ le1 M r j := by
        intro j h1 h2 hle1
        refine hthr (hguard.1 ?_)
        refine le1_of_le1_subtree (by omega)
          ((rtg1_to_rtg0 hpa.2.2).tail hedge) (by omega) ?_ hle1
        intro x hx1 hx2
        have := hall x (by omega) (by omega)
        simp only [hqdef, decide_eq_true_eq] at this
        exact this
      have hsub : (List.range' (a + 1) m).map (fun j =>
            ((entry M 0 j + e,
              entry M 1 j + (if le1 M r j then f else 0),
              entry M 2 j) : ℕ × ℕ × ℕ))
          = shiftr01 e 0 ((List.range' (a + 1) m).map fun j =>
              ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)) := by
        unfold shiftr01
        rw [List.map_map]
        refine List.map_congr_left ?_
        intro j hj
        have hjb := List.mem_range'_1.1 hj
        simp only [Function.comp_apply]
        rw [if_neg (hnog j hjb.1 (by omega))]
      rw [hsub, htail]

end TRIO
