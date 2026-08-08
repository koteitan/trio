import Pair.Wset
import Wset
import Gcopy
import Lcone
import Wchar

/-!
# ペア数列 → トリオ数列の埋め込み

`GRAFTALL-PLAN` §4.2 の通り、trio の残差 `TowerExp2Root` の `|R| = 1` 基底は

```
[(k*e, v + k*f, 0)]_{k<n} ∈ TRIO.W (2v)
```

＝ **ペア数列の停止性そのもの**である。lean-yapss の証明は `Pair/*` として
取り込んであるので、あとは

```
emb S := S.map (fun p => (p.1, p.2, 0))
```

に沿って `YAPSS.W v` を `TRIO.W (2v)` に移せばよい。

**要点**: 転送では trio 側の `Aop` 節 3 を**使わない**。yapss 側の節 3 は
`domT S m` を持つので `S⟦n⟧ = graft S []` となり、`z = []` のデータだけで
trio 側の節 2 が立つ。これで「trio の `W m'` は埋め込み像より真に大きい」という
量詞のずれを回避できる。
-/

namespace TRIO

open Wset

namespace PairBridge

/-- 行 2 を `0` で埋める埋め込み。 -/
def emb (S : YAPSS.PairSeq) : TrioSeq := S.map (fun p => ((p.1, p.2, 0) : ℕ × ℕ × ℕ))

@[simp] theorem emb_length (S : YAPSS.PairSeq) : (emb S).length = S.length := by
  simp [emb]

theorem emb_getD (S : YAPSS.PairSeq) (j : ℕ) :
    (emb S).getD j ((0, 0, 0) : ℕ × ℕ × ℕ)
      = (((S.getD j ((0, 0) : ℕ × ℕ)).1, (S.getD j ((0, 0) : ℕ × ℕ)).2, 0)) := by
  unfold emb
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : S[j]? with
  | none => simp
  | some p => simp

@[simp] theorem entry_emb0 (S : YAPSS.PairSeq) (j : ℕ) :
    entry (emb S) 0 j = YAPSS.entry S 0 j := by
  unfold entry YAPSS.entry
  rw [emb_getD]
  simp

@[simp] theorem entry_emb1 (S : YAPSS.PairSeq) (j : ℕ) :
    entry (emb S) 1 j = YAPSS.entry S 1 j := by
  unfold entry YAPSS.entry
  rw [emb_getD]
  simp

@[simp] theorem entry_emb2 (S : YAPSS.PairSeq) (j : ℕ) :
    entry (emb S) 2 j = 0 := by
  unfold entry
  rw [emb_getD]
  simp

theorem nextrel0_emb (S : YAPSS.PairSeq) : nextrel0 (emb S) = YAPSS.nextrel0 S := by
  funext a b
  refine propext ?_
  unfold nextrel0 YAPSS.nextrel0
  simp

theorem le0_emb (S : YAPSS.PairSeq) : le0 (emb S) = YAPSS.le0 S := by
  funext a b
  refine propext ?_
  unfold le0 YAPSS.le0
  rw [nextrel0_emb]
  simp

theorem nextrel1_emb (S : YAPSS.PairSeq) : nextrel1 (emb S) = YAPSS.nextrel1 S := by
  funext a b
  refine propext ?_
  unfold nextrel1 YAPSS.nextrel1
  rw [le0_emb]
  simp

theorem le1_emb (S : YAPSS.PairSeq) {a b : ℕ} :
    le1 (emb S) a b ↔ (a < S.length ∧ b < S.length ∧
      Relation.ReflTransGen (YAPSS.nextrel1 S) a b) := by
  unfold le1
  rw [nextrel1_emb]
  simp

theorem srow_emb (S : YAPSS.PairSeq) (j : ℕ) : srow (emb S) j = YAPSS.idx1 S j := by
  unfold srow YAPSS.idx1
  rw [entry_emb2, entry_emb1]
  simp

theorem nextR_emb (S : YAPSS.PairSeq) {i : ℕ} (hi : i ≤ 1) :
    nextR (emb S) i = YAPSS.nextR S i := by
  funext a b
  refine propext ?_
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · show nextrel0 (emb S) a b ↔ YAPSS.nextrel0 S a b
    rw [nextrel0_emb]
  · have hi1 : i = 1 := by omega
    subst hi1
    show nextrel1 (emb S) a b ↔ YAPSS.nextrel1 S a b
    rw [nextrel1_emb]

theorem hasParent_emb (S : YAPSS.PairSeq) {i b : ℕ} (hi : i ≤ 1) :
    hasParent (emb S) i b ↔ YAPSS.hasParent S i b := by
  unfold hasParent YAPSS.hasParent
  rw [nextR_emb S hi]

theorem parent_emb (S : YAPSS.PairSeq) {i b : ℕ} (hi : i ≤ 1) :
    parent (emb S) i b = YAPSS.parent S i b := by
  unfold parent YAPSS.parent
  rw [nextR_emb S hi]

@[simp] theorem emb_take (S : YAPSS.PairSeq) (k : ℕ) :
    (emb S).take k = emb (S.take k) := by
  simp [emb, List.map_take]

@[simp] theorem emb_dropLast (S : YAPSS.PairSeq) :
    (emb S).dropLast = emb S.dropLast := by
  rw [List.dropLast_eq_take, List.dropLast_eq_take, emb_length, emb_take]

theorem Pred_emb (S : YAPSS.PairSeq) : Pred (emb S) = emb (YAPSS.Pred S) := by
  unfold Pred YAPSS.Pred
  by_cases h : S.length ≤ 1
  · rw [if_pos (by simpa using h), if_pos h]
  · rw [if_neg (by simpa using h), if_neg h, emb_dropLast]

@[simp] theorem emb_append (A B : YAPSS.PairSeq) : emb (A ++ B) = emb A ++ emb B := by
  simp [emb]

theorem emb_flatMap {α : Type _} (l : List α) (f : α → YAPSS.PairSeq) :
    emb (l.flatMap f) = l.flatMap (fun x => emb (f x)) := by
  simp [emb, List.map_flatMap]

theorem emb_map {α : Type _} (l : List α) (g : α → ℕ × ℕ) :
    emb (l.map g) = l.map (fun x => (((g x).1, (g x).2, 0) : ℕ × ℕ × ℕ)) := by
  simp [emb, List.map_map]

/-- **The row-0 ascension guard is vacuous inside the window.**  Every column of
`[j0, j1)` is strictly deeper than `j0`, hence a row-0 descendant of it, so
trio's `A_x0` guard in `oper` always fires. -/
theorem le0_window {M : TrioSeq} {j0 j1 : ℕ} (hb1 : j1 < M.length)
    (hch : Relation.ReflTransGen (nextrel0 M) j0 j1) :
    ∀ j, j0 ≤ j → j < j1 → le0 M j0 j := by
  intro j hj0 hj1
  have hdeep : ∀ l, j0 < l → l ≤ j → entry M 0 j0 < entry M 0 l := by
    intro l hl0 hl1
    exact window_of_rtg0 hch hb1 l hl0 (by omega)
  exact ⟨by omega, by omega, rtg0_of_window (by omega) hj0 hdeep⟩

/-- **The expansions agree.**  `d1 = 0` on both sides (`idx1 ≤ 1`), the row-2
component is constantly `0`, and trio's row-0 guard `A_x0` is vacuous inside the
window by `le0_window`. -/
theorem oper_emb (S : YAPSS.PairSeq) (n : ℕ) : (emb S)⟦n⟧ = emb (S⟦n⟧) := by
  classical
  by_cases hL : S.length - 1 = 0
  · rw [oper_eq_self_of_short n (by simpa using hL), YAPSS.oper_eq_self_of_short n hL]
  · have hLe : (emb S).length - 1 ≠ 0 := by simpa using hL
    have hlen : (emb S).length - 1 = S.length - 1 := by simp
    by_cases hz : YAPSS.entry S 0 (S.length - 1) = 0 ∧ YAPSS.entry S 1 (S.length - 1) = 0
    · have hze : entry (emb S) 0 ((emb S).length - 1) = 0 ∧
          entry (emb S) 1 ((emb S).length - 1) = 0 ∧
          entry (emb S) 2 ((emb S).length - 1) = 0 := by
        rw [hlen, entry_emb0, entry_emb1, entry_emb2]
        exact ⟨hz.1, hz.2, rfl⟩
      rw [oper_eq_pred_of_zero n hLe hze, YAPSS.oper_eq_pred_of_zero n hL hz, Pred_emb]
    · have hze : ¬ (entry (emb S) 0 ((emb S).length - 1) = 0 ∧
          entry (emb S) 1 ((emb S).length - 1) = 0 ∧
          entry (emb S) 2 ((emb S).length - 1) = 0) := by
        rw [hlen, entry_emb0, entry_emb1, entry_emb2]
        tauto
      have hi1 : YAPSS.idx1 S (S.length - 1) ≤ 1 := by
        unfold YAPSS.idx1; split <;> omega
      have hsr : srow (emb S) ((emb S).length - 1) = YAPSS.idx1 S (S.length - 1) := by
        rw [hlen, srow_emb]
      by_cases hp : YAPSS.hasParent S (YAPSS.idx1 S (S.length - 1)) (S.length - 1)
      · have hpe : hasParent (emb S) (srow (emb S) ((emb S).length - 1))
            ((emb S).length - 1) := by
          rw [hsr, hlen, hasParent_emb S hi1]; exact hp
        have hnr0 := parent_nextR hpe
        rw [hsr, hlen, parent_emb S hi1, nextR_emb S hi1] at hnr0
        rw [oper_bad_unfold n hLe hze hpe, YAPSS.oper_bad_unfold n hL hz hp,
          hsr, hlen, parent_emb S hi1, emb_append, emb_flatMap]
        set j1 := S.length - 1 with hj1
        set j0 := YAPSS.parent S (YAPSS.idx1 S j1) j1 with hj0
        have hchain : Relation.ReflTransGen (nextrel0 (emb S)) j0 j1 := by
          unfold YAPSS.nextR at hnr0
          rw [nextrel0_emb]
          split at hnr0
          · exact Relation.ReflTransGen.single hnr0
          · exact hnr0.2.2.2.2.1.2.2
        have hd1 : ¬ (1 < YAPSS.idx1 S j1) := by omega
        congr 1
        · rw [emb_take]
        refine List.flatMap_congr ?_
        intro k _
        rw [emb_map]
        refine List.map_congr_left ?_
        intro j hj
        rw [List.mem_range'] at hj
        have hg0 : le0 (emb S) j0 j :=
          le0_window (by simp; omega) hchain j (by omega) (by omega)
        simp only [if_pos hg0, if_neg hd1, entry_emb0, entry_emb1, entry_emb2,
          Nat.mul_zero, ite_self, Nat.add_zero]
      · have hpe : ¬ hasParent (emb S) (srow (emb S) ((emb S).length - 1))
            ((emb S).length - 1) := by
          rw [hsr, hlen, hasParent_emb S hi1]; exact hp
        rw [oper_eq_pred_of_noParent n hLe hze hpe,
          YAPSS.oper_eq_pred_of_noParent n hL hz hp, Pred_emb]

/-- **★ The transfer.**  `YAPSS.W v` lands in `TRIO.W (2v)` under the embedding.

The proof uses trio's `Aop` clauses 1 and 2 ONLY.  yapss's clause 3 carries
`domT S m`, so `S⟦n⟧ = graft S []` and the `z = []` instance of its datum already
gives trio's clause 2; that is how the quantifier mismatch (trio's `W m'` is far
bigger than the embedded `YAPSS.W m`) is avoided. -/
theorem emb_mem_W {v : ℕ} {S : YAPSS.PairSeq} (h : S ∈ YAPSS.Wset.W v) :
    emb S ∈ Wset.W (2 * v) := by
  classical
  have hsub : YAPSS.Wset.W v ⊆ {T : YAPSS.PairSeq | emb T ∈ Wset.W (2 * v)} := by
    refine YAPSS.Wset.A2' ?_
    intro T A
    show emb T ∈ Wset.W (2 * v)
    rcases A with ⟨hl, hw⟩ | ⟨-, hop⟩ | ⟨m, hm, hd, hgr⟩
    · refine Wset.A1_intro (Or.inl ⟨by simpa using hl, ?_⟩)
      unfold Wset.lev
      rw [entry_emb1, entry_emb2, hw]
    · refine Wset.A1_intro (Or.inr (Or.inl (fun n hn => ?_)))
      rw [oper_emb]
      exact hop n hn
    · rcases Nat.lt_or_ge T.length 2 with hshort | hlong
      · -- a single column: `domT T m` pins its row 1 to `m + 1 ≤ v`
        have hTne : T ≠ [] := by
          intro hc
          rw [hc] at hd
          exact YAPSS.Wset.not_domT_nil m hd
        have hT1 : T.length = 1 := by
          have := List.length_pos_iff.mpr hTne
          omega
        have hw : YAPSS.entry T 1 0 = m + 1 := by
          have := hd.1
          rw [hT1] at this
          simpa using this
        obtain ⟨q, hq⟩ : ∃ q, T = [q] := List.length_eq_one_iff.mp hT1
        have hqe : q = (q.1, q.2) := rfl
        rw [hq] at hw ⊢
        show emb [q] ∈ Wset.W (2 * v)
        have : emb [q] = [((q.1, q.2, 0) : ℕ × ℕ × ℕ)] := by simp [emb]
        rw [this]
        refine singleton_mem_W ?_
        have : q.2 = m + 1 := by
          unfold YAPSS.entry at hw
          simpa using hw
        omega
      · refine Wset.A1_intro (Or.inr (Or.inl (fun n hn => ?_)))
        rw [oper_emb, YAPSS.Wset.oper_eq_graft_nil_of_domT (n := n) (by omega) hd]
        exact hgr [] (YAPSS.Wset.W_nil m) YAPSS.Wset.based_nil
  exact hsub h

/-- **★★ (PAIR)** — every pair block planted under a root of row-1 value `v`
lands in trio's `W (2v)`.

This is the pair-sequence COLLAPSE, transported verbatim from lean-yapss
(`YAPSS.Wset.mem_Wstar` is unconditional there).  `GRAFTALL-PLAN` §4.2 shows it
is on trio's critical path: the `|R| = 1` base of `TowerExp2Root` is exactly a
pair diagonal at the root's own stage. -/
theorem pair_plant_mem_W (v : ℕ) (R : YAPSS.PairSeq) (hR : YAPSS.Wset.argOK R) :
    emb (((0, v) : ℕ × ℕ) :: R) ∈ Wset.W (2 * v) :=
  emb_mem_W (YAPSS.Wset.mem_Wstar R hR v)

/-- **★★ The pair diagonal at the root's own stage.**  With `0 < e` every
column but the root sits strictly below it, so `(PAIR)` applies.  This is the
`|R| = 1, z = 0` base case of `TowerExp2Root`. -/
theorem diag_mem_W (v e f n : ℕ) (he : 0 < e) :
    ((List.range n).map (fun k => ((k * e, v + k * f, 0) : ℕ × ℕ × ℕ)))
      ∈ Wset.W (2 * v) := by
  classical
  cases n with
  | zero => simpa using Wset.W_nil (2 * v)
  | succ n =>
      have hr : List.range (n + 1) = 0 :: List.range' 1 n := by
        rw [List.range_eq_range', List.range'_succ]
      have hR : YAPSS.Wset.argOK ((List.range' 1 n).map
          (fun k => ((k * e, v + k * f) : ℕ × ℕ))) := by
        intro p hp
        rw [List.mem_map] at hp
        obtain ⟨k, hk, rfl⟩ := hp
        rw [List.mem_range'] at hk
        have hk1 : 1 ≤ k := by obtain ⟨i, -, rfl⟩ := hk; omega
        exact Nat.mul_pos (by omega) he
      have := pair_plant_mem_W v _ hR
      rw [hr]
      convert this using 2
      simp [emb]

end PairBridge

end TRIO
