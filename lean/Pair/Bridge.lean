import Pair.Wset
import Wset
import Gcopy
import Lcone

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

end PairBridge

end TRIO
