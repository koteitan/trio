/-
H12Export.lean: **L3 が `L106.lean` に写すための依存閉包**（H12 ⟹ L3）。

`L106.lean` は `H12H2.lean` を import できない（作業ファイルなので）。
⟹ **写す**しかなく、依存が 1 本でも欠けると通らない。
⟹ **このファイルは「必要なものだけ」を集めて緑にしたもの。緑 ＝ 依存閉包に欠けが無い証明。**

⚠ 名前の衝突は 1 件も入っていない（`h12_row2_const_mTower` /
`entry2_mTower_blockRoot`（L3 の `mTower_entry2_root` と同じ）は**含めていない**）。
⚠ `H12H2.lean` の `h2` 系・反例・`snocStep_outOfCone` 系は**要らないので入れていない**。
-/
import L105Cap

namespace TRIO
namespace H12Export

open Wset
open L105

/-- `nextrel2` は接頭辞と行き来する（終点が接頭辞に入っていれば）。 -/
theorem nextrel2_take_iff {M : TrioSeq} {l a b : ℕ} (hl : l ≤ M.length) (hb : b < l) :
    nextrel2 (M.take l) a b ↔ nextrel2 M a b := by
  have hlen : (M.take l).length = l := by rw [List.length_take]; omega
  constructor
  · rintro ⟨hal, hbl, hab, hent, hle, hmin⟩
    rw [hlen] at hal hbl
    refine ⟨by omega, by omega, hab, ?_, (le1_take hl hb).mp hle, ?_⟩
    · rwa [entry_take (show a < l by omega), entry_take hb] at hent
    · intro j hj
      have hjb : j ≤ b := le1_le' hj.2
      have hres := hmin j ⟨hj.1, (le1_take hl (show b < l from hb)).mpr hj.2⟩
      rwa [entry_take hb, entry_take (show j < l by omega)] at hres
  · rintro ⟨hal, hbl, hab, hent, hle, hmin⟩
    refine ⟨by rw [hlen]; omega, by rw [hlen]; omega, hab, ?_,
      (le1_take hl hb).mpr hle, ?_⟩
    · rw [entry_take (show a < l by omega), entry_take hb]; exact hent
    · intro j hj
      have hjl : j < l := by
        have := (le1_take hl hb).mp hj.2
        have : j ≤ b := le1_le' this
        omega
      have hres := hmin j ⟨hj.1, (le1_take hl hb).mp hj.2⟩
      rw [entry_take hb, entry_take hjl]
      exact hres

/-- ⟹ 行 2 の `hasParent` も接頭辞と行き来する。 -/
theorem hasParent_two_take {M : TrioSeq} {l p : ℕ} (hl : l ≤ M.length) (hp : p < l) :
    hasParent (M.take l) 2 p ↔ hasParent M 2 p := by
  have hnR : ∀ (N : TrioSeq) (j : ℕ), nextR N 2 j p ↔ nextrel2 N j p := by
    intro N j; unfold nextR; rw [if_neg (by omega), if_neg (by omega)]
  unfold hasParent
  constructor
  · rintro ⟨j0, hj0, hu⟩
    refine ⟨j0, (hnR M j0).mpr ((nextrel2_take_iff hl hp).mp ((hnR _ j0).mp hj0)),
      fun y hy => hu y ((hnR _ y).mpr ((nextrel2_take_iff hl hp).mpr ((hnR M y).mp hy)))⟩
  · rintro ⟨j0, hj0, hu⟩
    refine ⟨j0, (hnR _ j0).mpr ((nextrel2_take_iff hl hp).mpr ((hnR M j0).mp hj0)),
      fun y hy => hu y ((hnR M y).mpr ((nextrel2_take_iff hl hp).mp ((hnR _ y).mp hy)))⟩

/-- `(A ++ B).take (|A| + m) = A ++ B.take m`（core に この形が無いので自前）。 -/
theorem take_append_add (A B : TrioSeq) (m : ℕ) :
    (A ++ B).take (A.length + m) = A ++ B.take m := by
  induction A with
  | nil => simp
  | cons a A' ih =>
      simp only [List.cons_append, List.length_cons]
      rw [show A'.length + 1 + m = (A'.length + m) + 1 from by omega,
        List.take_succ_cons, ih]

/-- **位置合わせ**: `hstep` の主語は塔の接頭辞そのもの。 -/
theorem mTower_append_take (Q : TrioSeq) (d e n j : ℕ) :
    mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)
      = (mTower Q d e (n + 1)).take (n * Q.length + (j + 1)) := by
  have hTlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  rw [mTower_succ, ← hTlen, take_append_add]

/-- ★★★★★★ **錐の外の列の行 2 の親は、必ず同じブロックの中**（前のブロックからは来ない）。 -/
theorem outOfCone_nextrel2_sameBlock {M : TrioSeq} {d e n' q a : ℕ}
    (hM2 : 2 ≤ M.length) (hd1pos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hq : q < M.dropLast.length) (hq1 : 0 < q)
    (hout : ¬ le1 M 0 (0 + q))
    (h : nextrel2 (mTower M.dropLast d e (n' + 1)) a
      ((mTower M.dropLast d e n').length + q)) :
    (mTower M.dropLast d e n').length ≤ a := by
  have hAlen : (mTower M.dropLast d e n').length = n' * M.dropLast.length := by
    rw [mTower_length]
  rw [hAlen] at h ⊢
  exact le1_mTower_in_block (n := n' + 1) (k := n') hM2 hd1pos hd0e hr0 hlp
    (by omega) hq hq1 hout a h.2.2.2.2.1.2.2

/-- ⟹ **`hasParent` の言葉で**: 錐の外の列が塔で親を持つなら、その親は同じブロック。 -/
theorem outOfCone_parent_sameBlock {M : TrioSeq} {d e n' q : ℕ}
    (hM2 : 2 ≤ M.length) (hd1pos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hq : q < M.dropLast.length) (hq1 : 0 < q)
    (hout : ¬ le1 M 0 (0 + q))
    (hp : hasParent (mTower M.dropLast d e (n' + 1)) 2
      ((mTower M.dropLast d e n').length + q)) :
    (mTower M.dropLast d e n').length
      ≤ parent (mTower M.dropLast d e (n' + 1)) 2
        ((mTower M.dropLast d e n').length + q) := by
  have hnr := parent_nextR hp
  have h2 : nextrel2 (mTower M.dropLast d e (n' + 1))
      (parent (mTower M.dropLast d e (n' + 1)) 2
        ((mTower M.dropLast d e n').length + q))
      ((mTower M.dropLast d e n').length + q) := by
    unfold nextR at hnr
    rw [if_neg (by omega), if_neg (by omega)] at hnr
    exact hnr
  exact outOfCone_nextrel2_sameBlock hM2 hd1pos hd0e hr0 hlp hq hq1 hout h2

/-- `parent`（行 2）は接頭辞と一致する。 -/
theorem parent_two_take {M : TrioSeq} {l p : ℕ} (hl : l ≤ M.length) (hp : p < l)
    (h : hasParent M 2 p) :
    parent (M.take l) 2 p = parent M 2 p := by
  have hnR : ∀ (N : TrioSeq) (j : ℕ), nextR N 2 j p ↔ nextrel2 N j p := by
    intro N j; unfold nextR; rw [if_neg (by omega), if_neg (by omega)]
  have ht : hasParent (M.take l) 2 p := (hasParent_two_take hl hp).mpr h
  refine ht.unique (parent_nextR ht) ?_
  exact (hnR _ _).mpr ((nextrel2_take_iff hl hp).mpr ((hnR M _).mp (parent_nextR h)))

/-- ★ **錐の外の列の行 1 の親も、必ず同じブロックの中**。 -/
theorem outOfCone_nextrel1_sameBlock {M : TrioSeq} {d e n' q a : ℕ}
    (hM2 : 2 ≤ M.length) (hd1pos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hq : q < M.dropLast.length) (hq1 : 0 < q)
    (hout : ¬ le1 M 0 (0 + q))
    (h : nextrel1 (mTower M.dropLast d e (n' + 1)) a
      ((mTower M.dropLast d e n').length + q)) :
    (mTower M.dropLast d e n').length ≤ a := by
  have hAlen : (mTower M.dropLast d e n').length = n' * M.dropLast.length := by
    rw [mTower_length]
  rw [hAlen] at h ⊢
  exact le1_mTower_in_block (n := n' + 1) (k := n') hM2 hd1pos hd0e hr0 hlp
    (by omega) hq hq1 hout a (Relation.ReflTransGen.single h)

/-- ⟹ `hasParent` の言葉で（行 1）。 -/
theorem outOfCone_parent_one_sameBlock {M : TrioSeq} {d e n' q : ℕ}
    (hM2 : 2 ≤ M.length) (hd1pos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hq : q < M.dropLast.length) (hq1 : 0 < q)
    (hout : ¬ le1 M 0 (0 + q))
    (hp : hasParent (mTower M.dropLast d e (n' + 1)) 1
      ((mTower M.dropLast d e n').length + q)) :
    (mTower M.dropLast d e n').length
      ≤ parent (mTower M.dropLast d e (n' + 1)) 1
        ((mTower M.dropLast d e n').length + q) := by
  have hnr := parent_nextR hp
  have h1 : nextrel1 (mTower M.dropLast d e (n' + 1))
      (parent (mTower M.dropLast d e (n' + 1)) 1
        ((mTower M.dropLast d e n').length + q))
      ((mTower M.dropLast d e n').length + q) := by
    unfold nextR at hnr
    rw [if_neg (by omega), if_pos rfl] at hnr
    exact hnr
  exact outOfCone_nextrel1_sameBlock hM2 hd1pos hd0e hr0 hlp hq hq1 hout h1

/-- ★★★★★★★ **ブロックの根は行 0 の壁**: 塔の第 `n` ブロックの `j > 0` 番目の列の
行 0 の親は、必ず同じブロックの中。（錐の中か外かによらない。） -/
theorem window_row0_sameBlock {Q : TrioSeq} {d e n j a : ℕ}
    (hQ0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hj : j < Q.length) (hj1 : 0 < j)
    (h : nextrel0 (mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      a (n * Q.length + j)) :
    n * Q.length ≤ a := by
  rcases Nat.lt_or_ge a (n * Q.length) with hlt | hge
  swap
  · exact hge
  exfalso
  have hTlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have hE : ∀ i, i < j + 1 → i < Q.length →
      entry (mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 0
        (n * Q.length + i) = entry Q 0 i + d * n := by
    intro i hi1 hi2
    rw [show n * Q.length + i = (mTower Q d e n).length + i from by rw [hTlen],
      entry_append_right, entry_take hi1, entry0_Lift1, entry0_shiftr01 hi2]
  have hmin := h.2.2.2.2 (n * Q.length) ⟨hlt, by omega⟩
  have h0 : entry (mTower Q d e n
      ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 0 (n * Q.length)
      = entry Q 0 0 + d * n := by
    simpa using hE 0 (by omega) (by omega)
  rw [hE j (by omega) hj, h0] at hmin
  have := hQ0 j hj1 hj
  omega

/-- ⟹ `hasParent` の言葉で（行 0）。 -/
theorem window_row0_parent {Q : TrioSeq} {d e n j : ℕ}
    (hQ0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hj : j < Q.length) (hj1 : 0 < j)
    (hp : hasParent (mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 0
      (n * Q.length + j)) :
    n * Q.length ≤ parent (mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 0
      (n * Q.length + j) := by
  have hnr := parent_nextR hp
  have h0 : nextrel0 (mTower Q d e n
      ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (parent (mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 0
        (n * Q.length + j))
      (n * Q.length + j) := by
    unfold nextR at hnr
    rw [if_pos rfl] at hnr
    exact hnr
  exact window_row0_sameBlock hQ0 hj hj1 h0

/-- `nextrel1` は接頭辞と行き来する。 -/
theorem nextrel1_take_iff {M : TrioSeq} {l a b : ℕ} (hl : l ≤ M.length) (hb : b < l) :
    nextrel1 (M.take l) a b ↔ nextrel1 M a b := by
  have hlen : (M.take l).length = l := by rw [List.length_take]; omega
  constructor
  · rintro ⟨hal, hbl, hab, hent, hle, hmin⟩
    rw [hlen] at hal hbl
    refine ⟨by omega, by omega, hab, ?_, (le0_take hl hb).mp hle, ?_⟩
    · rwa [entry_take (show a < l by omega), entry_take hb] at hent
    · intro j hj
      have hjb : j ≤ b := le0_le' hj.2
      have hres := hmin j ⟨hj.1, (le0_take hl hb).mpr hj.2⟩
      rwa [entry_take hb, entry_take (show j < l by omega)] at hres
  · rintro ⟨hal, hbl, hab, hent, hle, hmin⟩
    refine ⟨by rw [hlen]; omega, by rw [hlen]; omega, hab, ?_,
      (le0_take hl hb).mpr hle, ?_⟩
    · rw [entry_take (show a < l by omega), entry_take hb]; exact hent
    · intro j hj
      have hjl : j < l := by
        have h1 := (le0_take hl hb).mp hj.2
        have h2 : j ≤ b := le0_le' h1
        omega
      have hres := hmin j ⟨hj.1, (le0_take hl hb).mp hj.2⟩
      rw [entry_take hb, entry_take hjl]
      exact hres

/-- ⟹ 行 1 の `hasParent` も接頭辞と行き来する。 -/
theorem hasParent_one_take {M : TrioSeq} {l p : ℕ} (hl : l ≤ M.length) (hp : p < l) :
    hasParent (M.take l) 1 p ↔ hasParent M 1 p := by
  have hnR : ∀ (N : TrioSeq) (j : ℕ), nextR N 1 j p ↔ nextrel1 N j p := by
    intro N j; unfold nextR; rw [if_neg (by omega), if_pos rfl]
  unfold hasParent
  constructor
  · rintro ⟨j0, hj0, hu⟩
    exact ⟨j0, (hnR M j0).mpr ((nextrel1_take_iff hl hp).mp ((hnR _ j0).mp hj0)),
      fun y hy => hu y ((hnR _ y).mpr ((nextrel1_take_iff hl hp).mpr ((hnR M y).mp hy)))⟩
  · rintro ⟨j0, hj0, hu⟩
    exact ⟨j0, (hnR _ j0).mpr ((nextrel1_take_iff hl hp).mpr ((hnR M j0).mp hj0)),
      fun y hy => hu y ((hnR M y).mpr ((nextrel1_take_iff hl hp).mp ((hnR _ y).mp hy)))⟩

/-- ⟹ 行 1 の `parent` も接頭辞と一致する。 -/
theorem parent_one_take {M : TrioSeq} {l p : ℕ} (hl : l ≤ M.length) (hp : p < l)
    (h : hasParent M 1 p) :
    parent (M.take l) 1 p = parent M 1 p := by
  have hnR : ∀ (N : TrioSeq) (j : ℕ), nextR N 1 j p ↔ nextrel1 N j p := by
    intro N j; unfold nextR; rw [if_neg (by omega), if_pos rfl]
  have ht : hasParent (M.take l) 1 p := (hasParent_one_take hl hp).mpr h
  refine ht.unique (parent_nextR ht) ?_
  exact (hnR _ _).mpr ((nextrel1_take_iff hl hp).mpr ((hnR M _).mp (parent_nextR h)))

open Classical in
/-- ★ **錐の外の `srow = 1` の列でも、親が居るなら窓は `< |Q|`。** -/
theorem window_of_outOfCone_one {M : TrioSeq} {d e n j : ℕ}
    (hM2 : 2 ≤ M.length) (hd1pos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hj : j < M.dropLast.length) (hj1 : 0 < j)
    (hout : ¬ le1 M 0 (0 + j))
    (hpar0 : hasParent (mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)) 1
      (n * M.dropLast.length + j)) :
    n * M.dropLast.length
      ≤ parent (mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)) 1
        (n * M.dropLast.length + j) := by
  have hTlen : (mTower M.dropLast d e n).length = n * M.dropLast.length :=
    mTower_length M.dropLast d e n
  rw [mTower_append_take] at hpar0 ⊢
  have hle : n * M.dropLast.length + (j + 1)
      ≤ (mTower M.dropLast d e (n + 1)).length := by
    rw [mTower_length, Nat.succ_mul]; omega
  have hlt : n * M.dropLast.length + j < n * M.dropLast.length + (j + 1) := by omega
  have hfull : hasParent (mTower M.dropLast d e (n + 1)) 1
      (n * M.dropLast.length + j) := (hasParent_one_take hle hlt).mp hpar0
  rw [parent_one_take hle hlt hfull]
  have := outOfCone_parent_one_sameBlock (n' := n) hM2 hd1pos hd0e hr0 hlp hj hj1 hout
    (by rwa [hTlen])
  rwa [hTlen] at this

/-- 塔の第 `n` ブロックの `j` 番目の列の行 2 は `Q` のそれと同じ。 -/
theorem entry2_block (Q : TrioSeq) (d e n j : ℕ) (_hj : j < Q.length) :
    entry (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 2
      (n * Q.length + j) = entry Q 2 j := by
  have hTlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  rw [show n * Q.length + j = (mTower Q d e n).length + j from by rw [hTlen],
    entry_append_right, entry_take (by omega), entry2_Lift1, entry2_shiftr01]

open Classical in
/-- 行 2 版（素の `2` の形）。 -/
theorem window_of_outOfCone_two {M : TrioSeq} {d e n j : ℕ}
    (hM2 : 2 ≤ M.length) (hd1pos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hj : j < M.dropLast.length) (hj1 : 0 < j)
    (hout : ¬ le1 M 0 (0 + j))
    (hpar0 : hasParent (mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)) 2
      (n * M.dropLast.length + j)) :
    n * M.dropLast.length
      ≤ parent (mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)) 2
        (n * M.dropLast.length + j) := by
  have hTlen : (mTower M.dropLast d e n).length = n * M.dropLast.length :=
    mTower_length M.dropLast d e n
  rw [mTower_append_take] at hpar0 ⊢
  have hle : n * M.dropLast.length + (j + 1)
      ≤ (mTower M.dropLast d e (n + 1)).length := by
    rw [mTower_length, Nat.succ_mul]; omega
  have hlt : n * M.dropLast.length + j < n * M.dropLast.length + (j + 1) := by omega
  have hfull : hasParent (mTower M.dropLast d e (n + 1)) 2
      (n * M.dropLast.length + j) := (hasParent_two_take hle hlt).mp hpar0
  rw [parent_two_take hle hlt hfull]
  have := outOfCone_parent_sameBlock (n' := n) hM2 hd1pos hd0e hr0 hlp hj hj1 hout
    (by rwa [hTlen])
  rwa [hTlen] at this

open Classical in
/-- ★★★★★★★★ **錐の外の列は、`srow` が何であっても窓が `< |Q|`。**
⟹ `hstep` の窓の前提に **`le1 Q 0 j` は要らない**。 -/
theorem window_of_outOfCone_all {M : TrioSeq} {d e n j : ℕ}
    (hM2 : 2 ≤ M.length) (hd1pos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hj : j < M.dropLast.length) (hj1 : 0 < j)
    (hout : ¬ le1 M 0 (0 + j))
    (hpar0 : hasParent (mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
      (srow (mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
        (n * M.dropLast.length + j))
      (n * M.dropLast.length + j)) :
    n * M.dropLast.length
      ≤ parent (mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
        (srow (mTower M.dropLast d e n
            ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
          (n * M.dropLast.length + j))
        (n * M.dropLast.length + j) := by
  -- `Q = M.dropLast` の上の `hr0`
  have hQ0 : ∀ l, 0 < l → l < M.dropLast.length →
      entry M.dropLast 0 0 < entry M.dropLast 0 l := by
    intro l hl0 hl1
    have hdl : M.dropLast.length = M.length - 1 := List.length_dropLast
    rw [hdl] at hl1
    rw [List.dropLast_eq_take, entry_take (show (0 : ℕ) < M.length - 1 by omega),
      entry_take hl1]
    exact hr0 l hl0 (by omega)
  by_cases h2 : 0 < entry (mTower M.dropLast d e n
      ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)) 2
      (n * M.dropLast.length + j)
  · have hs : srow (mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
        (n * M.dropLast.length + j) = 2 := by unfold srow; rw [if_pos h2]
    rw [hs] at hpar0 ⊢
    exact window_of_outOfCone_two hM2 hd1pos hd0e hr0 hlp hj hj1 hout hpar0
  · by_cases h1 : 0 < entry (mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)) 1
        (n * M.dropLast.length + j)
    · have hs : srow (mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
          (n * M.dropLast.length + j) = 1 := by
        unfold srow; rw [if_neg h2, if_pos h1]
      rw [hs] at hpar0 ⊢
      exact window_of_outOfCone_one hM2 hd1pos hd0e hr0 hlp hj hj1 hout hpar0
    · have hs : srow (mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
          (n * M.dropLast.length + j) = 0 := by
        unfold srow; rw [if_neg h2, if_neg h1]
      rw [hs] at hpar0 ⊢
      exact window_row0_parent hQ0 hj hj1 hpar0

/-- 塔の第 `k` ブロックの `i` 番目の列の行 0。 -/
theorem entry0_mTower_block (Q : TrioSeq) (d e : ℕ) :
    ∀ (n k i : ℕ), k < n → i < Q.length →
      entry (mTower Q d e n) 0 (k * Q.length + i) = entry Q 0 i + d * k := by
  intro n
  induction n with
  | zero => intro k i hk _; omega
  | succ n ih =>
      intro k i hk hi
      rw [mTower_succ]
      rcases Nat.lt_or_ge k n with hkn | hkn
      · have hlt : k * Q.length + i < (mTower Q d e n).length := by
          rw [mTower_length]
          calc k * Q.length + i < k * Q.length + Q.length := by omega
            _ = (k + 1) * Q.length := by rw [Nat.succ_mul]
            _ ≤ n * Q.length := Nat.mul_le_mul_right _ (by omega)
        rw [entry_append_left _ _ hlt]
        exact ih k i hkn hi
      · have hk0 : k = n := by omega
        subst hk0
        rw [show k * Q.length + i = (mTower Q d e k).length + i from by
            rw [mTower_length],
          entry_append_right, entry0_Lift1, entry0_shiftr01 hi]

/-- 塔の第 `k` ブロックの**根**の行 1（根は自分の錐の中なので持ち上がる）。 -/
theorem entry1_mTower_blockRoot {Q : TrioSeq} (hQne : Q ≠ []) (d e : ℕ) :
    ∀ (n k : ℕ), k < n →
      entry (mTower Q d e n) 1 (k * Q.length) = entry Q 1 0 + e * k := by
  intro n
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
      intro k hk
      rw [mTower_succ]
      rcases Nat.lt_or_ge k n with hkn | hkn
      · have hQ1 : 0 < Q.length := List.length_pos_iff.mpr hQne
        have hlt : k * Q.length < (mTower Q d e n).length := by
          rw [mTower_length]
          calc k * Q.length < k * Q.length + Q.length := by omega
            _ = (k + 1) * Q.length := by rw [Nat.succ_mul]
            _ ≤ n * Q.length := Nat.mul_le_mul_right _ (by omega)
        rw [entry_append_left _ _ hlt]
        exact ih k hkn
      · have hk0 : k = n := by omega
        subst hk0
        have hsne : shiftr01 (d * k) 0 Q ≠ [] := by
          intro hc
          have : (shiftr01 (d * k) 0 Q).length = 0 := by rw [hc]; rfl
          rw [shiftr01_length] at this
          exact hQne (List.length_eq_zero_iff.mp this)
        rw [show k * Q.length = (mTower Q d e k).length + 0 from by
            rw [mTower_length]; omega,
          entry_append_right, L53.entry1_Lift1_zero hsne, entry1_shiftr01]

/-- ★ **ブロック `k` の根から次のブロックの根まで、行 0 の鎖が通る**（`rtg0_of_window`）。 -/
theorem rtg0_blockRoot_succ {Q : TrioSeq} {d e n k : ℕ}
    (hQne : Q ≠ []) (hd : 0 < d) (hk : k + 1 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) :
    Relation.ReflTransGen (nextrel0 (mTower Q d e n))
      (k * Q.length) ((k + 1) * Q.length) := by
  have hQ1 : 0 < Q.length := List.length_pos_iff.mpr hQne
  have hTlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have hroot : entry (mTower Q d e n) 0 (k * Q.length) = entry Q 0 0 + d * k := by
    have := entry0_mTower_block Q d e n k 0 (by omega) hQ1
    rwa [Nat.add_zero] at this
  refine rtg0_of_window (M := mTower Q d e n) (a := k * Q.length)
    (show (k + 1) * Q.length < (mTower Q d e n).length from by
      rw [hTlen]; exact Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl _) hQ1)
    (by rw [Nat.succ_mul]; omega) ?_
  intro l hl0 hl1
  rw [hroot]
  rcases Nat.lt_or_ge l ((k + 1) * Q.length) with hlk | hlk
  · -- 第 `k` ブロックの内側の列
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < Q.length ∧ l = k * Q.length + i := by
      refine ⟨l - k * Q.length, ?_, by omega⟩
      have : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
      omega
    rw [entry0_mTower_block Q d e n k i (by omega) hi]
    have := hr0 i (by omega) hi
    omega
  · -- 第 `k+1` ブロックの根（`l = (k+1)*|Q|`）
    have hle : l = (k + 1) * Q.length := by omega
    subst hle
    have := entry0_mTower_block Q d e n (k + 1) 0 (by omega) hQ1
    rw [Nat.add_zero] at this
    rw [this]
    have hmul : d * (k + 1) = d * k + d := Nat.mul_succ d k
    omega

/-- ★★★ **ブロックの根の行 1 の親は、1 つ前のブロックの中にいる。**
（L3 の §187.2 が**仮定**していたもの。） -/
theorem blockRoot_parent_prevBlock {Q : TrioSeq} {d e n k a : ℕ}
    (hQne : Q ≠ []) (hd : 0 < d) (he : 0 < e) (hk : k + 1 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (h : nextrel1 (mTower Q d e n) a ((k + 1) * Q.length)) :
    k * Q.length ≤ a := by
  by_contra hlt
  have hQ1 : 0 < Q.length := List.length_pos_iff.mpr hQne
  have hTlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have hb1 : k * Q.length < (mTower Q d e n).length := by
    rw [hTlen]
    exact Nat.lt_of_lt_of_le
      (show k * Q.length < (k + 1) * Q.length from by rw [Nat.succ_mul]; omega)
      (Nat.mul_le_mul_right _ (by omega))
  have hb2 : (k + 1) * Q.length < (mTower Q d e n).length := by
    rw [hTlen]
    exact Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl _) hQ1
  have hle0 : le0 (mTower Q d e n) (k * Q.length) ((k + 1) * Q.length) :=
    ⟨hb1, hb2, rtg0_blockRoot_succ hQne hd hk hr0⟩
  have hmin := h.2.2.2.2.2 (k * Q.length) ⟨by omega, hle0⟩
  rw [entry1_mTower_blockRoot hQne d e n (k + 1) (by omega),
    entry1_mTower_blockRoot hQne d e n k (by omega)] at hmin
  have hmul : e * (k + 1) = e * k + e := Nat.mul_succ e k
  omega

/-- 塔の第 `k` ブロックの根の行 2（`Lift1` も `shiftr01` も行 2 を変えない）。 -/
theorem entry2_mTower_blockRoot (Q : TrioSeq) (d e : ℕ) :
    ∀ (n k : ℕ), k < n → 0 < Q.length →
      entry (mTower Q d e n) 2 (k * Q.length) = entry Q 2 0 := by
  intro n
  induction n with
  | zero => intro k hk _; omega
  | succ n ih =>
      intro k hk hQ1
      rw [mTower_succ]
      rcases Nat.lt_or_ge k n with hkn | hkn
      · have hlt : k * Q.length < (mTower Q d e n).length := by
          rw [mTower_length]
          calc k * Q.length < k * Q.length + Q.length := by omega
            _ = (k + 1) * Q.length := by rw [Nat.succ_mul]
            _ ≤ n * Q.length := Nat.mul_le_mul_right _ (by omega)
        rw [entry_append_left _ _ hlt]
        exact ih k hkn hQ1
      · have hk0 : k = n := by omega
        subst hk0
        rw [show k * Q.length = (mTower Q d e k).length + 0 from by
            rw [mTower_length]; omega,
          entry_append_right, entry2_Lift1, entry2_shiftr01]

/-- ★★ **`p_rel` の分割**: ブロックの根の行 1 の親は `k*|Q| + p_rel`（`p_rel < |Q|`）。 -/
theorem blockRoot_parent_split {Q : TrioSeq} {d e n k : ℕ}
    (hQne : Q ≠ []) (hd : 0 < d) (he : 0 < e) (hk : k + 1 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hp : hasParent (mTower Q d e n) 1 ((k + 1) * Q.length)) :
    ∃ p, p < Q.length ∧
      parent (mTower Q d e n) 1 ((k + 1) * Q.length) = k * Q.length + p := by
  have hnr := parent_nextR hp
  have h1 : nextrel1 (mTower Q d e n)
      (parent (mTower Q d e n) 1 ((k + 1) * Q.length)) ((k + 1) * Q.length) := by
    unfold nextR at hnr
    rw [if_neg (by omega), if_pos rfl] at hnr
    exact hnr
  have hge : k * Q.length ≤ parent (mTower Q d e n) 1 ((k + 1) * Q.length) :=
    blockRoot_parent_prevBlock hQne hd he hk hr0 h1
  have hlt : parent (mTower Q d e n) 1 ((k + 1) * Q.length) < (k + 1) * Q.length :=
    h1.2.2.1
  have hsucc : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
  exact ⟨parent (mTower Q d e n) 1 ((k + 1) * Q.length) - k * Q.length,
    by omega, by omega⟩

/-- ★ **`j = 0` の窓は `|Q| − p_rel`**（L3 の §187.2 の式）。 -/
theorem blockRoot_window_eq {Q : TrioSeq} {d e n k : ℕ}
    (hQne : Q ≠ []) (hd : 0 < d) (he : 0 < e) (hk : k + 1 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hp : hasParent (mTower Q d e n) 1 ((k + 1) * Q.length)) :
    ∃ p, p < Q.length ∧
      parent (mTower Q d e n) 1 ((k + 1) * Q.length) = k * Q.length + p ∧
      (k + 1) * Q.length - parent (mTower Q d e n) 1 ((k + 1) * Q.length)
        = Q.length - p := by
  obtain ⟨p, hplt, hpe⟩ := blockRoot_parent_split hQne hd he hk hr0 hp
  have hsucc : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
  exact ⟨p, hplt, hpe, by rw [hpe]; omega⟩

/-- ★★ **`p_rel ≥ 1`（＝ 親がブロックの根でない）なら、窓は `< |Q|`。**
（L3 の §187.2 の「良い側」。`|V|` が減る枝。） -/
theorem blockRoot_window_lt_of_ne_root {Q : TrioSeq} {d e n k : ℕ}
    (hQne : Q ≠ []) (hd : 0 < d) (he : 0 < e) (hk : k + 1 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hp : hasParent (mTower Q d e n) 1 ((k + 1) * Q.length))
    (hne : parent (mTower Q d e n) 1 ((k + 1) * Q.length) ≠ k * Q.length) :
    (k + 1) * Q.length - parent (mTower Q d e n) 1 ((k + 1) * Q.length)
      < Q.length := by
  obtain ⟨p, hplt, hpe, hw⟩ := blockRoot_window_eq hQne hd he hk hr0 hp
  rw [hw]
  have hp0 : p ≠ 0 := by
    intro hc
    rw [hc, Nat.add_zero] at hpe
    exact hne hpe
  omega

/-- ⚠ **`p_rel = 0`（親がブロックの根）なら窓は `= |Q|`**（減らない側 ＝ 核）。 -/
theorem blockRoot_window_eq_of_root {Q : TrioSeq} {d e n k : ℕ}
    (hQ1 : 0 < Q.length)
    (hpe : parent (mTower Q d e n) 1 ((k + 1) * Q.length) = k * Q.length) :
    (k + 1) * Q.length - parent (mTower Q d e n) 1 ((k + 1) * Q.length)
      = Q.length := by
  rw [hpe]
  have hsucc : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
  omega

/-- 塔＋途中ブロックの根の行 0 は `Q` の根の行 0。 -/
theorem entry0_towerPrefix_root (Q : TrioSeq) (d e n j : ℕ) (hQ1 : 0 < Q.length) :
    entry (mTower Q d e n
      ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 0 0
      = entry Q 0 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [show mTower Q d e 0 = ([] : TrioSeq) from rfl, List.nil_append,
      entry_take (by omega), entry0_Lift1, entry0_shiftr01 hQ1, Nat.mul_zero,
      Nat.add_zero]
  · have hlt : 0 < (mTower Q d e n).length := by
      rw [mTower_length]; exact Nat.mul_pos hn hQ1
    rw [entry_append_left _ _ hlt]
    have := entry0_mTower_block Q d e n 0 0 hn hQ1
    simpa using this

open Classical in
/-- ★★★★★★★★ **接頭辞つき窓補題**: 錐の外の列でも、親が居るなら
窓は自分のブロックの中（＝ 親は `(A ++ mTower).length` 以上）。
**`le1 Q 0 j` は不要。** -/
theorem prefix_window_of_outOfCone_all {A M : TrioSeq} {d e n j : ℕ}
    (hM2 : 2 ≤ M.length) (hd1pos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hbase : entry M.dropLast 0 0 = 0)
    (hj : j < M.dropLast.length) (hj1 : 0 < j)
    (hout : ¬ le1 M 0 (0 + j))
    (hpar0 : hasParent (A ++ mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
      (srow (A ++ mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
        ((A ++ mTower M.dropLast d e n).length + j))
      ((A ++ mTower M.dropLast d e n).length + j)) :
    (A ++ mTower M.dropLast d e n).length
      ≤ parent (A ++ mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
        (srow (A ++ mTower M.dropLast d e n
            ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
          ((A ++ mTower M.dropLast d e n).length + j))
        ((A ++ mTower M.dropLast d e n).length + j) := by
  set Q := M.dropLast with hQ
  set T := mTower Q d e n
      ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1) with hT
  have hQ1 : 0 < Q.length := by omega
  have hTlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have hAT : (A ++ mTower Q d e n).length = A.length + n * Q.length := by
    rw [List.length_append, hTlen]
  -- ★ 結合を `A ++ (塔 ++ ブロック)` に直す
  have hassoc : A ++ mTower Q d e n
      ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1) = A ++ T := by
    rw [hT, List.append_assoc]
  have hpos' : (A ++ mTower Q d e n).length + j = A.length + (n * Q.length + j) := by
    rw [hAT]; omega
  -- ★ `hasParent_append_right` / `parent_append_right` の前提
  have hroot : entry T 0 0 = 0 := by
    rw [hT, entry0_towerPrefix_root Q d e n j hQ1]
    exact hbase
  have hTentry : entry T 0 (n * Q.length + j) = entry Q 0 j + d * n := by
    rw [hT, show n * Q.length + j = (mTower Q d e n).length + j from by rw [hTlen],
      entry_append_right, entry_take (by omega), entry0_Lift1,
      entry0_shiftr01 (by omega)]
  have hQj : 0 < entry Q 0 j := by
    have hjM : j < M.length := by
      rw [hQ, List.length_dropLast] at hj; omega
    have := hr0 j hj1 hjM
    rw [hQ, List.dropLast_eq_take,
      entry_take (show j < M.length - 1 by rw [hQ, List.length_dropLast] at hj; omega)]
    omega
  have hposA : 0 < entry (A ++ T) 0 (A.length + (n * Q.length + j)) := by
    rw [entry_append_right, hTentry]; omega
  -- ★ 接頭辞を剥がす
  rw [hassoc, hpos'] at hpar0 ⊢
  have hsrow : srow (A ++ T) (A.length + (n * Q.length + j))
      = srow T (n * Q.length + j) := by
    unfold srow
    rw [entry_append_right, entry_append_right]
  rw [hsrow] at hpar0 ⊢
  have hpT : hasParent T (srow T (n * Q.length + j)) (n * Q.length + j) :=
    (hasParent_append_right A T hroot hposA).mp hpar0
  rw [parent_append_right A T hroot hposA hpT, hAT]
  have hcore := window_of_outOfCone_all (M := M) (d := d) (e := e) (n := n) (j := j)
    hM2 hd1pos hd0e hr0 hlp hj hj1 hout hpT
  rw [← hQ, ← hT] at hcore
  omega

/-- 位置の書き換え（`B.take j` の長さは `j`）。 -/
theorem prefixTake_length (A Q : TrioSeq) (d e n j : ℕ) (hj : j < Q.length) :
    (A ++ mTower Q d e n
      ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length
      = (A ++ mTower Q d e n).length + j := by
  have hBlen : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length = Q.length := by
    rw [Lift1_length, shiftr01_length]
  rw [List.length_append, List.length_take, hBlen, Nat.min_eq_left (by omega)]

open Classical in
/-- ★★ **§167 の書き方に合わせた接頭辞つき窓補題**（L3 がそのまま貼れる形）。 -/
theorem prefix_window_of_outOfCone_all' {A M : TrioSeq} {d e n j : ℕ}
    (hM2 : 2 ≤ M.length) (hd1pos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hbase : entry M.dropLast 0 0 = 0)
    (hj : j < M.dropLast.length) (hj1 : 0 < j)
    (hout : ¬ le1 M 0 (0 + j))
    (hpar0 : hasParent (A ++ mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
      (srow (A ++ mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
        (A ++ mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length)
      (A ++ mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length) :
    (A ++ mTower M.dropLast d e n).length
      ≤ parent (A ++ mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
        (srow (A ++ mTower M.dropLast d e n
            ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
          (A ++ mTower M.dropLast d e n
            ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length)
        (A ++ mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length := by
  rw [prefixTake_length A M.dropLast d e n j hj] at hpar0 ⊢
  exact prefix_window_of_outOfCone_all hM2 hd1pos hd0e hr0 hlp hbase hj hj1 hout hpar0

/-- ★★ **二分法の `iff`**（L3 の問い): 窓が `|Q|`（＝ 非減少）⟺ 親がブロックの根。 -/
theorem blockRoot_window_eq_iff {Q : TrioSeq} {d e n k : ℕ}
    (hQne : Q ≠ []) (hd : 0 < d) (he : 0 < e) (hk : k + 1 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hp : hasParent (mTower Q d e n) 1 ((k + 1) * Q.length)) :
    (k + 1) * Q.length - parent (mTower Q d e n) 1 ((k + 1) * Q.length)
        = Q.length
      ↔ parent (mTower Q d e n) 1 ((k + 1) * Q.length) = k * Q.length := by
  have hQ1 : 0 < Q.length := List.length_pos_iff.mpr hQne
  constructor
  · intro hw
    by_contra hne
    have := blockRoot_window_lt_of_ne_root hQne hd he hk hr0 hp hne
    omega
  · exact fun hpe => blockRoot_window_eq_of_root hQ1 hpe

open Classical in
/-- ★★★★★★★★ **§186 の接頭辞つき版**: 塔に 1 列足したものの展開は
**接頭辞 ＋ 短い塔**に分かれる。 -/
theorem prefix_snocStep_oper_tower {A Q : TrioSeq} {d e n j p m : ℕ}
    (hj : j < Q.length) (hpj : p < j) (hQ1 : 0 < Q.length)
    (hbase : entry Q 0 0 = 0)
    (hz : ¬ (entry (mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 0
        ((mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1) = 0 ∧
      entry (mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 1
        ((mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1) = 0 ∧
      entry (mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 2
        ((mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1) = 0))
    (hpar : hasParent (mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (srow (mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        ((mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1))
      ((mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1))
    (hpe : parent (mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (srow (mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        ((mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1))
      ((mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1)
      = n * Q.length + p) :
    ∃ (V : TrioSeq) (d0 d1 : ℕ), V.length = j - p ∧
      (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))⟦m⟧
      = (A ++ mTower Q d e n
          ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take p)
        ++ mTower V d0 d1 m := by
  obtain ⟨V, d0, d1, hVlen, hVeq⟩ :=
    snocStep_oper_tower (Q := Q) (d := d) (e := e) (n := n) (j := j) (p := p) (m := m)
      hj hpj hz hpar hpe
  refine ⟨V, d0, d1, hVlen, ?_⟩
  have hTlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have hBlen : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length = Q.length := by
    rw [Lift1_length, shiftr01_length]
  have hT2 : 2 ≤ (mTower Q d e n
      ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length := by
    rw [List.length_append, hTlen, List.length_take, hBlen,
      Nat.min_eq_left (by omega)]
    omega
  have hroot : entry (mTower Q d e n
      ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 0 0 = 0 := by
    rw [entry0_towerPrefix_root Q d e n j hQ1]; exact hbase
  rw [List.append_assoc A (mTower Q d e n), oper_append_right _ _ m hT2 hroot,
    hVeq, ← List.append_assoc, ← List.append_assoc]

/-- `ℕ × ℕ` の辞書式順序は整礎。 -/
theorem prodLexNat_wf :
    WellFounded (Prod.Lex (· < · : ℕ → ℕ → Prop) (· < · : ℕ → ℕ → Prop)) :=
  WellFounded.prod_lex wellFounded_lt wellFounded_lt

/-- ★★ **形 (b)**: `ℕ` の対についての強帰納の原理（L3 の指定）。 -/
theorem prodLexNat_induction {P : ℕ × ℕ → Prop}
    (h : ∀ p, (∀ q, Prod.Lex (· < · : ℕ → ℕ → Prop) (· < · : ℕ → ℕ → Prop) q p → P q) → P p) :
    ∀ p, P p :=
  fun p => prodLexNat_wf.induction p h

/-- ★★ **測度つき版**: `μ : α → ℕ × ℕ` を測度にした強帰納
（`|V|` と `rankDE` を直に入れて使える形）。 -/
theorem prodLexNat_measure_induction {α : Sort*} {μ : α → ℕ × ℕ} {P : α → Prop}
    (h : ∀ a, (∀ b, Prod.Lex (· < · : ℕ → ℕ → Prop) (· < · : ℕ → ℕ → Prop)
        (μ b) (μ a) → P b) → P a) :
    ∀ a, P a :=
  fun a => (InvImage.wf μ prodLexNat_wf).induction a h

/-- ★ **第 1 成分が減る**（`|V|` が減る段）。 -/
theorem prodLexNat_fst {a₁ a₂ b₁ b₂ : ℕ} (h : a₁ < a₂) :
    Prod.Lex (· < · : ℕ → ℕ → Prop) (· < · : ℕ → ℕ → Prop) (a₁, b₁) (a₂, b₂) :=
  Prod.Lex.left _ _ h

/-- ★ **第 1 成分は同じで第 2 成分が減る**（`|V|` は同じで `rankDE` が減る段）。 -/
theorem prodLexNat_snd {a b₁ b₂ : ℕ} (h : b₁ < b₂) :
    Prod.Lex (· < · : ℕ → ℕ → Prop) (· < · : ℕ → ℕ → Prop) (a, b₁) (a, b₂) :=
  Prod.Lex.right _ h

/-- ★★★ **⟹ 2 枝をそのまま渡せる形**（L3 の「場合分けの合成」に直結）。
各段で「第 1 成分が減る」か「第 1 成分は同じで第 2 成分が減る」なら、帰納が回る。 -/
theorem prodLexNat_induction_two {α : Sort*} {μ : α → ℕ × ℕ} {P : α → Prop}
    (h : ∀ a, (∀ b, (μ b).1 < (μ a).1 ∨ ((μ b).1 = (μ a).1 ∧ (μ b).2 < (μ a).2) → P b) →
      P a) :
    ∀ a, P a := by
  refine prodLexNat_measure_induction (μ := μ) (fun a ih => h a (fun b hb => ih b ?_))
  rcases hb with hlt | ⟨heq, hlt⟩
  · exact (Prod.mk.eta (p := μ b)) ▸ (Prod.mk.eta (p := μ a)) ▸ prodLexNat_fst hlt
  · refine (Prod.mk.eta (p := μ b)) ▸ (Prod.mk.eta (p := μ a)) ▸ ?_
    rw [heq]
    exact prodLexNat_snd hlt

/-- 定数の行 2 は `shiftr01` で保たれる。 -/
theorem h12_constRow2_shiftr01 {Q : TrioSeq} {z d0 d1 : ℕ} (h : ∀ p ∈ Q, p.2.2 = z) :
    ∀ p ∈ shiftr01 d0 d1 Q, p.2.2 = z := by
  intro p hp
  unfold shiftr01 at hp
  rw [List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact h q hq

/-- 定数の行 2 は塔で保たれる。 -/
theorem h12_constRow2_mTower {Q : TrioSeq} {z : ℕ} (h : ∀ p ∈ Q, p.2.2 = z) (d e n : ℕ) :
    ∀ p ∈ mTower Q d e n, p.2.2 = z := by
  intro p hp
  unfold mTower at hp
  rw [List.mem_flatMap] at hp
  obtain ⟨k, -, hk⟩ := hp
  exact L105.constRow2_Lift1 (h12_constRow2_shiftr01 h) p hk

/-- ★ **行 2 が定数なら塔は `W u` に入る**（`c = 0` も `c ≥ 1` も）。
⟹ `MTowerClosedRow2` の「行 2 が定数」の場合を閉じる。 -/
theorem mTower_mem_of_constRow2 {u : ℕ} {Q : TrioSeq} {c : ℕ}
    (hz : ∀ p ∈ Q, p.2.2 = c) (hQ : Q ∈ W u) (d e n : ℕ) :
    mTower Q d e n ∈ W u := by
  by_cases hQne : Q = []
  · have : mTower Q d e n = [] := by
      refine List.eq_nil_of_length_eq_zero ?_
      rw [mTower_length, hQne]
      simp
    rw [this]
    simpa using W_nil u
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · exact mTower_mem_of_zeroRow2 hz hQ d e n
  · cases n with
    | zero => simpa using W_nil u
    | succ n =>
        refine constRow2_mem_W (h12_constRow2_mTower hz d e (n + 1)) ?_
        rw [lev_mTower_root hQne]
        exact lev_root_le_of_mem_W hQ hQne

/-- ★ **深さ 0 の列は行 2 の親を持てない**（行 0 の鎖が入って来られない）。 -/
theorem not_hasParent_two_of_depth_zero {M : TrioSeq} {j : ℕ} (h : entry M 0 j = 0) :
    ¬ hasParent M 2 j := by
  rintro ⟨j0, hj0, -⟩
  have h2 : nextrel2 M j0 j := by
    unfold nextR at hj0
    rw [if_neg (by omega), if_neg (by omega)] at hj0
    exact hj0
  have hlt : j0 < j := h2.2.2.1
  have hrtg : Relation.ReflTransGen (nextrel0 M) j0 j := rtg1_to_rtg0 h2.2.2.2.2.1.2.2
  rcases Relation.ReflTransGen.cases_tail hrtg with hEq | ⟨b, -, hb⟩
  · omega
  · have : entry M 0 b < entry M 0 j := hb.2.2.2.1
    omega

/-- ★★★ **接頭辞つき `MTowerSingle`（行 2 が正の場合）**。
⟹ R2 の残差の **4.32%（`|V| = 1`）** を消す。 -/
theorem prefix_mTowerSingle_row2 {u : ℕ} {A Q : TrioSeq}
    (hA : A ∈ W u) (hAne : A ≠ []) (h1 : Q.length = 1)
    (hbase : entry Q 0 0 = 0) (hzpos : 0 < entry Q 2 0) (d e : ℕ) :
    ∀ n, A ++ mTower Q d e n ∈ W u := by
  have hQne : Q ≠ [] := by intro hc; rw [hc] at h1; simp at h1
  set z : ℕ := entry Q 2 0 with hzdef
  have hconstQ : ∀ p ∈ Q, p.2.2 = z := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hp
    have hj0 : j = 0 := by omega
    subst hj0
    show (Q[0]'(by omega)).2.2 = entry Q 2 0
    unfold entry
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp
  intro n
  induction n with
  | zero =>
      rw [show mTower Q d e 0 = ([] : TrioSeq) from rfl, List.append_nil]
      exact hA
  | succ n ih =>
      have hTn : (mTower Q d e n).length = n := by rw [mTower_length, h1, Nat.mul_one]
      have hTn1 : (mTower Q d e (n + 1)).length = n + 1 := by
        rw [mTower_length, h1, Nat.mul_one]
      have hconstT : ∀ p ∈ mTower Q d e (n + 1), p.2.2 = z :=
        h12_constRow2_mTower hconstQ d e (n + 1)
      obtain ⟨c, hc⟩ : ∃ c, Lift1 (shiftr01 (d * n) 0 Q) (e * n) = [c] := by
        rw [← List.length_eq_one_iff, Lift1_length, shiftr01_length, h1]
      have hCne : A ++ mTower Q d e n ≠ [] := by
        intro h
        exact hAne (List.append_eq_nil_iff.mp h).1
      have hCl : (A ++ mTower Q d e n).length = A.length + n := by
        rw [List.length_append, hTn]
      -- 対象を `A ++ mTower Q d e (n+1)` に揃える
      have hobj : A ++ mTower Q d e n ++ [c] = A ++ mTower Q d e (n + 1) := by
        rw [mTower_succ, hc, List.append_assoc]
      -- 末尾列の行 2 は `z > 0` ⟹ `srow = 2`
      have hE2 : entry (A ++ mTower Q d e (n + 1)) 2 (A.length + n) = z := by
        rw [entry_append_right]
        exact hconstT _ (entry_pair_mem (by omega))
      have hsrow : srow (A ++ mTower Q d e (n + 1)) (A.length + n) = 2 := by
        unfold srow; rw [if_pos (by rw [hE2]; omega)]
      -- 末尾列は行 2 の孤児
      have horph : ¬ hasParent (A ++ mTower Q d e (n + 1)) 2 (A.length + n) := by
        by_cases hd0 : entry (A ++ mTower Q d e (n + 1)) 0 (A.length + n) = 0
        · exact not_hasParent_two_of_depth_zero hd0
        · have hroot : entry (mTower Q d e (n + 1)) 0 0 = 0 := by
            have := entry0_mTower_block Q d e (n + 1) 0 0 (by omega) (by omega)
            simpa [hbase] using this
          intro hp
          have := (hasParent_append_right A (mTower Q d e (n + 1)) hroot
            (show 0 < entry (A ++ mTower Q d e (n + 1)) 0 (A.length + n) by omega)).mp hp
          exact L105.not_hasParent_two_of_row2_const hconstT (by omega)
            (by rw [hTn1]; simpa using this)
      rw [mTower_succ, ← List.append_assoc, hc]
      refine snoc_orphan_W c ih hCne ?_
      rw [hobj, hCl, hsrow]
      exact horph

/-- ★★★ **`zle1 R` は「末尾列の行 2 ≤ 1」だけでよい**。 -/
theorem tower2_z_zero_of_last {v z m : ℕ} {R : TrioSeq} (hRne : R ≠ [])
    (hz1 : z ≤ 1) (hlast : entry R 2 (R.length - 1) ≤ 1) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) : z = 0 := by
  have hlt := L53.tower2_zr (v := v) (z := z) hRne hd hi2 hpM
  omega

/-- ⟹ **消費側の `hz0` は「`R` の末尾列の行 2 ≤ 1」1 本から出る。** -/
theorem hz0_of_last {v z m t : ℕ} {R : TrioSeq} (hRne : R ≠ [])
    (hz1 : z ≤ 1) (hlast : entry R 2 (R.length - 1) ≤ 1) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t) 2 0 = 0 := by
  have hzz : z = 0 := tower2_z_zero_of_last hRne hz1 hlast hd hi2 hpM
  rw [entry2_Lift1]
  show entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 2 0 = 0
  have : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 2 0 = z := rfl
  omega

/-- ★★★ **錐の外の二分法**: ブロッカーが `j` 自身か、`j` より手前か。 -/
theorem outOfCone_dichotomy {Q : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    {j : ℕ} (hj : j < Q.length) (hout : ¬ le1 Q 0 j) :
    entry Q 1 j ≤ entry Q 1 0
      ∨ ∃ y, y < j ∧ y ≠ 0 ∧ Relation.ReflTransGen (nextrel0 Q) y j
          ∧ entry Q 1 y ≤ entry Q 1 0 := by
  obtain ⟨y, hy, hy0, hy1⟩ := (L105.not_le1_zero_iff hr0 hj).mp hout
  have hyle : y ≤ j := rtg0_le hy
  rcases Nat.lt_or_ge y j with hlt | hge
  · exact Or.inr ⟨y, hlt, hy0, hy, hy1⟩
  · have : y = j := by omega
    subst this
    exact Or.inl hy1

/-- ⟹ **`h1out` が破れるのは「`j` 自身がブロッカー」のときだけ**。 -/
theorem h1out_holds_of_not_selfBlocker {Q : TrioSeq}
    (_hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    {j : ℕ} (_hj : j < Q.length) (_hout : ¬ le1 Q 0 j)
    (hself : ¬ (entry Q 1 j ≤ entry Q 1 0)) :
    entry Q 1 0 < entry Q 1 j := by omega

/-- ★ **`j` 自身がブロッカーなら、根は行 1 の親になれない**（狭義増加が破れる）。 -/
theorem root_not_nextrel1_of_selfBlocker {Q : TrioSeq} {j : ℕ}
    (hself : entry Q 1 j ≤ entry Q 1 0) : ¬ nextrel1 Q 0 j := by
  intro h
  have := h.2.2.2.1
  omega

/-- ★★★ **行 0 版**: `srow = 0` のブロック根の行 0 の親は、1 つ前のブロックの中。
⚠ **`le0` の鎖が要りません**（`nextrel0` の最小性は素の区間の上なので）。 -/
theorem blockRoot_parent_prevBlock_row0 {Q : TrioSeq} {d e n k a : ℕ}
    (hQ1 : 0 < Q.length) (hd : 0 < d) (hk : k + 1 < n)
    (h : nextrel0 (mTower Q d e n) a ((k + 1) * Q.length)) :
    k * Q.length ≤ a := by
  by_contra hlt
  have hE : ∀ i, i < n →
      entry (mTower Q d e n) 0 (i * Q.length) = entry Q 0 0 + d * i := by
    intro i hi
    have := entry0_mTower_block Q d e n i 0 hi hQ1
    simpa using this
  have hsucc : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
  have hmin := h.2.2.2.2 (k * Q.length) ⟨by omega, by omega⟩
  rw [hE (k + 1) (by omega), hE k (by omega)] at hmin
  have hmul : d * (k + 1) = d * k + d := Nat.mul_succ d k
  omega

/-- ⟹ `hasParent` の言葉で（行 0）。 -/
theorem blockRoot_parent_prevBlock_row0' {Q : TrioSeq} {d e n k : ℕ}
    (hQ1 : 0 < Q.length) (hd : 0 < d) (hk : k + 1 < n)
    (hp : hasParent (mTower Q d e n) 0 ((k + 1) * Q.length)) :
    k * Q.length ≤ parent (mTower Q d e n) 0 ((k + 1) * Q.length) := by
  have hnr := parent_nextR hp
  have h0 : nextrel0 (mTower Q d e n)
      (parent (mTower Q d e n) 0 ((k + 1) * Q.length)) ((k + 1) * Q.length) := by
    unfold nextR at hnr
    rw [if_pos rfl] at hnr
    exact hnr
  exact blockRoot_parent_prevBlock_row0 hQ1 hd hk h0

/-- ★ **(p1c) ブロック根の `srow` は `entry Q 1 0 + e*(k+1)` で決まる**
（行 2 は `hz0` で 0）。⟹ **`srow = 0 ⟺ entry Q 1 0 = 0 ∧ e = 0`**。 -/
theorem srow_mTower_blockRoot_zero {Q : TrioSeq} {d e n k : ℕ}
    (hQ1 : 0 < Q.length) (hQne : Q ≠ []) (hk : k + 1 < n)
    (hz0 : entry Q 2 0 = 0) (h1 : entry Q 1 0 = 0) (he : e = 0) :
    srow (mTower Q d e n) ((k + 1) * Q.length) = 0 := by
  have h2 : entry (mTower Q d e n) 2 ((k + 1) * Q.length) = 0 := by
    rw [entry2_mTower_blockRoot Q d e n (k + 1) (by omega) hQ1]; exact hz0
  have hr1 : entry (mTower Q d e n) 1 ((k + 1) * Q.length) = 0 := by
    rw [entry1_mTower_blockRoot hQne d e n (k + 1) (by omega), h1, he]
    omega
  unfold srow
  rw [if_neg (by omega), if_neg (by omega)]

/-- 塔の第 `k` ブロックの `i` 列目の行 1 の**上界**（錐の中か外かによらない）。 -/
theorem entry1_mTower_block_le (Q : TrioSeq) (d e : ℕ) :
    ∀ (n k i : ℕ), k < n → i < Q.length →
      entry (mTower Q d e n) 1 (k * Q.length + i) ≤ entry Q 1 i + e * k := by
  intro n
  induction n with
  | zero => intro k i hk _; omega
  | succ n ih =>
      intro k i hk hi
      rw [mTower_succ]
      rcases Nat.lt_or_ge k n with hkn | hkn
      · have hlt : k * Q.length + i < (mTower Q d e n).length := by
          rw [mTower_length]
          calc k * Q.length + i < k * Q.length + Q.length := by omega
            _ = (k + 1) * Q.length := by rw [Nat.succ_mul]
            _ ≤ n * Q.length := Nat.mul_le_mul_right _ (by omega)
        rw [entry_append_left _ _ hlt]
        exact ih k i hkn hi
      · have hk0 : k = n := by omega
        subst hk0
        rw [show k * Q.length + i = (mTower Q d e k).length + i from by
            rw [mTower_length],
          entry_append_right]
        show ((Lift1 (shiftr01 (d * k) 0 Q) (e * k)).getD i (0, 0, 0)).2.1
          ≤ entry Q 1 i + e * k
        rw [L105.block_getD hi]
        by_cases hc : le1 Q 0 i <;> simp [hc]

/-- ★★★ **(q2a) 証人つき一般化**: 最小性の証人が**根でなくてよい**。
⚠ **`0 < e` も `0 < d` も `hr0` も要りません。** -/
theorem blockRoot_parent_prevBlock_gen {Q : TrioSeq} {d e n k a x : ℕ}
    (hQne : Q ≠ []) (hk : k + 1 < n)
    (hx : x < Q.length) (hxlow : entry Q 1 x < entry Q 1 0)
    (hxle0 : le0 (mTower Q d e n) (k * Q.length + x) ((k + 1) * Q.length))
    (h : nextrel1 (mTower Q d e n) a ((k + 1) * Q.length)) :
    k * Q.length ≤ a := by
  by_contra hlt
  have hmin := h.2.2.2.2.2 (k * Q.length + x) ⟨by omega, hxle0⟩
  rw [entry1_mTower_blockRoot hQne d e n (k + 1) (by omega)] at hmin
  have hub := entry1_mTower_block_le Q d e n k x (by omega) hx
  have hmul : e * (k + 1) = e * k + e := Nat.mul_succ e k
  omega

/-- 行 0 は行 0 の鎖に沿って**単調**。 -/
theorem rtg0_entry_mono {M : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 M) a b) : entry M 0 a ≤ entry M 0 b := by
  induction h with
  | refl => omega
  | @tail c d _ hcd ih => have := hcd.2.2.2.1; omega

/-- ★ **鎖 ⟹ 窓**（`rtg0_of_window` の逆向き）。 -/
theorem rtg0_window {M : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 M) a b) :
    ∀ l, a < l → l ≤ b → entry M 0 a < entry M 0 l := by
  induction h with
  | refl => intro l h1 h2; omega
  | @tail c d hac hcd ih =>
      intro l h1 h2
      rcases Nat.lt_or_ge c l with hcl | hlc
      · have hmono : entry M 0 a ≤ entry M 0 c := rtg0_entry_mono hac
        have hlt : entry M 0 c < entry M 0 d := hcd.2.2.2.1
        rcases Nat.eq_or_lt_of_le h2 with heq | hld
        · subst heq; omega
        · have hmin := hcd.2.2.2.2 l ⟨hcl, hld⟩
          omega
      · exact ih l h1 hlc

/-- ★★★★ **(q5)**: 遠いブロックの位置 `x` が `le0` で次のブロックの根に届くなら、
**近いブロックの同じ位置も届く**。⚠ **`0 < d` も `0 < e` も `hr0` も要りません。** -/
theorem le0_mTower_block_shift {Q : TrioSeq} {d e n m k x : ℕ}
    (hQ1 : 0 < Q.length) (hm : m ≤ k) (hx : x < Q.length) (hk : k + 1 < n)
    (h : le0 (mTower Q d e n) (m * Q.length + x) ((k + 1) * Q.length)) :
    le0 (mTower Q d e n) (k * Q.length + x) ((k + 1) * Q.length) := by
  have hE : ∀ j i, j < n → i < Q.length →
      entry (mTower Q d e n) 0 (j * Q.length + i) = entry Q 0 i + d * j :=
    fun j i hj hi => entry0_mTower_block Q d e n j i hj hi
  have hTlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have hw := rtg0_window h.2.2
  have hlen1 : (k + 1) * Q.length < (mTower Q d e n).length := by
    rw [hTlen]; exact Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl _) hQ1
  refine ⟨by
    rw [hTlen]
    calc k * Q.length + x < k * Q.length + Q.length := by omega
      _ = (k + 1) * Q.length := by rw [Nat.succ_mul]
      _ < n * Q.length := by rw [hTlen] at hlen1; exact hlen1, hlen1, ?_⟩
  refine rtg0_of_window hlen1 (by rw [Nat.succ_mul]; omega) ?_
  intro l hl1 hl2
  rw [hE k x (by omega) hx]
  have hsucc : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
  rcases Nat.eq_or_lt_of_le hl2 with heq | hlt
  · -- l = (k+1)*|Q| : 証人は ブロック (m+1) の根
    subst heq
    have hmp : m * Q.length + x < (m + 1) * Q.length := by
      rw [Nat.succ_mul]; omega
    have hmle : (m + 1) * Q.length ≤ (k + 1) * Q.length :=
      Nat.mul_le_mul_right _ (by omega)
    have := hw ((m + 1) * Q.length) hmp hmle
    rw [show m * Q.length + x = m * Q.length + x from rfl] at this
    rw [hE m x (by omega) hx] at this
    have h0 := hE (m + 1) 0 (by omega) hQ1
    rw [Nat.add_zero] at h0
    rw [h0] at this
    have h1 := hE (k + 1) 0 (by omega) hQ1
    rw [Nat.add_zero] at h1
    rw [h1]
    have hm1 : d * (m + 1) = d * m + d := Nat.mul_succ d m
    have hk1 : d * (k + 1) = d * k + d := Nat.mul_succ d k
    omega
  · -- l = k*|Q| + i, x < i < |Q| : 証人は ブロック m の同じ位置 i
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < Q.length ∧ l = k * Q.length + i := by
      refine ⟨l - k * Q.length, by omega, by omega⟩
    have hmp : m * Q.length + x < m * Q.length + i := by omega
    have hmle : m * Q.length + i ≤ (k + 1) * Q.length := by
      have : m * Q.length ≤ k * Q.length := Nat.mul_le_mul_right _ hm
      omega
    have := hw (m * Q.length + i) hmp hmle
    rw [hE m x (by omega) hx, hE m i (by omega) hi] at this
    rw [hE k i (by omega) hi]
    omega

/-- `e = 0` なら塔の行 1 はブロックに依らない。 -/
theorem entry1_mTower_block_e_zero (Q : TrioSeq) (d : ℕ) :
    ∀ (n k i : ℕ), k < n → i < Q.length →
      entry (mTower Q d 0 n) 1 (k * Q.length + i) = entry Q 1 i := by
  intro n
  induction n with
  | zero => intro k i hk _; omega
  | succ n ih =>
      intro k i hk hi
      rw [mTower_succ]
      rcases Nat.lt_or_ge k n with hkn | hkn
      · have hlt : k * Q.length + i < (mTower Q d 0 n).length := by
          rw [mTower_length]
          calc k * Q.length + i < k * Q.length + Q.length := by omega
            _ = (k + 1) * Q.length := by rw [Nat.succ_mul]
            _ ≤ n * Q.length := Nat.mul_le_mul_right _ (by omega)
        rw [entry_append_left _ _ hlt]
        exact ih k i hkn hi
      · have hk0 : k = n := by omega
        subst hk0
        rw [show k * Q.length + i = (mTower Q d 0 k).length + i from by
            rw [mTower_length],
          entry_append_right]
        show ((Lift1 (shiftr01 (d * k) 0 Q) (0 * k)).getD i (0, 0, 0)).2.1 = entry Q 1 i
        rw [L105.block_getD hi]
        by_cases hc : le1 Q 0 i <;> simp [hc]

/-- ★★★ **`e = 0` の場合**（`0 < d` も `hr0` も要りません）。 -/
theorem blockRoot_parent_prevBlock_e_zero {Q : TrioSeq} {d n k a : ℕ}
    (hQ1 : 0 < Q.length) (hk : k + 1 < n)
    (h : nextrel1 (mTower Q d 0 n) a ((k + 1) * Q.length)) :
    k * Q.length ≤ a := by
  by_contra hlt
  have hx0 : a % Q.length < Q.length := Nat.mod_lt _ hQ1
  have hdiv : a / Q.length * Q.length + a % Q.length = a := Nat.div_add_mod' a Q.length
  have hmk : a / Q.length ≤ k := by
    have : a / Q.length * Q.length ≤ a := by omega
    by_contra hc
    have hge : (k + 1) * Q.length ≤ a / Q.length * Q.length :=
      Nat.mul_le_mul_right _ (by omega)
    have hsucc : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
    omega
  have hle0 : le0 (mTower Q d 0 n) (a / Q.length * Q.length + a % Q.length)
      ((k + 1) * Q.length) := by rw [hdiv]; exact h.2.2.2.2.1
  have hshift := le0_mTower_block_shift hQ1 hmk hx0 hk hle0
  have hlt2 : k * Q.length + a % Q.length < (k + 1) * Q.length := by
    have hsucc : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
    omega
  have hmin := h.2.2.2.2.2 (k * Q.length + a % Q.length) ⟨by omega, hshift⟩
  rw [entry1_mTower_block_e_zero Q d n k (a % Q.length) (by omega) hx0] at hmin
  have hstrict : entry (mTower Q d 0 n) 1 a
      < entry (mTower Q d 0 n) 1 ((k + 1) * Q.length) := h.2.2.2.1
  have ha : entry (mTower Q d 0 n) 1 a = entry Q 1 (a % Q.length) := by
    have hh := entry1_mTower_block_e_zero Q d n (a / Q.length) (a % Q.length)
      (by omega) hx0
    rwa [hdiv] at hh
  omega

/-- ★★★★★ **(q3b) `he` を落とした版**: `0 < e` は要りません。 -/
theorem blockRoot_parent_prevBlock_noE {Q : TrioSeq} {d e n k a : ℕ}
    (hQne : Q ≠ []) (hd : 0 < d) (hk : k + 1 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (h : nextrel1 (mTower Q d e n) a ((k + 1) * Q.length)) :
    k * Q.length ≤ a := by
  have hQ1 : 0 < Q.length := List.length_pos_iff.mpr hQne
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact blockRoot_parent_prevBlock_e_zero hQ1 hk h
  · exact blockRoot_parent_prevBlock hQne hd he hk hr0 h


/-! ## ★ ZeroDOK (d = 0 の枝) —— §294 -/

/-- `d = e = 0` の塔は同一コピーの連結。 -/
theorem h12_shiftr01_zero_zero (Q : TrioSeq) : shiftr01 0 0 Q = Q := by
  unfold shiftr01
  refine List.ext_getElem (by simp) ?_
  intro i h1 h2
  simp

theorem h12_mTower_zero_zero (Q : TrioSeq) (n : ℕ) :
    mTower Q 0 0 n = (List.range n).flatMap fun _ => Q := by
  unfold mTower
  congr 1
  funext k
  simp only [Nat.zero_mul, Lift1_zero, h12_shiftr01_zero_zero]

/-- ★★★ **接頭辞つきの `d = e = 0` の枝は無料**。 -/
theorem prefix_mTower_d0_mem {u : ℕ} {A Q : TrioSeq}
    (hA : A ∈ W u) (hQ : Q ∈ W u) (hb : entry Q 0 0 = 0) (n : ℕ) :
    A ++ mTower Q 0 0 n ∈ W u := by
  rw [h12_mTower_zero_zero]
  exact L105.prefixCopies_of_based hA hQ hb

theorem entry0_mTower_block_d_zero {Q : TrioSeq} {e n k q : ℕ}
    (hk : k < n) (hq : q < Q.length) :
    entry (mTower Q 0 e n) 0 (k * Q.length + q) = entry Q 0 q := by
  rw [mTower_entry hk hq, entry0_Lift1, Nat.zero_mul, h12_shiftr01_zero_zero]

theorem entry0_mTower_blockRoot_d_zero {Q : TrioSeq} {e n k : ℕ}
    (hQ1 : 0 < Q.length) (hk : k < n) :
    entry (mTower Q 0 e n) 0 (k * Q.length) = entry Q 0 0 := by
  have := entry0_mTower_block_d_zero (Q := Q) (e := e) (n := n) (k := k) (q := 0) hk hQ1
  simpa using this

/-- ★ **ブロック根の行 0 は塔全体の最小値**。 -/
theorem entry0_mTower_min_d_zero {Q : TrioSeq} {e n m : ℕ} (hQ1 : 0 < Q.length)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hm : m < (mTower Q 0 e n).length) :
    entry Q 0 0 ≤ entry (mTower Q 0 e n) 0 m := by
  have hlen : (mTower Q 0 e n).length = n * Q.length := mTower_length Q 0 e n
  rw [hlen] at hm
  have hq : m % Q.length < Q.length := Nat.mod_lt _ hQ1
  have hk : m / Q.length < n := by
    refine Nat.div_lt_of_lt_mul ?_
    rw [Nat.mul_comm]; exact hm
  have hsplit : m = (m / Q.length) * Q.length + m % Q.length := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod m Q.length).symm
  rw [hsplit, entry0_mTower_block_d_zero hk hq]
  rcases Nat.eq_zero_or_pos (m % Q.length) with h0 | hp
  · rw [h0]
  · exact Nat.le_of_lt (hr0 _ hp hq)

/-- ★★ **ブロック根に入る `nextrel0` は無い**。 -/
theorem no_nextrel0_blockRoot_d_zero {Q : TrioSeq} {e n k a : ℕ} (hQ1 : 0 < Q.length)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hk : k < n) :
    ¬ nextrel0 (mTower Q 0 e n) a (k * Q.length) := by
  rintro ⟨ha, -, -, hlt, -⟩
  rw [entry0_mTower_blockRoot_d_zero hQ1 hk] at hlt
  exact absurd (entry0_mTower_min_d_zero hQ1 hr0 ha) (by omega)

/-- ★★ `le0` でブロック根に届くのは自分だけ。 -/
theorem le0_blockRoot_d_zero {Q : TrioSeq} {e n k a : ℕ} (hQ1 : 0 < Q.length)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hk : k < n)
    (h : le0 (mTower Q 0 e n) a (k * Q.length)) : a = k * Q.length := by
  obtain ⟨-, -, hrt⟩ := h
  rcases Relation.ReflTransGen.cases_tail hrt with h1 | ⟨c, -, hc⟩
  · exact h1.symm
  · exact absurd hc (no_nextrel0_blockRoot_d_zero hQ1 hr0 hk)

/-- ★★ ブロック根に入る `nextrel1` も無い。 -/
theorem no_nextrel1_blockRoot_d_zero {Q : TrioSeq} {e n k a : ℕ} (hQ1 : 0 < Q.length)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hk : k < n) :
    ¬ nextrel1 (mTower Q 0 e n) a (k * Q.length) := by
  rintro ⟨-, -, hab, -, hle0, -⟩
  have := le0_blockRoot_d_zero hQ1 hr0 hk hle0
  omega

/-- ★★ `le1` でブロック根に届くのも自分だけ。 -/
theorem le1_blockRoot_d_zero {Q : TrioSeq} {e n k a : ℕ} (hQ1 : 0 < Q.length)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hk : k < n)
    (h : le1 (mTower Q 0 e n) a (k * Q.length)) : a = k * Q.length := by
  obtain ⟨-, -, hrt⟩ := h
  rcases Relation.ReflTransGen.cases_tail hrt with h1 | ⟨c, -, hc⟩
  · exact h1.symm
  · exact absurd hc (no_nextrel1_blockRoot_d_zero hQ1 hr0 hk)

/-- ★★★★★ **`d = 0` の塔では、ブロック根はどの行にも親を持たない（孤児）**。 -/
theorem no_hasParent_blockRoot_d_zero {Q : TrioSeq} {e n k r : ℕ} (hQ1 : 0 < Q.length)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hk : k < n) :
    ¬ hasParent (mTower Q 0 e n) r (k * Q.length) := by
  rintro ⟨a, ha, -⟩
  unfold nextR at ha
  by_cases h0 : r = 0
  · rw [if_pos h0] at ha
    exact no_nextrel0_blockRoot_d_zero hQ1 hr0 hk ha
  · rw [if_neg h0] at ha
    by_cases h1 : r = 1
    · rw [if_pos h1] at ha
      exact no_nextrel1_blockRoot_d_zero hQ1 hr0 hk ha
    · rw [if_neg h1] at ha
      obtain ⟨-, -, hab, -, hle1, -⟩ := ha
      have := le1_blockRoot_d_zero hQ1 hr0 hk hle1
      omega


/-- 塔の側の列は行 0 が `entry Q 0 0` 以上（接頭辞つき）。 -/
theorem entry0_prefix_mTower_min_d_zero {A Q : TrioSeq} {e n m : ℕ} (hQ1 : 0 < Q.length)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hm1 : A.length ≤ m) (hm2 : m < (A ++ mTower Q 0 e n).length) :
    entry Q 0 0 ≤ entry (A ++ mTower Q 0 e n) 0 m := by
  obtain ⟨r, rfl⟩ : ∃ r, m = A.length + r := ⟨m - A.length, by omega⟩
  rw [entry_append_right]
  refine entry0_mTower_min_d_zero hQ1 hr0 ?_
  rw [List.length_append] at hm2; omega

/-- ブロック根の行 0（接頭辞つき）。 -/
theorem entry0_prefix_blockRoot_d_zero {A Q : TrioSeq} {e n k : ℕ}
    (hQ1 : 0 < Q.length) (hk : k < n) :
    entry (A ++ mTower Q 0 e n) 0 (A.length + k * Q.length) = entry Q 0 0 := by
  rw [entry_append_right]
  exact entry0_mTower_blockRoot_d_zero hQ1 hk

/-- ★★ ブロック根の `nextrel0` の親は**接頭辞の中にしかいない**。 -/
theorem nextrel0_prefix_blockRoot_src_d_zero {A Q : TrioSeq} {e n k a : ℕ}
    (hQ1 : 0 < Q.length)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hk : k < n)
    (h : nextrel0 (A ++ mTower Q 0 e n) a (A.length + k * Q.length)) :
    a < A.length := by
  obtain ⟨ha, -, -, hlt, -⟩ := h
  by_contra hc
  push Not at hc
  rw [entry0_prefix_blockRoot_d_zero hQ1 hk] at hlt
  exact absurd (entry0_prefix_mTower_min_d_zero hQ1 hr0 hc ha) (by omega)

/-- ★★★ **`nextrel0` の親は全ブロック根で共通**（`k` 番目 ⟺ `0` 番目、同じ列 `a`）。 -/
theorem nextrel0_prefix_blockRoot_iff_d_zero {A Q : TrioSeq} {e n k a : ℕ}
    (hQ1 : 0 < Q.length) (hn : 0 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hk : k < n) :
    nextrel0 (A ++ mTower Q 0 e n) a (A.length + k * Q.length)
      ↔ nextrel0 (A ++ mTower Q 0 e n) a A.length := by
  have hMlen : (A ++ mTower Q 0 e n).length = A.length + n * Q.length := by
    rw [List.length_append, mTower_length]
  have hA0 : A.length = A.length + 0 * Q.length := by omega
  have hek : entry (A ++ mTower Q 0 e n) 0 (A.length + k * Q.length) = entry Q 0 0 :=
    entry0_prefix_blockRoot_d_zero hQ1 hk
  have he0 : entry (A ++ mTower Q 0 e n) 0 A.length = entry Q 0 0 := by
    rw [hA0]; exact entry0_prefix_blockRoot_d_zero hQ1 hn
  have hnq : 0 < n * Q.length := Nat.mul_pos hn hQ1
  have hkq : (k + 1) * Q.length ≤ n * Q.length := Nat.mul_le_mul_right _ (by omega)
  have hsk : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
  have hlt0 : A.length < (A ++ mTower Q 0 e n).length := by omega
  have hltk : A.length + k * Q.length < (A ++ mTower Q 0 e n).length := by omega
  constructor
  · intro h
    have hain := nextrel0_prefix_blockRoot_src_d_zero hQ1 hr0 hk h
    obtain ⟨ha, -, -, hlt, hmin⟩ := h
    refine ⟨ha, hlt0, hain, by rw [he0, ← hek]; exact hlt, ?_⟩
    intro j hj
    rw [he0, ← hek]
    exact hmin j ⟨hj.1, by omega⟩
  · rintro ⟨ha, -, hab, hlt, hmin⟩
    refine ⟨ha, hltk, by omega, by rw [hek, ← he0]; exact hlt, ?_⟩
    intro j hj
    rw [hek]
    rcases Nat.lt_or_ge j A.length with hjl | hjr
    · have := hmin j ⟨hj.1, hjl⟩
      rw [he0] at this; exact this
    · exact entry0_prefix_mTower_min_d_zero hQ1 hr0 hjr (by omega)

/-- ★★★★★ **`d = 0`: `k` 番目のブロック根が行 0 の親を持つ ⟺ `Q` の根が持つ**
（しかも親の列は同じ）。 -/
theorem hasParent0_prefix_blockRoot_iff_d_zero {A Q : TrioSeq} {e n k : ℕ}
    (hQ1 : 0 < Q.length) (hn : 0 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hk : k < n) :
    hasParent (A ++ mTower Q 0 e n) 0 (A.length + k * Q.length)
      ↔ hasParent (A ++ mTower Q 0 e n) 0 A.length := by
  have hiff : ∀ a, nextR (A ++ mTower Q 0 e n) 0 a (A.length + k * Q.length)
      ↔ nextR (A ++ mTower Q 0 e n) 0 a A.length := by
    intro a
    unfold nextR
    rw [if_pos rfl]
    exact nextrel0_prefix_blockRoot_iff_d_zero hQ1 hn hr0 hk
  constructor
  · rintro ⟨a, ha, hu⟩
    exact ⟨a, (hiff a).mp ha, fun b hb => hu b ((hiff b).mpr hb)⟩
  · rintro ⟨a, ha, hu⟩
    exact ⟨a, (hiff a).mpr ha, fun b hb => hu b ((hiff b).mp hb)⟩


theorem entry1_mTower_blockRoot_d_zero {Q : TrioSeq} {e n k : ℕ}
    (hQne : Q ≠ []) (hQ1 : 0 < Q.length) (hk : k < n) :
    entry (mTower Q 0 e n) 1 (k * Q.length) = entry Q 1 0 + e * k := by
  have h := mTower_entry (Q := Q) (d := 0) (e := e) (n := n) (k := k) (q := 0) (i := 1) hk hQ1
  rw [Nat.add_zero] at h
  rw [h, Nat.zero_mul, h12_shiftr01_zero_zero, L53.entry1_Lift1_zero hQne]

theorem entry2_mTower_blockRoot_d_zero {Q : TrioSeq} {e n k : ℕ}
    (hQ1 : 0 < Q.length) (hk : k < n) :
    entry (mTower Q 0 e n) 2 (k * Q.length) = entry Q 2 0 := by
  have h := mTower_entry (Q := Q) (d := 0) (e := e) (n := n) (k := k) (q := 0) (i := 2) hk hQ1
  rw [Nat.add_zero] at h
  rw [h, Nat.zero_mul, h12_shiftr01_zero_zero, Wset.entry2_Lift1]

/-- ★★ **`hz0` があればブロック根の `srow` は 0 か 1**（行 2 は使わない）。 -/
theorem srow_prefix_blockRoot_d_zero {A Q : TrioSeq} {e n k : ℕ}
    (hQne : Q ≠ []) (hQ1 : 0 < Q.length) (hz0 : entry Q 2 0 = 0) (hk : k < n) :
    srow (A ++ mTower Q 0 e n) (A.length + k * Q.length)
      = if 0 < entry Q 1 0 + e * k then 1 else 0 := by
  unfold srow
  rw [entry_append_right, entry_append_right,
    entry2_mTower_blockRoot_d_zero hQ1 hk, hz0,
    entry1_mTower_blockRoot_d_zero hQne hQ1 hk]
  simp

/-- ★★★ **`le0` の祖先集合も全ブロック根で一致する**。 -/
theorem le0_prefix_blockRoot_iff_d_zero {A Q : TrioSeq} {e n k j : ℕ}
    (hQ1 : 0 < Q.length) (hn : 0 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hk : k < n)
    (hj : j < A.length) :
    le0 (A ++ mTower Q 0 e n) j (A.length + k * Q.length)
      ↔ le0 (A ++ mTower Q 0 e n) j A.length := by
  have hMlen : (A ++ mTower Q 0 e n).length = A.length + n * Q.length := by
    rw [List.length_append, mTower_length]
  have hnq : 0 < n * Q.length := Nat.mul_pos hn hQ1
  have hkq : (k + 1) * Q.length ≤ n * Q.length := Nat.mul_le_mul_right _ (by omega)
  have hsk : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
  have hlt0 : A.length < (A ++ mTower Q 0 e n).length := by omega
  have hltk : A.length + k * Q.length < (A ++ mTower Q 0 e n).length := by omega
  have hA0 : A.length = A.length + 0 * Q.length := by omega
  constructor
  · rintro ⟨hjl, -, hrt⟩
    refine ⟨hjl, hlt0, ?_⟩
    rcases Relation.ReflTransGen.cases_tail hrt with h1 | ⟨c, hc1, hc2⟩
    · omega
    · exact hc1.tail
        ((nextrel0_prefix_blockRoot_iff_d_zero hQ1 hn hr0 hk).mp hc2)
  · rintro ⟨hjl, -, hrt⟩
    refine ⟨hjl, hltk, ?_⟩
    rcases Relation.ReflTransGen.cases_tail hrt with h1 | ⟨c, hc1, hc2⟩
    · omega
    · refine hc1.tail ((nextrel0_prefix_blockRoot_iff_d_zero hQ1 hn hr0 hk).mpr ?_)
      rw [hA0] at hc2 ⊢
      exact hc2


/-- ★★ `e = 0`: ブロック根の `srow` は `Q` の根の `srow` と同じ。 -/
theorem srow_prefix_blockRoot_e_zero {A Q : TrioSeq} {d n k : ℕ}
    (_hQne : Q ≠ []) (hQ1 : 0 < Q.length) (hk : k < n) :
    srow (A ++ mTower Q d 0 n) (A.length + k * Q.length) = srow Q 0 := by
  unfold srow
  have h1 : entry (A ++ mTower Q d 0 n) 1 (A.length + k * Q.length) = entry Q 1 0 := by
    rw [entry_append_right]
    have := entry1_mTower_block_e_zero Q d n k 0 hk hQ1
    rwa [Nat.add_zero] at this
  have h2 : entry (A ++ mTower Q d 0 n) 2 (A.length + k * Q.length) = entry Q 2 0 := by
    rw [entry_append_right]
    exact entry2_mTower_blockRoot Q d 0 n k hk hQ1
  rw [h1, h2]


theorem rtg0_index_le {M : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 M) a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl _
  | tail _ hstep ih => exact le_trans ih (le_of_lt hstep.2.2.1)

theorem entry1_prefix_blockRoot_d_zero {A Q : TrioSeq} {e n k : ℕ}
    (hQne : Q ≠ []) (hQ1 : 0 < Q.length) (hk : k < n) :
    entry (A ++ mTower Q 0 e n) 1 (A.length + k * Q.length) = entry Q 1 0 + e * k := by
  rw [entry_append_right]
  exact entry1_mTower_blockRoot_d_zero hQne hQ1 hk

/-- ★★ `le0` でブロック根に届く列は、自分自身か**接頭辞の中**。 -/
theorem le0_prefix_blockRoot_src_d_zero {A Q : TrioSeq} {e n k a : ℕ}
    (hQ1 : 0 < Q.length)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hk : k < n)
    (h : le0 (A ++ mTower Q 0 e n) a (A.length + k * Q.length))
    (hne : a ≠ A.length + k * Q.length) : a < A.length := by
  obtain ⟨-, -, hrt⟩ := h
  rcases Relation.ReflTransGen.cases_tail hrt with h1 | ⟨c, hc1, hc2⟩
  · exact absurd h1.symm hne
  · exact Nat.lt_of_le_of_lt (rtg0_index_le hc1)
      (nextrel0_prefix_blockRoot_src_d_zero hQ1 hr0 hk hc2)

/-- ★★★★★★ **`d = 0`: `nextrel1` の条件から塔が消える**。
右辺に現れるのは接頭辞 `A` の中の列と、閾値 `entry Q 1 0 + e*k` だけ。 -/
theorem nextrel1_prefix_blockRoot_iff_d_zero {A Q : TrioSeq} {e n k a : ℕ}
    (hQne : Q ≠ []) (hQ1 : 0 < Q.length) (hn : 0 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hk : k < n) :
    nextrel1 (A ++ mTower Q 0 e n) a (A.length + k * Q.length)
      ↔ (a < A.length ∧ le0 (A ++ mTower Q 0 e n) a A.length ∧
          entry (A ++ mTower Q 0 e n) 1 a < entry Q 1 0 + e * k ∧
          ∀ j, j < A.length → a < j → le0 (A ++ mTower Q 0 e n) j A.length →
            entry Q 1 0 + e * k ≤ entry (A ++ mTower Q 0 e n) 1 j) := by
  have hMlen : (A ++ mTower Q 0 e n).length = A.length + n * Q.length := by
    rw [List.length_append, mTower_length]
  have hnq : 0 < n * Q.length := Nat.mul_pos hn hQ1
  have hkq : (k + 1) * Q.length ≤ n * Q.length := Nat.mul_le_mul_right _ (by omega)
  have hsk : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
  have hlt0 : A.length < (A ++ mTower Q 0 e n).length := by omega
  have hltk : A.length + k * Q.length < (A ++ mTower Q 0 e n).length := by omega
  have hval : entry (A ++ mTower Q 0 e n) 1 (A.length + k * Q.length)
      = entry Q 1 0 + e * k := entry1_prefix_blockRoot_d_zero hQne hQ1 hk
  constructor
  · rintro ⟨ha, -, hab, hlt, hle0, hmin⟩
    have hain : a < A.length :=
      le0_prefix_blockRoot_src_d_zero hQ1 hr0 hk hle0 (by omega)
    refine ⟨hain, (le0_prefix_blockRoot_iff_d_zero hQ1 hn hr0 hk hain).mp hle0,
      by rwa [hval] at hlt, ?_⟩
    intro j hjA haj hj0
    have := hmin j ⟨haj, (le0_prefix_blockRoot_iff_d_zero hQ1 hn hr0 hk hjA).mpr hj0⟩
    rwa [hval] at this
  · rintro ⟨hain, hle0A, hlt, hmin⟩
    refine ⟨by omega, hltk, by omega, by rw [hval]; exact hlt,
      (le0_prefix_blockRoot_iff_d_zero hQ1 hn hr0 hk hain).mpr hle0A, ?_⟩
    intro j hj
    rw [hval]
    by_cases hje : j = A.length + k * Q.length
    · rw [hje, hval]
    · have hjA : j < A.length :=
        le0_prefix_blockRoot_src_d_zero hQ1 hr0 hk hj.2 hje
      exact hmin j hjA hj.1
        ((le0_prefix_blockRoot_iff_d_zero hQ1 hn hr0 hk hjA).mp hj.2)

/-- `nextrel0` の始点は一意（最小性から）。 -/
theorem nextrel0_src_unique {M : TrioSeq} {c1 c2 j1 : ℕ}
    (h1 : nextrel0 M c1 j1) (h2 : nextrel0 M c2 j1) : c1 = c2 := by
  obtain ⟨-, -, hc1, hlt1, hmin1⟩ := h1
  obtain ⟨-, -, hc2, hlt2, hmin2⟩ := h2
  rcases Nat.lt_trichotomy c1 c2 with h | h | h
  · exact absurd (hmin1 c2 ⟨h, hc2⟩) (by omega)
  · exact h
  · exact absurd (hmin2 c1 ⟨h, hc1⟩) (by omega)

/-- `le0` で `j1` に届く列は、その行 0 の親 `a0` 以下。 -/
theorem le0_le_parent0 {M : TrioSeq} {a0 j j1 : ℕ}
    (ha0 : nextrel0 M a0 j1) (h : le0 M j j1) (hne : j ≠ j1) : j ≤ a0 := by
  obtain ⟨-, -, hrt⟩ := h
  rcases Relation.ReflTransGen.cases_tail hrt with h1 | ⟨c, hc1, hc2⟩
  · exact absurd h1.symm hne
  · rw [← nextrel0_src_unique hc2 ha0]
    exact rtg0_index_le hc1

/-- ★★★★★★★ **`d = 0`: 閾値を超えたブロック根の行 1 の親は `a0` に固定**。 -/
theorem nextrel1_prefix_blockRoot_parent0 {A Q : TrioSeq} {e n k a0 : ℕ}
    (hQne : Q ≠ []) (hQ1 : 0 < Q.length) (hn : 0 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hk : k < n)
    (ha0 : nextrel0 (A ++ mTower Q 0 e n) a0 A.length)
    (hc : entry (A ++ mTower Q 0 e n) 1 a0 < entry Q 1 0 + e * k) :
    nextrel1 (A ++ mTower Q 0 e n) a0 (A.length + k * Q.length) := by
  have ha0A : a0 < A.length := ha0.2.2.1
  refine (nextrel1_prefix_blockRoot_iff_d_zero hQne hQ1 hn hr0 hk).mpr
    ⟨ha0A, ⟨ha0.1, ha0.2.1, Relation.ReflTransGen.single ha0⟩, hc, ?_⟩
  intro j hjA haj hj0
  exact absurd (le0_le_parent0 ha0 hj0 (by omega)) (by omega)

/-- ★★★★★★★ **しかも一意** ⟹ `hasParent` が出る。 -/
theorem hasParent1_prefix_blockRoot_d_zero {A Q : TrioSeq} {e n k a0 : ℕ}
    (hQne : Q ≠ []) (hQ1 : 0 < Q.length) (hn : 0 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hk : k < n)
    (ha0 : nextrel0 (A ++ mTower Q 0 e n) a0 A.length)
    (hc : entry (A ++ mTower Q 0 e n) 1 a0 < entry Q 1 0 + e * k) :
    hasParent (A ++ mTower Q 0 e n) 1 (A.length + k * Q.length) := by
  refine ⟨a0, ?_, ?_⟩
  · show nextR (A ++ mTower Q 0 e n) 1 a0 (A.length + k * Q.length)
    unfold nextR
    rw [if_neg (by omega), if_pos rfl]
    exact nextrel1_prefix_blockRoot_parent0 hQne hQ1 hn hr0 hk ha0 hc
  · intro b hb
    unfold nextR at hb
    rw [if_neg (by omega), if_pos rfl] at hb
    obtain ⟨hbA, hb0, hblt, hbmin⟩ :=
      (nextrel1_prefix_blockRoot_iff_d_zero hQne hQ1 hn hr0 hk).mp hb
    have hup : b ≤ a0 := le0_le_parent0 ha0 hb0 (by omega)
    rcases Nat.lt_or_ge b a0 with hlt | hge
    · exact absurd (hbmin a0 ha0.2.2.1 hlt
        ⟨ha0.1, ha0.2.1, Relation.ReflTransGen.single ha0⟩) (by omega)
    · omega

/-- ★★★ 逆に **`Q` の根に行 0 の親が無ければ、全ブロック根は行 1 でも孤児**。 -/
theorem no_hasParent1_prefix_blockRoot_d_zero {A Q : TrioSeq} {e n k : ℕ}
    (hQne : Q ≠ []) (hQ1 : 0 < Q.length) (hn : 0 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hk : k < n)
    (hnp : ∀ a, ¬ nextrel0 (A ++ mTower Q 0 e n) a A.length) :
    ¬ hasParent (A ++ mTower Q 0 e n) 1 (A.length + k * Q.length) := by
  rintro ⟨b, hb, -⟩
  unfold nextR at hb
  rw [if_neg (by omega), if_pos rfl] at hb
  obtain ⟨hbA, hb0, -, -⟩ :=
    (nextrel1_prefix_blockRoot_iff_d_zero hQne hQ1 hn hr0 hk).mp hb
  obtain ⟨-, -, hrt⟩ := hb0
  rcases Relation.ReflTransGen.cases_tail hrt with h1 | ⟨c, -, hc2⟩
  · omega
  · exact hnp c hc2

/-- ★★★ 行 0 も同様に孤児。 -/
theorem no_hasParent0_prefix_blockRoot_d_zero {A Q : TrioSeq} {e n k : ℕ}
    (hQ1 : 0 < Q.length) (hn : 0 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hk : k < n)
    (hnp : ∀ a, ¬ nextrel0 (A ++ mTower Q 0 e n) a A.length) :
    ¬ hasParent (A ++ mTower Q 0 e n) 0 (A.length + k * Q.length) := by
  rintro ⟨b, hb, -⟩
  unfold nextR at hb
  rw [if_pos rfl] at hb
  exact hnp b ((nextrel0_prefix_blockRoot_iff_d_zero hQ1 hn hr0 hk).mp hb)


/-- ★ **ブロック根の行 1 の親は必ず接頭辞 `A` の中**（塔の列は決して親にならない）。 -/
theorem nextrel1_prefix_blockRoot_src_d_zero {A Q : TrioSeq} {e n k a : ℕ}
    (hQne : Q ≠ []) (hQ1 : 0 < Q.length) (hn : 0 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hk : k < n)
    (h : nextrel1 (A ++ mTower Q 0 e n) a (A.length + k * Q.length)) :
    a < A.length :=
  ((nextrel1_prefix_blockRoot_iff_d_zero hQne hQ1 hn hr0 hk).mp h).1

/-- ★★★ **親は `k` について単調に上がる**（鎖を `a0` に向かって上るだけ）。 -/
theorem nextrel1_prefix_blockRoot_mono_d_zero {A Q : TrioSeq} {e n k k' a b : ℕ}
    (hQne : Q ≠ []) (hQ1 : 0 < Q.length) (hn : 0 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hk : k < n) (hk' : k' < n) (hkk : k ≤ k')
    (ha : nextrel1 (A ++ mTower Q 0 e n) a (A.length + k * Q.length))
    (hb : nextrel1 (A ++ mTower Q 0 e n) b (A.length + k' * Q.length)) :
    a ≤ b := by
  obtain ⟨haA, ha0, halt, -⟩ :=
    (nextrel1_prefix_blockRoot_iff_d_zero hQne hQ1 hn hr0 hk).mp ha
  obtain ⟨-, -, -, hbmin⟩ :=
    (nextrel1_prefix_blockRoot_iff_d_zero hQne hQ1 hn hr0 hk').mp hb
  by_contra hc
  push Not at hc
  have hle : entry Q 1 0 + e * k ≤ entry Q 1 0 + e * k' := by
    have : e * k ≤ e * k' := Nat.mul_le_mul_left e hkk
    omega
  exact absurd (hbmin a haA hc ha0) (by omega)

open Classical in
/-- ★★★★★★★ **存在も完全に決まる**: ブロック根が行 1 の親を持つ ⟺
`A` の中の `le0` 祖先で行 1 が閾値未満のものが 1 つでもある。 -/
theorem hasParent1_prefix_blockRoot_iff_d_zero {A Q : TrioSeq} {e n k : ℕ}
    (hQne : Q ≠ []) (hQ1 : 0 < Q.length) (hn : 0 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hk : k < n) :
    hasParent (A ++ mTower Q 0 e n) 1 (A.length + k * Q.length)
      ↔ ∃ j, j < A.length ∧ le0 (A ++ mTower Q 0 e n) j A.length ∧
             entry (A ++ mTower Q 0 e n) 1 j < entry Q 1 0 + e * k := by
  set M := A ++ mTower Q 0 e n with hM
  have hiff := fun a => nextrel1_prefix_blockRoot_iff_d_zero
    (A := A) (Q := Q) (e := e) (n := n) (k := k) (a := a) hQne hQ1 hn hr0 hk
  constructor
  · rintro ⟨a, ha, -⟩
    unfold nextR at ha
    rw [if_neg (by omega), if_pos rfl] at ha
    obtain ⟨h1, h2, h3, -⟩ := (hiff a).mp ha
    exact ⟨a, h1, h2, h3⟩
  · rintro ⟨j0, hj0A, hj00, hj0c⟩
    set T := (Finset.range A.length).filter
      (fun j => le0 M j A.length ∧ entry M 1 j < entry Q 1 0 + e * k) with hT
    have hj0T : j0 ∈ T := by
      rw [hT, Finset.mem_filter, Finset.mem_range]
      exact ⟨hj0A, hj00, hj0c⟩
    have hTne : T.Nonempty := ⟨j0, hj0T⟩
    set b := T.max' hTne with hb
    have hbT : b ∈ T := T.max'_mem hTne
    rw [hT, Finset.mem_filter, Finset.mem_range] at hbT
    obtain ⟨hbA, hb0, hbc⟩ := hbT
    have hbmax : ∀ j, j < A.length → b < j → le0 M j A.length →
        entry Q 1 0 + e * k ≤ entry M 1 j := by
      intro j hjA hbj hj0
      by_contra hcon
      push Not at hcon
      have hjT : j ∈ T := by
        rw [hT, Finset.mem_filter, Finset.mem_range]
        exact ⟨hjA, hj0, hcon⟩
      exact absurd (T.le_max' j hjT) (by omega)
    have hbn : nextrel1 M b (A.length + k * Q.length) :=
      (hiff b).mpr ⟨hbA, hb0, hbc, hbmax⟩
    refine ⟨b, ?_, ?_⟩
    · show nextR M 1 b (A.length + k * Q.length)
      unfold nextR; rw [if_neg (by omega), if_pos rfl]; exact hbn
    · intro y hy
      unfold nextR at hy
      rw [if_neg (by omega), if_pos rfl] at hy
      obtain ⟨hyA, hy0, hyc, hymin⟩ := (hiff y).mp hy
      rcases Nat.lt_trichotomy y b with h | h | h
      · exact absurd (hymin b hbA h hb0) (Nat.not_le.mpr hbc)
      · exact h
      · exact absurd (hbmax y hyA h hy0) (Nat.not_le.mpr hyc)


/-- ★★★ **ブロックの中の `nextrel0` は `Q` の中の `nextrel0` と同値**。 -/
theorem nextrel0_mTower_intra_block (Q : TrioSeq) {d e n k i' i : ℕ}
    (hk : k < n) (hi' : i' < Q.length) (hi : i < Q.length) :
    nextrel0 (mTower Q d e n) (k * Q.length + i') (k * Q.length + i) ↔ nextrel0 Q i' i := by
  have hlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have hkq : (k + 1) * Q.length ≤ n * Q.length := Nat.mul_le_mul_right _ (by omega)
  have hsk : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
  have hb : ∀ m, m < Q.length → k * Q.length + m < (mTower Q d e n).length := by
    intro m hm; omega
  constructor
  · rintro ⟨-, -, hab, hlt, hmin⟩
    rw [entry0_mTower_block Q d e n k i' hk hi', entry0_mTower_block Q d e n k i hk hi] at hlt
    refine ⟨hi', hi, by omega, by omega, ?_⟩
    intro j hj
    have hjq : j < Q.length := by omega
    have := hmin (k * Q.length + j) ⟨by omega, by omega⟩
    rw [entry0_mTower_block Q d e n k i hk hi, entry0_mTower_block Q d e n k _ hk hjq] at this
    omega
  · rintro ⟨-, -, hab, hlt, hmin⟩
    refine ⟨hb i' hi', hb i hi, by omega, ?_, ?_⟩
    · rw [entry0_mTower_block Q d e n k i' hk hi', entry0_mTower_block Q d e n k i hk hi]; omega
    · intro j hj
      have hjq : j - k * Q.length < Q.length := by omega
      have hjeq : j = k * Q.length + (j - k * Q.length) := by omega
      rw [entry0_mTower_block Q d e n k i hk hi, hjeq, entry0_mTower_block Q d e n k _ hk hjq]
      have := hmin (j - k * Q.length) ⟨by omega, by omega⟩
      omega

/-- ★★★★ **ブロック根の行 0 の親は「前のブロックの固定された位置」**（`k` に依らない）。
`d`・`e` に依らない一般の道具。 -/
theorem nextrel0_blockRoot_shift (Q : TrioSeq) {d e n k i : ℕ}
    (hQ1 : 0 < Q.length) (hi : i < Q.length) (hk2 : k + 2 < n) :
    nextrel0 (mTower Q d e n) (k * Q.length + i) ((k + 1) * Q.length)
      ↔ nextrel0 (mTower Q d e n) ((k + 1) * Q.length + i) ((k + 2) * Q.length) := by
  have hlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have h3 : (k + 3) * Q.length ≤ n * Q.length := Nat.mul_le_mul_right _ (by omega)
  have e1 : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
  have e2 : (k + 2) * Q.length = (k + 1) * Q.length + Q.length := Nat.succ_mul (k + 1) Q.length
  have e3 : (k + 3) * Q.length = (k + 2) * Q.length + Q.length := Nat.succ_mul (k + 2) Q.length
  have hr : ∀ m, m < Q.length → ∀ j, j < n →
      entry (mTower Q d e n) 0 (j * Q.length + m) = entry Q 0 m + d * j :=
    fun m hm j hj => entry0_mTower_block Q d e n j m hj hm
  have hz1 : entry (mTower Q d e n) 0 ((k + 1) * Q.length) = entry Q 0 0 + d * (k + 1) := by
    have := hr 0 hQ1 (k + 1) (by omega); simpa using this
  have hz2 : entry (mTower Q d e n) 0 ((k + 2) * Q.length) = entry Q 0 0 + d * (k + 2) := by
    have := hr 0 hQ1 (k + 2) (by omega); simpa using this
  have hi1 : entry (mTower Q d e n) 0 (k * Q.length + i) = entry Q 0 i + d * k :=
    hr i hi k (by omega)
  have hi2 : entry (mTower Q d e n) 0 ((k + 1) * Q.length + i) = entry Q 0 i + d * (k + 1) :=
    hr i hi (k + 1) (by omega)
  have hdk : d * (k + 1) = d * k + d := by rw [Nat.mul_succ]
  have hdk2 : d * (k + 2) = d * (k + 1) + d := by rw [Nat.mul_succ]
  constructor
  · rintro ⟨-, -, hab, hlt, hmin⟩
    rw [hi1, hz1] at hlt
    refine ⟨by omega, by omega, by omega, by rw [hi2, hz2]; omega, ?_⟩
    intro j hj
    have hjq : j - (k + 1) * Q.length < Q.length := by omega
    have hjeq : j = (k + 1) * Q.length + (j - (k + 1) * Q.length) := by omega
    have hj1 := hmin (k * Q.length + (j - (k + 1) * Q.length)) ⟨by omega, by omega⟩
    rw [hr _ hjq k (by omega), hz1] at hj1
    rw [hz2, hjeq, hr _ hjq (k + 1) (by omega)]
    omega
  · rintro ⟨-, -, hab, hlt, hmin⟩
    rw [hi2, hz2] at hlt
    refine ⟨by omega, by omega, by omega, by rw [hi1, hz1]; omega, ?_⟩
    intro j hj
    have hjq : j - k * Q.length < Q.length := by omega
    have hjeq : j = k * Q.length + (j - k * Q.length) := by omega
    have hj1 := hmin ((k + 1) * Q.length + (j - k * Q.length)) ⟨by omega, by omega⟩
    rw [hr _ hjq (k + 1) (by omega), hz2] at hj1
    rw [hz1, hjeq, hr _ hjq k (by omega)]
    omega


/-- ★★★ `d = 0` でも `0 < e` なら第 `k` ブロック（`k ≥ 1`）の根の行 1 は正。 -/
theorem blockRoot_row1_pos_of_e_pos {Q : TrioSeq} {d e n k : ℕ}
    (hQne : Q ≠ []) (he : 0 < e) (hk : k < n) (hk0 : 0 < k) :
    0 < entry (mTower Q d e n) 1 (k * Q.length) := by
  rw [entry1_mTower_blockRoot hQne d e n k hk]
  have : 0 < e * k := Nat.mul_pos he hk0
  omega

/-- ★★★ したがって末尾列（ブロック根）は非零。⟹ `hsnoc_zero_of_parent` の `hz` が出る。 -/
theorem blockRoot_nonzero_of_e_pos {Q : TrioSeq} {d e n k : ℕ}
    (hQne : Q ≠ []) (he : 0 < e) (hk : k < n) (hk0 : 0 < k) :
    ¬ (entry (mTower Q d e n) 0 (k * Q.length) = 0 ∧
       entry (mTower Q d e n) 1 (k * Q.length) = 0 ∧
       entry (mTower Q d e n) 2 (k * Q.length) = 0) := by
  rintro ⟨-, h1, -⟩
  have hp := blockRoot_row1_pos_of_e_pos (Q := Q) (d := d) (e := e) (n := n) (k := k)
    hQne he hk hk0
  omega


/-- `le0` で真に上がると行 0 は狭義に増える。 -/
theorem entry0_lt_of_le0_ne {M : TrioSeq} {a b : ℕ}
    (h : le0 M a b) (hne : a ≠ b) : entry M 0 a < entry M 0 b := by
  obtain ⟨-, -, hrt⟩ := h
  rcases Relation.ReflTransGen.cases_tail hrt with h1 | ⟨c, hc1, hc2⟩
  · exact absurd h1.symm hne
  · exact Nat.lt_of_le_of_lt (rtg0_entry_mono hc1) hc2.2.2.2.1

/-- `nextrel1` の始点は行 0 でも狭義に小さい。 -/
theorem entry0_lt_of_nextrel1 {M : TrioSeq} {a b : ℕ}
    (h : nextrel1 M a b) : entry M 0 a < entry M 0 b :=
  entry0_lt_of_le0_ne h.2.2.2.2.1 (Nat.ne_of_lt h.2.2.1)

/-- `le1` で真に上がると行 0 も狭義に増える。 -/
theorem entry0_lt_of_le1_ne {M : TrioSeq} {a b : ℕ}
    (h : le1 M a b) (hne : a ≠ b) : entry M 0 a < entry M 0 b := by
  obtain ⟨-, -, hrt⟩ := h
  rcases Relation.ReflTransGen.cases_tail hrt with h1 | ⟨c, hc1, hc2⟩
  · exact absurd h1.symm hne
  · refine Nat.lt_of_le_of_lt ?_ (entry0_lt_of_nextrel1 hc2)
    clear hc2
    induction hc1 with
    | refl => exact le_refl _
    | tail _ hstep ih => exact le_trans ih (le_of_lt (entry0_lt_of_nextrel1 hstep))

/-- ★★★ `nextrel2` の始点は**行 0 でも狭義に小さい**。⟹ `wd0 > 0`。 -/
theorem entry0_lt_of_nextrel2 {M : TrioSeq} {a b : ℕ}
    (h : nextrel2 M a b) : entry M 0 a < entry M 0 b :=
  entry0_lt_of_le1_ne h.2.2.2.2.1 (Nat.ne_of_lt h.2.2.1)

/-- ★★★★★ **`srow = 2` の段では、親の行 0 は末尾の行 0 より狭義に小さい**。
⟹ `wd0 = entry 0 (末尾) - entry 0 (親) > 0`。 -/
theorem entry0_parent_lt_of_srow2 {M : TrioSeq} {a b : ℕ}
    (h : nextR M 2 a b) : entry M 0 a < entry M 0 b := by
  unfold nextR at h
  rw [if_neg (by omega), if_neg (by omega)] at h
  exact entry0_lt_of_nextrel2 h

/-- 行 1 の段でも同じ（`srow = 1` のとき `wd0 > 0`）。 -/
theorem entry0_parent_lt_of_srow1 {M : TrioSeq} {a b : ℕ}
    (h : nextR M 1 a b) : entry M 0 a < entry M 0 b := by
  unfold nextR at h
  rw [if_neg (by omega), if_pos rfl] at h
  exact entry0_lt_of_nextrel1 h


/-- ★★ 行 0 で接頭辞から塔に入れるのは**塔の根だけ**。 -/
theorem nextrel0_cross_root {A T : TrioSeq}
    (hmin : ∀ m, 0 < m → m < T.length → entry T 0 0 < entry T 0 m)
    {c m : ℕ} (hc : c < A.length) (hm : m < T.length)
    (h : nextrel0 (A ++ T) c (A.length + m)) : m = 0 := by
  by_contra hm0
  have hval := h.2.2.2.2 A.length ⟨hc, by omega⟩
  rw [entry_append_right, show A.length = A.length + 0 from by omega,
    entry_append_right] at hval
  exact absurd (hmin m (by omega) hm) (by omega)

/-- ★★★ `le0` の鎖が接頭辞から塔に入るなら、**塔の根を通る**。 -/
theorem rtg0_through_root {A T : TrioSeq}
    (hmin : ∀ m, 0 < m → m < T.length → entry T 0 0 < entry T 0 m)
    {y : ℕ} (hy : y < A.length) {b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 (A ++ T)) y b) :
    b < A.length ∨ Relation.ReflTransGen (nextrel0 (A ++ T)) A.length b := by
  induction h with
  | refl => exact Or.inl hy
  | @tail c b _ hcb ih =>
      rcases ih with hc | hc
      · rcases Nat.lt_or_ge b A.length with hb | hb
        · exact Or.inl hb
        · have hblen : b < (A ++ T).length := hcb.2.1
          have hbT : b - A.length < T.length := by
            rw [List.length_append] at hblen; omega
          have hbe : b = A.length + (b - A.length) := by omega
          have hz := nextrel0_cross_root hmin hc hbT (by rw [← hbe]; exact hcb)
          have hb0 : b = A.length := by omega
          rw [hb0]
          exact Or.inr Relation.ReflTransGen.refl
      · exact Or.inr (hc.tail hcb)

/-- ★★★★ **`le0` で接頭辞から塔の中に届くなら、塔の根も `le0` 祖先**。 -/
theorem le0_through_root {A T : TrioSeq}
    (hmin : ∀ m, 0 < m → m < T.length → entry T 0 0 < entry T 0 m)
    {y m : ℕ} (hy : y < A.length) (hm : m < T.length)
    (h : le0 (A ++ T) y (A.length + m)) :
    le0 (A ++ T) A.length (A.length + m) := by
  obtain ⟨-, hb, hrt⟩ := h
  have hAlen : A.length < (A ++ T).length := by
    rw [List.length_append]; omega
  rcases rtg0_through_root hmin hy hrt with hc | hc
  · omega
  · exact ⟨hAlen, hb, hc⟩

/-- ★★★★★★ **錐の中の的には、接頭辞から行 1 の親は来ない**。
（`OrphOK` の行 1 の壁。`le0` が塔の根を通ることから出る。） -/
theorem no_nextrel1_cross_of_cone {A T : TrioSeq}
    (hmin : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    {c m : ℕ} (hc : c < A.length) (hm : m < T.length) (_hm0 : 0 < m)
    (hcone : entry T 1 0 < entry T 1 m) :
    ¬ nextrel1 (A ++ T) c (A.length + m) := by
  intro h
  have hroot := le0_through_root hmin hc hm h.2.2.2.2.1
  have hval := h.2.2.2.2.2 A.length ⟨hc, hroot⟩
  rw [entry_append_right, show A.length = A.length + 0 from by omega,
    entry_append_right] at hval
  omega

/-- ★★★ 行 1 で接頭辞から塔に入れるのは**塔の根だけ**（ブロッカーが無ければ）。 -/
theorem nextrel1_cross_root {A T : TrioSeq}
    (hmin : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    (hnb : ∀ l, 0 < l → l < T.length → entry T 1 0 < entry T 1 l)
    {c m : ℕ} (hc : c < A.length) (hm : m < T.length)
    (h : nextrel1 (A ++ T) c (A.length + m)) : m = 0 := by
  by_contra hm0
  exact no_nextrel1_cross_of_cone hmin hc hm (by omega) (hnb m (by omega) hm) h

/-- ★★★ `le1` の鎖が接頭辞から塔に入るなら、**塔の根を通る**。 -/
theorem rtg1_through_root {A T : TrioSeq}
    (hmin : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    (hnb : ∀ l, 0 < l → l < T.length → entry T 1 0 < entry T 1 l)
    {y : ℕ} (hy : y < A.length) {b : ℕ}
    (h : Relation.ReflTransGen (nextrel1 (A ++ T)) y b) :
    b < A.length ∨ Relation.ReflTransGen (nextrel1 (A ++ T)) A.length b := by
  induction h with
  | refl => exact Or.inl hy
  | @tail c b _ hcb ih =>
      rcases ih with hc | hc
      · rcases Nat.lt_or_ge b A.length with hb | hb
        · exact Or.inl hb
        · have hblen : b < (A ++ T).length := hcb.2.1
          have hbT : b - A.length < T.length := by
            rw [List.length_append] at hblen; omega
          have hbe : b = A.length + (b - A.length) := by omega
          have hz := nextrel1_cross_root hmin hnb hc hbT (by rw [← hbe]; exact hcb)
          have hb0 : b = A.length := by omega
          rw [hb0]
          exact Or.inr Relation.ReflTransGen.refl
      · exact Or.inr (hc.tail hcb)

/-- ★★★★ `le1` で接頭辞から塔の中に届くなら、塔の根も `le1` 祖先。 -/
theorem le1_through_root {A T : TrioSeq}
    (hmin : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    (hnb : ∀ l, 0 < l → l < T.length → entry T 1 0 < entry T 1 l)
    {y m : ℕ} (hy : y < A.length) (hm : m < T.length)
    (h : le1 (A ++ T) y (A.length + m)) :
    le1 (A ++ T) A.length (A.length + m) := by
  obtain ⟨-, hb, hrt⟩ := h
  have hAlen : A.length < (A ++ T).length := by
    rw [List.length_append]; omega
  rcases rtg1_through_root hmin hnb hy hrt with hc | hc
  · omega
  · exact ⟨hAlen, hb, hc⟩

/-- ★★★★★★ **行 2 の壁**: 錐の中の的には、接頭辞から行 2 の親も来ない。 -/
theorem no_nextrel2_cross_of_cone {A T : TrioSeq}
    (hmin : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    (hnb : ∀ l, 0 < l → l < T.length → entry T 1 0 < entry T 1 l)
    {c m : ℕ} (hc : c < A.length) (hm : m < T.length) (_hm0 : 0 < m)
    (hcone : entry T 2 0 < entry T 2 m) :
    ¬ nextrel2 (A ++ T) c (A.length + m) := by
  intro h
  have hroot := le1_through_root hmin hnb hc hm h.2.2.2.2.1
  have hval := h.2.2.2.2.2 A.length ⟨hc, hroot⟩
  rw [entry_append_right, show A.length = A.length + 0 from by omega,
    entry_append_right] at hval
  omega

/-- ★★★★★★★ **接頭辞は親を供給しない**（`OrphOK` の壁、3 行そろい）。 -/
theorem no_nextR_cross_of_cone {A T : TrioSeq}
    (hmin : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    (hnb : ∀ l, 0 < l → l < T.length → entry T 1 0 < entry T 1 l)
    (h2 : ∀ l, 0 < l → l < T.length → entry T 2 0 < entry T 2 l)
    {r c m : ℕ} (hc : c < A.length) (hm : m < T.length) (hm0 : 0 < m) :
    ¬ nextR (A ++ T) r c (A.length + m) := by
  intro h
  unfold nextR at h
  by_cases hr0 : r = 0
  · rw [if_pos hr0] at h
    exact absurd (nextrel0_cross_root hmin hc hm h) (by omega)
  · rw [if_neg hr0] at h
    by_cases hr1 : r = 1
    · rw [if_pos hr1] at h
      exact no_nextrel1_cross_of_cone hmin hc hm hm0 (hnb m hm0 hm) h
    · rw [if_neg hr1] at h
      exact no_nextrel2_cross_of_cone hmin hnb hc hm hm0 (h2 m hm0 hm) h


/-- `Lift1` は行 1 を下げない。 -/
theorem entry1_Lift1_ge {X : TrioSeq} {t i : ℕ} (hi : i < X.length) :
    entry X 1 i ≤ entry (Lift1 X t) 1 i := by
  rw [Wset.entry1_Lift1 hi]
  split <;> omega

/-- 塔の各列の行 1 は `Q` の対応する列の行 1 以上。 -/
theorem entry1_mTower_ge {Q : TrioSeq} {d e n k i : ℕ} (hk : k < n) (hi : i < Q.length) :
    entry Q 1 i ≤ entry (mTower Q d e n) 1 (k * Q.length + i) := by
  rw [mTower_entry hk hi]
  refine le_trans ?_ (entry1_Lift1_ge (by rwa [shiftr01_length]))
  rw [entry1_shiftr01]

/-- ★★★ **塔にブロッカーが無い ⟸ `Q` にブロッカーが無い ＋ `0 < e`**。 -/
theorem no_blocker_mTower {Q : TrioSeq} {d e n : ℕ} (hQne : Q ≠ []) (hQ1 : 0 < Q.length)
    (he : 0 < e) (hnbQ : ∀ i, 0 < i → i < Q.length → entry Q 1 0 < entry Q 1 i) :
    ∀ l, 0 < l → l < (mTower Q d e n).length →
      entry (mTower Q d e n) 1 0 < entry (mTower Q d e n) 1 l := by
  intro l hl0 hl
  have hlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  rw [hlen] at hl
  have hroot : entry (mTower Q d e n) 1 0 = entry Q 1 0 := by
    have hn : 0 < n := by
      by_contra hc
      have : n = 0 := by omega
      rw [this] at hl; omega
    have := entry1_mTower_blockRoot hQne d e n 0 hn
    simpa using this
  have hi : l % Q.length < Q.length := Nat.mod_lt _ hQ1
  have hk : l / Q.length < n := by
    refine Nat.div_lt_of_lt_mul ?_
    rw [Nat.mul_comm]; exact hl
  have hsplit : l = (l / Q.length) * Q.length + l % Q.length := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod l Q.length).symm
  rw [hroot]
  rcases Nat.eq_zero_or_pos (l % Q.length) with h0 | hp
  · -- ブロック根（`k ≥ 1`）: 行 1 は `entry Q 1 0 + e*k`
    have hk0 : 0 < l / Q.length := by
      rcases Nat.eq_zero_or_pos (l / Q.length) with hc | hc
      · exfalso; rw [hsplit, hc, h0] at hl0; omega
      · exact hc
    have heq : l = (l / Q.length) * Q.length := by omega
    have hbr := entry1_mTower_blockRoot hQne d e n (l / Q.length) hk
    rw [← heq] at hbr
    rw [hbr]
    have : 0 < e * (l / Q.length) := Nat.mul_pos he hk0
    omega
  · -- ブロック内の非根の列: `Q` のブロッカー無しから
    have hge := entry1_mTower_ge (Q := Q) (d := d) (e := e) (n := n)
      (k := l / Q.length) (i := l % Q.length) hk hi
    rw [← hsplit] at hge
    exact Nat.lt_of_lt_of_le (hnbQ _ hp hi) hge

/-- ★★★ 塔の根が行 0 で狭義最浅（`hmin`）⟸ `hr0` ＋ `0 < d`。 -/
theorem shallowest_mTower {Q : TrioSeq} {d e n : ℕ} (hQ1 : 0 < Q.length) (hd : 0 < d)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) :
    ∀ l, 0 < l → l < (mTower Q d e n).length →
      entry (mTower Q d e n) 0 0 < entry (mTower Q d e n) 0 l := by
  intro l hl0 hl
  have hlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  rw [hlen] at hl
  have hn : 0 < n := by
    by_contra hc
    have : n = 0 := by omega
    rw [this] at hl; omega
  have hroot : entry (mTower Q d e n) 0 0 = entry Q 0 0 := by
    have := entry0_mTower_block Q d e n 0 0 hn hQ1
    simpa using this
  have hi : l % Q.length < Q.length := Nat.mod_lt _ hQ1
  have hk : l / Q.length < n := by
    refine Nat.div_lt_of_lt_mul ?_
    rw [Nat.mul_comm]; exact hl
  have hsplit : l = (l / Q.length) * Q.length + l % Q.length := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod l Q.length).symm
  have hval := entry0_mTower_block Q d e n (l / Q.length) (l % Q.length) hk hi
  rw [← hsplit] at hval
  rw [hroot, hval]
  rcases Nat.eq_zero_or_pos (l % Q.length) with h0 | hp
  · have hk0 : 0 < l / Q.length := by
      rcases Nat.eq_zero_or_pos (l / Q.length) with hc | hc
      · exfalso; rw [hc, h0] at hsplit; simp at hsplit; omega
      · exact hc
    have : 0 < d * (l / Q.length) := Nat.mul_pos hd hk0
    rw [h0]
    omega
  · have := hr0 _ hp hi
    omega

/-- ★★★★★★★ **接頭辞は `srow` の行で親を供給しない**（`OrphOK` の壁、最終形）。
行 2 の錐の条件は **`hz0`（塔の根の行 2 が 0）から自動**で出る。 -/
theorem no_nextR_srow_cross {A T : TrioSeq}
    (hmin : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    (hnb : ∀ l, 0 < l → l < T.length → entry T 1 0 < entry T 1 l)
    (hz0 : entry T 2 0 = 0)
    {c m : ℕ} (hc : c < A.length) (hm : m < T.length) (hm0 : 0 < m) :
    ¬ nextR (A ++ T) (srow (A ++ T) (A.length + m)) c (A.length + m) := by
  have e1 : entry (A ++ T) 1 (A.length + m) = entry T 1 m := entry_append_right A T 1 m
  have e2 : entry (A ++ T) 2 (A.length + m) = entry T 2 m := entry_append_right A T 2 m
  unfold srow
  rw [e1, e2]
  by_cases h2 : 0 < entry T 2 m
  · rw [if_pos h2]
    unfold nextR
    rw [if_neg (by omega), if_neg (by omega)]
    exact no_nextrel2_cross_of_cone hmin hnb hc hm hm0 (by omega)
  · rw [if_neg h2]
    by_cases h1 : 0 < entry T 1 m
    · rw [if_pos h1]
      unfold nextR
      rw [if_neg (by omega), if_pos rfl]
      exact no_nextrel1_cross_of_cone hmin hc hm hm0 (hnb m hm0 hm)
    · rw [if_neg h1]
      unfold nextR
      rw [if_pos rfl]
      intro h
      exact absurd (nextrel0_cross_root hmin hc hm h) (by omega)


/-- ★ 窓の根は **`le0` 祖先の上でだけ**行 1 で狭義最小。 -/
theorem window_root_row1_min_on_le0 {M : TrioSeq} {a b l : ℕ}
    (h : nextrel1 M a b) (hl : a < l) (hle : le0 M l b) :
    entry M 1 a < entry M 1 l := by
  have hmin := h.2.2.2.2.2 l ⟨hl, hle⟩
  have hlt := h.2.2.2.1
  omega

/-- 行 2 版（`le1` 祖先の上でだけ）。 -/
theorem window_root_row2_min_on_le1 {M : TrioSeq} {a b l : ℕ}
    (h : nextrel2 M a b) (hl : a < l) (hle : le1 M l b) :
    entry M 2 a < entry M 2 l := by
  have hmin := h.2.2.2.2.2 l ⟨hl, hle⟩
  have hlt := h.2.2.2.1
  omega

/-- ★ 逆向き: **塔にブロッカーがあれば `Q` にもある**。⟹ `hnb(塔) ⟺ hnbQ`。 -/
theorem blocker_mTower_imp_Q {Q : TrioSeq} {d e n l : ℕ} (hQne : Q ≠ []) (hQ1 : 0 < Q.length)
    (he : 0 < e) (hl0 : 0 < l) (hl : l < (mTower Q d e n).length)
    (hb : entry (mTower Q d e n) 1 l ≤ entry (mTower Q d e n) 1 0) :
    ∃ i, 0 < i ∧ i < Q.length ∧ entry Q 1 i ≤ entry Q 1 0 := by
  have hlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  rw [hlen] at hl
  have hn : 0 < n := by
    by_contra hc
    have : n = 0 := by omega
    rw [this] at hl; omega
  have hroot : entry (mTower Q d e n) 1 0 = entry Q 1 0 := by
    have := entry1_mTower_blockRoot hQne d e n 0 hn
    simpa using this
  have hi : l % Q.length < Q.length := Nat.mod_lt _ hQ1
  have hk : l / Q.length < n := by
    refine Nat.div_lt_of_lt_mul ?_
    rw [Nat.mul_comm]; exact hl
  have hsplit : l = (l / Q.length) * Q.length + l % Q.length := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod l Q.length).symm
  rcases Nat.eq_zero_or_pos (l % Q.length) with h0 | hp
  · exfalso
    have hk0 : 0 < l / Q.length := by
      rcases Nat.eq_zero_or_pos (l / Q.length) with hc | hc
      · exfalso; rw [hc, h0] at hsplit; simp at hsplit; omega
      · exact hc
    have heq : l = (l / Q.length) * Q.length := by omega
    have hbr := entry1_mTower_blockRoot hQne d e n (l / Q.length) hk
    rw [← heq] at hbr
    rw [hbr, hroot] at hb
    have : 0 < e * (l / Q.length) := Nat.mul_pos he hk0
    omega
  · refine ⟨l % Q.length, hp, hi, ?_⟩
    have hge := entry1_mTower_ge (Q := Q) (d := d) (e := e) (n := n)
      (k := l / Q.length) (i := l % Q.length) hk hi
    rw [← hsplit] at hge
    rw [hroot] at hb
    omega


/-- ★★ 行 1 で接頭辞から越境できる先は**ブロッカーだけ**。 -/
theorem nextrel1_cross_is_blocker {A T : TrioSeq}
    (hmin : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    {c m : ℕ} (hc : c < A.length) (hm : m < T.length) (hm0 : 0 < m)
    (h : nextrel1 (A ++ T) c (A.length + m)) : entry T 1 m ≤ entry T 1 0 := by
  by_contra hcon
  push Not at hcon
  exact no_nextrel1_cross_of_cone hmin hc hm hm0 hcon h

/-- ★★ 行 2 版。 -/
theorem nextrel2_cross_is_blocker {A T : TrioSeq}
    (hmin : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    (hnb : ∀ l, 0 < l → l < T.length → entry T 1 0 < entry T 1 l)
    {c m : ℕ} (hc : c < A.length) (hm : m < T.length) (hm0 : 0 < m)
    (h : nextrel2 (A ++ T) c (A.length + m)) : entry T 2 m ≤ entry T 2 0 := by
  by_contra hcon
  push Not at hcon
  exact no_nextrel2_cross_of_cone hmin hnb hc hm hm0 hcon h


theorem le1_self {X : TrioSeq} (hX : 0 < X.length) : le1 X 0 0 :=
  ⟨hX, hX, Relation.ReflTransGen.refl⟩

/-- 錐の**外**の列は `Lift1` で持ち上がらない。 -/
theorem entry1_Lift1_out {X : TrioSeq} {t i : ℕ} (hi : i < X.length) (hout : ¬ le1 X 0 i) :
    entry (Lift1 X t) 1 i = entry X 1 i := by
  rw [Wset.entry1_Lift1 hi, if_neg hout]
  omega

/-- 錐の**中**の列はちょうど `t` だけ持ち上がる。 -/
theorem entry1_Lift1_in {X : TrioSeq} {t i : ℕ} (hi : i < X.length) (hin : le1 X 0 i) :
    entry (Lift1 X t) 1 i = entry X 1 i + t := by
  rw [Wset.entry1_Lift1 hi, if_pos hin]

/-- 根は必ず錐の中なので、必ず `+t` される。 -/
theorem entry1_Lift1_root {X : TrioSeq} {t : ℕ} (hX : 0 < X.length) :
    entry (Lift1 X t) 1 0 = entry X 1 0 + t :=
  entry1_Lift1_in hX (le1_self hX)

/-- ★★★★★ **錐の外の列は、`t` が差に追いつくとブロッカーになる**（両向き）。 -/
theorem blocker_Lift1_out_iff {X : TrioSeq} {t j : ℕ} (hX : 0 < X.length)
    (hj : j < X.length) (hout : ¬ le1 X 0 j) :
    entry (Lift1 X t) 1 j ≤ entry (Lift1 X t) 1 0
      ↔ entry X 1 j ≤ entry X 1 0 + t := by
  rw [entry1_Lift1_out hj hout, entry1_Lift1_root hX]

/-- ★★ 錐の**中**の列は、ブロッカーかどうかが `t` で変わらない。 -/
theorem blocker_Lift1_in_iff {X : TrioSeq} {t j : ℕ} (hX : 0 < X.length)
    (hj : j < X.length) (hin : le1 X 0 j) :
    entry (Lift1 X t) 1 j ≤ entry (Lift1 X t) 1 0
      ↔ entry X 1 j ≤ entry X 1 0 := by
  rw [entry1_Lift1_in hj hin, entry1_Lift1_root hX]
  omega

/-- ★★★★★★★ **`h1out` が `Lift1` を生き延びる条件（両向き、完全）**。
錐の中の列は元のまま（`t` に依らない）／錐の外の列は **差が `t` より真に大きい**ことが要る。
⟹ ★ **`t` が予算**。 -/
theorem h1out_Lift1_iff {X : TrioSeq} {t : ℕ} (hX : 0 < X.length) :
    (∀ j, 0 < j → j < (Lift1 X t).length →
        entry (Lift1 X t) 1 0 < entry (Lift1 X t) 1 j)
      ↔ (∀ j, 0 < j → j < X.length →
            (le1 X 0 j → entry X 1 0 < entry X 1 j) ∧
            (¬ le1 X 0 j → entry X 1 0 + t < entry X 1 j)) := by
  have hlen : (Lift1 X t).length = X.length := Lift1_length X t
  constructor
  · intro h j hj0 hj
    refine ⟨fun hin => ?_, fun hout => ?_⟩
    · have hv := h j hj0 (by rw [hlen]; exact hj)
      rw [entry1_Lift1_in hj hin, entry1_Lift1_root hX] at hv
      omega
    · have hv := h j hj0 (by rw [hlen]; exact hj)
      rw [entry1_Lift1_out hj hout, entry1_Lift1_root hX] at hv
      omega
  · intro h j hj0 hj
    rw [hlen] at hj
    rw [entry1_Lift1_root hX]
    by_cases hin : le1 X 0 j
    · rw [entry1_Lift1_in hj hin]
      have := (h j hj0 hj).1 hin
      omega
    · rw [entry1_Lift1_out hj hin]
      exact (h j hj0 hj).2 hin

open Classical in
/-- ★★★★★ **塔の行 1 の閉じた式**: 錐の中なら `+e*k`、外なら `+0`。 -/
theorem entry1_mTower_block_formula (Q : TrioSeq) {d e n k i : ℕ}
    (hk : k < n) (hi : i < Q.length) :
    entry (mTower Q d e n) 1 (k * Q.length + i)
      = entry Q 1 i + (if le1 Q 0 i then e * k else 0) := by
  rw [mTower_entry hk hi,
    Wset.entry1_Lift1 (by rwa [shiftr01_length]), entry1_shiftr01]
  congr 1
  by_cases h : le1 Q 0 i
  · rw [if_pos h, if_pos ((le1_shiftr01 (d0 := d * k)).mpr h)]
  · rw [if_neg h, if_neg (fun hc => h ((le1_shiftr01 (d0 := d * k)).mp hc))]

/-- ★★★★★★★ **差が `e*k` ずつ縮む**（R2 (s11) の機構、逐語）。

窓の根が第 `k` ブロックの**錐の中**の列 `p`、的が第 `k'` ブロックの**錐の外**の列 `j`:

    根の行 1 = `entry Q 1 p + e*k`   （持ち上がる）
    的の行 1 = `entry Q 1 j`         （持ち上がらない、`k'` に依らない）

⟹ ★ **`e*k` が `entry Q 1 j - entry Q 1 p` に追いついた瞬間に、的はブロッカーになる。** -/
theorem gap_shrinks_in_mTower (Q : TrioSeq) {d e n k k' p j : ℕ}
    (hk : k < n) (hk' : k' < n) (hp : p < Q.length) (hj : j < Q.length)
    (hin : le1 Q 0 p) (hout : ¬ le1 Q 0 j) :
    entry (mTower Q d e n) 1 (k * Q.length + p) = entry Q 1 p + e * k ∧
      entry (mTower Q d e n) 1 (k' * Q.length + j) = entry Q 1 j := by
  refine ⟨?_, ?_⟩
  · rw [entry1_mTower_block_formula Q hk hp, if_pos hin]
  · rw [entry1_mTower_block_formula Q hk' hj, if_neg hout]
    omega

/-- ★★★★★★★ **追いつく瞬間が式で出る**（両向き）。 -/
theorem outOfCone_becomes_blocker_iff (Q : TrioSeq) {d e n k k' p j : ℕ}
    (hk : k < n) (hk' : k' < n) (hp : p < Q.length) (hj : j < Q.length)
    (hin : le1 Q 0 p) (hout : ¬ le1 Q 0 j) :
    entry (mTower Q d e n) 1 (k' * Q.length + j)
        ≤ entry (mTower Q d e n) 1 (k * Q.length + p)
      ↔ entry Q 1 j ≤ entry Q 1 p + e * k := by
  obtain ⟨h1, h2⟩ := gap_shrinks_in_mTower Q hk hk' hp hj hin hout
  rw [h1, h2]


/-- ★★★ 根が錐の中・的が錐の中 ⟹ 深さで**良くなる**（`k ≤ k'` なので `e*k' ≥ e*k`）。 -/
theorem blocker_in_in (Q : TrioSeq) {d e n k k' p j : ℕ}
    (hk : k < n) (hk' : k' < n) (hp : p < Q.length) (hj : j < Q.length)
    (hinp : le1 Q 0 p) (hinj : le1 Q 0 j) :
    entry (mTower Q d e n) 1 (k' * Q.length + j)
        ≤ entry (mTower Q d e n) 1 (k * Q.length + p)
      ↔ entry Q 1 j + e * k' ≤ entry Q 1 p + e * k := by
  rw [entry1_mTower_block_formula Q hk' hj, if_pos hinj,
    entry1_mTower_block_formula Q hk hp, if_pos hinp]

/-- ★★★ 根が錐の中・的が錐の**外** ⟹ ⛔ **深さで悪くなる唯一のマス**。 -/
theorem blocker_in_out (Q : TrioSeq) {d e n k k' p j : ℕ}
    (hk : k < n) (hk' : k' < n) (hp : p < Q.length) (hj : j < Q.length)
    (hinp : le1 Q 0 p) (houtj : ¬ le1 Q 0 j) :
    entry (mTower Q d e n) 1 (k' * Q.length + j)
        ≤ entry (mTower Q d e n) 1 (k * Q.length + p)
      ↔ entry Q 1 j ≤ entry Q 1 p + e * k := by
  rw [entry1_mTower_block_formula Q hk' hj, if_neg houtj,
    entry1_mTower_block_formula Q hk hp, if_pos hinp]
  omega

/-- ★★★ 根が錐の**外**・的が錐の中 ⟹ 深さで良くなる。 -/
theorem blocker_out_in (Q : TrioSeq) {d e n k k' p j : ℕ}
    (hk : k < n) (hk' : k' < n) (hp : p < Q.length) (hj : j < Q.length)
    (houtp : ¬ le1 Q 0 p) (hinj : le1 Q 0 j) :
    entry (mTower Q d e n) 1 (k' * Q.length + j)
        ≤ entry (mTower Q d e n) 1 (k * Q.length + p)
      ↔ entry Q 1 j + e * k' ≤ entry Q 1 p := by
  rw [entry1_mTower_block_formula Q hk' hj, if_pos hinj,
    entry1_mTower_block_formula Q hk hp, if_neg houtp]
  omega

/-- ★★★★★ 根が錐の**外**・的も錐の外 ⟹ ★ **`k`・`k'`・`e` に一切依らない**
（＝ **深さで変わらない**）。 -/
theorem blocker_out_out (Q : TrioSeq) {d e n k k' p j : ℕ}
    (hk : k < n) (hk' : k' < n) (hp : p < Q.length) (hj : j < Q.length)
    (houtp : ¬ le1 Q 0 p) (houtj : ¬ le1 Q 0 j) :
    entry (mTower Q d e n) 1 (k' * Q.length + j)
        ≤ entry (mTower Q d e n) 1 (k * Q.length + p)
      ↔ entry Q 1 j ≤ entry Q 1 p := by
  rw [entry1_mTower_block_formula Q hk' hj, if_neg houtj,
    entry1_mTower_block_formula Q hk hp, if_neg houtp]
  omega


open Classical in
/-- ★★★★★★★ **表を 1 本にまとめたもの**（全 4 マス）。 -/
theorem blocker_mTower_iff (Q : TrioSeq) {d e n k k' p j : ℕ}
    (hk : k < n) (hk' : k' < n) (hp : p < Q.length) (hj : j < Q.length) :
    entry (mTower Q d e n) 1 (k' * Q.length + j)
        ≤ entry (mTower Q d e n) 1 (k * Q.length + p)
      ↔ entry Q 1 j + (if le1 Q 0 j then e * k' else 0)
          ≤ entry Q 1 p + (if le1 Q 0 p then e * k else 0) := by
  rw [entry1_mTower_block_formula Q hk' hj, entry1_mTower_block_formula Q hk hp]

/-- ★★★★★ **予算が 0 なら深さで一切変わらない**（`e = 0` または窓の根が第 0 ブロック）。
⟹ ⛔ **`h1out` の遺伝が壊れるには `0 < e` かつ `1 ≤ k` が要る**。 -/
theorem blocker_stable_of_budget_zero (Q : TrioSeq) {d e n k k' p j : ℕ}
    (hk : k < n) (hk' : k' < n) (hp : p < Q.length) (hj : j < Q.length)
    (hinp : le1 Q 0 p) (houtj : ¬ le1 Q 0 j) (hbudget : e * k = 0) :
    entry (mTower Q d e n) 1 (k' * Q.length + j)
        ≤ entry (mTower Q d e n) 1 (k * Q.length + p)
      ↔ entry Q 1 j ≤ entry Q 1 p := by
  rw [blocker_in_out Q hk hk' hp hj hinp houtj, hbudget]
  omega


/-- ⛔⛔ **`k` が `entry Q 1 j` 以上なら、錐の外の列は必ずブロッカーになる**。 -/
theorem blocker_of_large_k (Q : TrioSeq) {d e n k k' p j : ℕ}
    (hk : k < n) (hk' : k' < n) (hp : p < Q.length) (hj : j < Q.length)
    (hinp : le1 Q 0 p) (houtj : ¬ le1 Q 0 j)
    (he : 0 < e) (hbig : entry Q 1 j ≤ k) :
    entry (mTower Q d e n) 1 (k' * Q.length + j)
      ≤ entry (mTower Q d e n) 1 (k * Q.length + p) := by
  refine (blocker_in_out Q hk hk' hp hj hinp houtj).mpr ?_
  have : k ≤ e * k := Nat.le_mul_of_pos_left k he
  omega

/-- ⛔⛔ **同じことを「十分大きい `k` が存在する」形で**。 -/
theorem exists_k_blocker (Q : TrioSeq) {d e p j : ℕ}
    (hp : p < Q.length) (hj : j < Q.length)
    (hinp : le1 Q 0 p) (houtj : ¬ le1 Q 0 j) (he : 0 < e) :
    ∃ k0, ∀ k k' n, k0 ≤ k → k < n → k' < n →
      entry (mTower Q d e n) 1 (k' * Q.length + j)
        ≤ entry (mTower Q d e n) 1 (k * Q.length + p) := by
  refine ⟨entry Q 1 j, ?_⟩
  intro k k' n hk0 hk hk'
  exact blocker_of_large_k Q hk hk' hp hj hinp houtj he hk0


/-- `le1` で真に上がると行 1 は狭義に増える。 -/
theorem entry1_lt_of_le1_ne {M : TrioSeq} {a b : ℕ}
    (h : le1 M a b) (hne : a ≠ b) : entry M 1 a < entry M 1 b := by
  obtain ⟨-, -, hrt⟩ := h
  rcases Relation.ReflTransGen.cases_tail hrt with h1 | ⟨c, hc1, hc2⟩
  · exact absurd h1.symm hne
  · refine Nat.lt_of_le_of_lt ?_ hc2.2.2.2.1
    clear hc2
    induction hc1 with
    | refl => exact le_refl _
    | tail _ hstep ih => exact le_trans ih (le_of_lt hstep.2.2.2.1)

/-- ★★★ **ブロッカーは必ず錐の外**（`not_le1_zero_iff` の易しいほうの向き）。 -/
theorem blocker_not_le1 {M : TrioSeq} {j : ℕ} (hj : j ≠ 0)
    (hb : entry M 1 j ≤ entry M 1 0) : ¬ le1 M 0 j := by
  intro h
  exact absurd (entry1_lt_of_le1_ne h (fun hc => hj hc.symm)) (by omega)

/-- ★★★★★ **型 B の非根の列は 2 本とも錐の外**。⟹ `Lift1` は**根しか持ち上げない**。 -/
theorem typeB_out_of_cone {V : TrioSeq} (_hlen : V.length = 3)
    (h1 : entry V 1 1 ≤ entry V 1 0) (h2 : entry V 1 2 ≤ entry V 1 0) :
    ¬ le1 V 0 1 ∧ ¬ le1 V 0 2 :=
  ⟨blocker_not_le1 (by omega) h1, blocker_not_le1 (by omega) h2⟩

open Classical in
/-- ★★★★★★★ **型 B の塔の行 1 は完全に書ける**: 根だけが `+e*k`、他は据え置き。 -/
theorem entry1_mTower_typeB {V : TrioSeq} (hlen : V.length = 3)
    (hb1 : entry V 1 1 ≤ entry V 1 0) (hb2 : entry V 1 2 ≤ entry V 1 0)
    {d e m k : ℕ} (hk : k < m) :
    entry (mTower V d e m) 1 (k * V.length) = entry V 1 0 + e * k ∧
      entry (mTower V d e m) 1 (k * V.length + 1) = entry V 1 1 ∧
      entry (mTower V d e m) 1 (k * V.length + 2) = entry V 1 2 := by
  obtain ⟨ho1, ho2⟩ := typeB_out_of_cone hlen hb1 hb2
  refine ⟨?_, ?_, ?_⟩
  · have h := entry1_mTower_block_formula V (d := d) (e := e) (n := m) (k := k) (i := 0)
      hk (by omega)
    rw [Nat.add_zero] at h
    rw [h, if_pos (le1_self (by omega))]
  · rw [entry1_mTower_block_formula V hk (by omega), if_neg ho1]
    omega
  · rw [entry1_mTower_block_formula V hk (by omega), if_neg ho2]
    omega

/-- ★★★★★★★ **`A` も塔も行 2 ≡ 0 なら、連結は仮定ゼロで `W u`**。 -/
theorem prefix_mem_of_zeroRow2 {u : ℕ} {A T : TrioSeq}
    (hzA : ∀ p ∈ A, p.2.2 = 0) (hzT : ∀ p ∈ T, p.2.2 = 0)
    (hA : A ∈ W u) (hAne : A ≠ []) : A ++ T ∈ W u := by
  have hA1 : 0 < A.length := List.length_pos_iff.mpr hAne
  rw [mem_Wself_iff]
  refine ⟨zeroRow2_mem_Wself ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact hzA p h
    · exact hzT p h
  · have hlev : lev (A ++ T) 0 = lev A 0 := by
      unfold lev
      rw [entry_append_left A T hA1, entry_append_left A T hA1]
    rw [hlev]
    exact lev_root_le_of_mem_W hA hAne

/-- ★★★★★★★ **型 B（行 2 ≡ 0）の塔は、接頭辞つきでも無料**。 -/
theorem prefix_mTower_mem_of_zeroRow2 {u : ℕ} {A V : TrioSeq}
    (hzA : ∀ p ∈ A, p.2.2 = 0) (hzV : ∀ p ∈ V, p.2.2 = 0)
    (hA : A ∈ W u) (hAne : A ≠ []) (d e m : ℕ) :
    A ++ mTower V d e m ∈ W u :=
  prefix_mem_of_zeroRow2 hzA (zeroRow2_mTower hzV d e m) hA hAne

/-- 行 2 が 0 の列の `srow` は 1 以下。⟹ ★ **`wd1 = 0`**（＝ 次の `e` が 0）。 -/
theorem srow_le_one_of_row2_zero {M : TrioSeq} {j : ℕ} (h : entry M 2 j = 0) :
    srow M j ≤ 1 := by
  unfold srow
  rw [if_neg (by omega)]
  split <;> omega


/-- ★★★ `hnbQ` なら `Q` の全列が根の錐の中。 -/
theorem le1_all_of_hnbQ {Q : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hnbQ : ∀ i, 0 < i → i < Q.length → entry Q 1 0 < entry Q 1 i)
    {q : ℕ} (hq : q < Q.length) : le1 Q 0 q := by
  by_contra hc
  obtain ⟨y, hrt, hy0, hyb⟩ := (not_le1_zero_iff hr0 hq).mp hc
  have hylt : y < Q.length := by
    rcases Relation.ReflTransGen.cases_head hrt with h1 | ⟨c, hc1, -⟩
    · omega
    · exact hc1.1
  exact absurd (hnbQ y (by omega) hylt) (by omega)

open Classical in
/-- ★★★★★ `hnbQ` なら塔の行 1 は **全列が `+e*k`**（`if` が常に真）。 -/
theorem entry1_mTower_of_hnbQ {Q : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hnbQ : ∀ i, 0 < i → i < Q.length → entry Q 1 0 < entry Q 1 i)
    {d e n k i : ℕ} (hk : k < n) (hi : i < Q.length) :
    entry (mTower Q d e n) 1 (k * Q.length + i) = entry Q 1 i + e * k := by
  rw [entry1_mTower_block_formula Q hk hi, if_pos (le1_all_of_hnbQ hr0 hnbQ hi)]

/-- ★★★★★★★ **`e*n` が消える** —— 同じブロックの中の比較は `n`・`e` に依らない。
⟹ L3 の「`hnbQ` は `n` 依存を消す唯一の形」を式にしたもの。 -/
theorem blocker_in_block_of_hnbQ {Q : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hnbQ : ∀ i, 0 < i → i < Q.length → entry Q 1 0 < entry Q 1 i)
    {d e n k p x : ℕ} (hk : k < n) (hp : p < Q.length) (hx : x < Q.length) :
    entry (mTower Q d e n) 1 (k * Q.length + x)
        ≤ entry (mTower Q d e n) 1 (k * Q.length + p)
      ↔ entry Q 1 x ≤ entry Q 1 p := by
  rw [entry1_mTower_of_hnbQ hr0 hnbQ hk hx, entry1_mTower_of_hnbQ hr0 hnbQ hk hp]
  omega

/-- ★★★★★★★ **`hnbQ` の下では、ブロックの非根の列の行 1 は正**。
⟹ ⛔ **R2 の「型 B」（真ん中の列の行 1 が 0）は `hnbQ(Q)` の下では起きえない**。 -/
theorem row1_pos_in_block_of_hnbQ {Q : TrioSeq}
    (hnbQ : ∀ i, 0 < i → i < Q.length → entry Q 1 0 < entry Q 1 i)
    {d e n k x : ℕ} (hk : k < n) (hx : x < Q.length) (hx0 : 0 < x) :
    0 < entry (mTower Q d e n) 1 (k * Q.length + x) := by
  have hge := entry1_mTower_ge (Q := Q) (d := d) (e := e) (n := n) (k := k) (i := x) hk hx
  have := hnbQ x hx0 hx
  omega

/-- ★★★★★★★ **`hnbQ(V)` は `Q` だけの条件に落ちる**（`n`・`e`・`d` が消える）。
`j ≥ 1` の段では窓は 1 つのブロックの中（`parent_bound_pos`）なので、これがそのまま
「窓のブロッカー無し」の判定式になる。 -/
theorem hnbQ_window_iff_of_hnbQ {Q : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hnbQ : ∀ i, 0 < i → i < Q.length → entry Q 1 0 < entry Q 1 i)
    {d e n k p j : ℕ} (hk : k < n) (hp : p < Q.length) (hj : j ≤ Q.length) :
    (∀ x, p < x → x < j →
        entry (mTower Q d e n) 1 (k * Q.length + p)
          < entry (mTower Q d e n) 1 (k * Q.length + x))
      ↔ (∀ x, p < x → x < j → entry Q 1 p < entry Q 1 x) := by
  constructor
  · intro h x hpx hxj
    have hx : x < Q.length := by omega
    have := h x hpx hxj
    rw [entry1_mTower_of_hnbQ hr0 hnbQ hk hx,
      entry1_mTower_of_hnbQ hr0 hnbQ hk hp] at this
    omega
  · intro h x hpx hxj
    have hx : x < Q.length := by omega
    rw [entry1_mTower_of_hnbQ hr0 hnbQ hk hx,
      entry1_mTower_of_hnbQ hr0 hnbQ hk hp]
    have := h x hpx hxj
    omega


open Classical in
/-- ★★ ブロックの行 1（`hnbQ` の下）。⟹ **`e*n` が一様に乗るだけ**。 -/
theorem entry1_block_of_hnbQ {Q : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hnbQ : ∀ i, 0 < i → i < Q.length → entry Q 1 0 < entry Q 1 i)
    {d e n l : ℕ} (hl : l < Q.length) :
    entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 1 l = entry Q 1 l + e * n := by
  rw [Wset.entry1_Lift1 (by rwa [shiftr01_length]), entry1_shiftr01,
    if_pos ((le1_shiftr01 (d0 := d * n)).mpr (le1_all_of_hnbQ hr0 hnbQ hl))]

/-- ★★★ **`hnb`(ブロック) ＝ `hnbQ`**（`n`・`e`・`d` が消える）。 -/
theorem hnb_block_of_hnbQ {Q : TrioSeq} (hQ1 : 0 < Q.length)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hnbQ : ∀ i, 0 < i → i < Q.length → entry Q 1 0 < entry Q 1 i)
    {d e n : ℕ} :
    ∀ l, 0 < l → l < (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length →
      entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 1 0
        < entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 1 l := by
  intro l hl0 hl
  rw [Lift1_length, shiftr01_length] at hl
  rw [entry1_block_of_hnbQ hr0 hnbQ hl, entry1_block_of_hnbQ hr0 hnbQ hQ1]
  have := hnbQ l hl0 hl
  omega

/-- ★★★ **`hmin`(ブロック) ＝ `hr0`**（`d*n` が一様に乗るだけ）。 -/
theorem hmin_block_of_hr0 {Q : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) {d e n : ℕ} :
    ∀ l, 0 < l → l < (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length →
      entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 0 0
        < entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 0 l := by
  intro l hl0 hl
  rw [Lift1_length, shiftr01_length] at hl
  have hQ1 : 0 < Q.length := by omega
  rw [entry0_Lift1, entry0_Lift1,
    entry0_shiftr01 (W := Q) (d0 := d * n) (d1 := 0) (p := l) (by simpa using hl),
    entry0_shiftr01 (W := Q) (d0 := d * n) (d1 := 0) (p := 0) (by simpa using hQ1)]
  have := hr0 l hl0 hl
  omega

/-- ★★ `hz0`(ブロック) ＝ `hz0`（行 2 は `shiftr01`・`Lift1` で不変）。 -/
theorem hz0_block {Q : TrioSeq} (hz0 : entry Q 2 0 = 0) {d e n : ℕ} :
    entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 2 0 = 0 := by
  rw [Wset.entry2_Lift1, entry2_shiftr01]
  exact hz0

/-- ★★★★★★★ **(W6) の結論**: `hr0` ＋ `hnbQ` ＋ `hz0`（＝ `TowerP''` の中身）だけで、
**塔は「足しているブロックの `j` 列目」に親を供給できない**。
⟹ ★ **`n` にも `e` にも `d` にも依りません**（`hnbQ` が `e*n` を消すため）。 -/
theorem tower_no_cross_of_hnbQ {Q : TrioSeq} (hQ1 : 0 < Q.length)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hnbQ : ∀ i, 0 < i → i < Q.length → entry Q 1 0 < entry Q 1 i)
    (hz0 : entry Q 2 0 = 0)
    {d e n j c : ℕ} (hj : j < Q.length) (hj0 : 0 < j)
    (hc : c < (mTower Q d e n).length) :
    ¬ nextR (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        (srow (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
          ((mTower Q d e n).length + j))
        c ((mTower Q d e n).length + j) := by
  set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
  have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
  have hTlen : (B.take (j + 1)).length = j + 1 := by
    rw [List.length_take, hBlen]; omega
  refine no_nextR_srow_cross (A := mTower Q d e n) (T := B.take (j + 1)) ?_ ?_ ?_ hc ?_ hj0
  · intro l hl0 hl
    rw [hTlen] at hl
    rw [Wset.entry_take (show (0:ℕ) < j + 1 by omega),
      Wset.entry_take (show l < j + 1 by omega)]
    exact hmin_block_of_hr0 hr0 l hl0 (by rw [hBlen]; omega)
  · intro l hl0 hl
    rw [hTlen] at hl
    rw [Wset.entry_take (show (0:ℕ) < j + 1 by omega),
      Wset.entry_take (show l < j + 1 by omega)]
    exact hnb_block_of_hnbQ hQ1 hr0 hnbQ l hl0 (by rw [hBlen]; omega)
  · rw [Wset.entry_take (show (0:ℕ) < j + 1 by omega)]
    exact hz0_block hz0
  · rw [hTlen]; omega


open Classical in
/-- ★★★★★★★ **`hcls` があれば、証人の行 1 の狭義増加はブロックへそのまま移る**
（`n`・`e` が消える）。 -/
theorem entry1_block_lt_of_hcls {Q : TrioSeq} {d e n y j : ℕ}
    (hy : y < Q.length) (hj : j < Q.length)
    (hlt : entry Q 1 y < entry Q 1 j)
    (hcls : le1 Q 0 y → le1 Q 0 j) :
    entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 1 y
      < entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 1 j := by
  have hey : entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 1 y
      = entry Q 1 y + (if le1 Q 0 y then e * n else 0) := by
    rw [Wset.entry1_Lift1 (by rwa [shiftr01_length]), entry1_shiftr01]
    congr 1
    by_cases h : le1 Q 0 y
    · rw [if_pos h, if_pos ((le1_shiftr01 (d0 := d * n)).mpr h)]
    · rw [if_neg h, if_neg (fun hc => h ((le1_shiftr01 (d0 := d * n)).mp hc))]
  have hej : entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 1 j
      = entry Q 1 j + (if le1 Q 0 j then e * n else 0) := by
    rw [Wset.entry1_Lift1 (by rwa [shiftr01_length]), entry1_shiftr01]
    congr 1
    by_cases h : le1 Q 0 j
    · rw [if_pos h, if_pos ((le1_shiftr01 (d0 := d * n)).mpr h)]
    · rw [if_neg h, if_neg (fun hc => h ((le1_shiftr01 (d0 := d * n)).mp hc))]
  rw [hey, hej]
  by_cases hiy : le1 Q 0 y
  · rw [if_pos hiy, if_pos (hcls hiy)]
    omega
  · rw [if_neg hiy]
    split <;> omega

/-- ★★★ **隣の列は `nextrel0` の最小性が空虚**（間に列が無い）。 -/
theorem nextrel0_adjacent {M : TrioSeq} {j : ℕ} (hj0 : 0 < j) (hj : j < M.length)
    (h : entry M 0 (j - 1) < entry M 0 j) : nextrel0 M (j - 1) j := by
  refine ⟨by omega, hj, by omega, h, ?_⟩
  intro x hx
  omega

/-- ★★★★★★★ **(W9b) 隣の証人はブロックへそのまま移る**。
⟹ ★ しかも**隣なので窓を切っても必ず窓に残る** ⟹ 遺伝が自明になる。 -/
theorem block_witness_adjacent {Q : TrioSeq} {j : ℕ} (hj0 : 0 < j) (hj : j < Q.length)
    (h0 : entry Q 0 (j - 1) < entry Q 0 j)
    (h1 : entry Q 1 (j - 1) < entry Q 1 j)
    (hcls : le1 Q 0 (j - 1) → le1 Q 0 j) {d e n : ℕ} :
    nextrel0 (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) (j - 1) j ∧
      entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 1 (j - 1)
        < entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 1 j := by
  have hBlen : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length = Q.length := by
    rw [Lift1_length, shiftr01_length]
  refine ⟨nextrel0_adjacent hj0 (by rw [hBlen]; exact hj) ?_, ?_⟩
  · rw [entry0_Lift1, entry0_Lift1,
      entry0_shiftr01 (W := Q) (d0 := d * n) (d1 := 0) (p := j - 1) (by simpa using (by omega : j - 1 < Q.length)),
      entry0_shiftr01 (W := Q) (d0 := d * n) (d1 := 0) (p := j) (by simpa using hj)]
    omega
  · exact entry1_block_lt_of_hcls (by omega) hj h1 hcls

theorem entry_drop (M : TrioSeq) (i p x : ℕ) :
    entry (M.drop p) i x = entry M i (p + x) := by
  unfold entry
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- ★★★ `nextrel0` は**連続部分列**へそのまま移る（最小性の区間が中に収まるので）。 -/
theorem nextrel0_drop {M : TrioSeq} {p a b : ℕ} (hp : p ≤ a)
    (h : nextrel0 M a b) : nextrel0 (M.drop p) (a - p) (b - p) := by
  obtain ⟨ha, hb, hab, hlt, hmin⟩ := h
  have hlen : (M.drop p).length = M.length - p := by rw [List.length_drop]
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · rw [entry_drop, entry_drop]
    rw [show p + (a - p) = a from by omega, show p + (b - p) = b from by omega]
    exact hlt
  · intro x hx
    rw [entry_drop, entry_drop, show p + (b - p) = b from by omega]
    exact hmin (p + x) ⟨by omega, by omega⟩

/-- ★★★★ **`le0` も連続部分列へ移る**（始点が切れ目以降なら）。 -/
theorem rtg0_drop {M : TrioSeq} {p a b : ℕ} (hp : p ≤ a)
    (h : Relation.ReflTransGen (nextrel0 M) a b) :
    Relation.ReflTransGen (nextrel0 (M.drop p)) (a - p) (b - p) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c b hac hcb ih =>
      exact ih.tail (nextrel0_drop (le_trans hp (rtg0_index_le hac)) hcb)

/-- ★★★★★★★ **(W9c) 証人が窓に残る条件は「証人が窓の根以降」だけ**。
⟹ ★ 隣の証人（`y = j - 1`）は**必ず**残る。 -/
theorem witness_survives_window {M : TrioSeq} {p y j : ℕ} (hpy : p ≤ y)
    (hle0 : le0 M y j) (h1 : entry M 1 y < entry M 1 j) :
    le0 (M.drop p) (y - p) (j - p) ∧
      entry (M.drop p) 1 (y - p) < entry (M.drop p) 1 (j - p) := by
  obtain ⟨hy, hj, hrt⟩ := hle0
  have hlen : (M.drop p).length = M.length - p := by rw [List.length_drop]
  have hyj : y ≤ j := rtg0_index_le hrt
  refine ⟨⟨by omega, by omega, rtg0_drop hpy hrt⟩, ?_⟩
  rw [entry_drop, entry_drop, show p + (y - p) = y from by omega,
    show p + (j - p) = j from by omega]
  exact h1


/-- ★★★ **`nextrel0` の親は必ず窓の根以降**（`hr0_wnd` から）。 -/
theorem nextrel0_src_ge_of_shallow {M : TrioSeq} {p a b : ℕ}
    (hshallow : ∀ x, p < x → x < M.length → entry M 0 p < entry M 0 x)
    (hpb : p < b) (h : nextrel0 M a b) : p ≤ a := by
  obtain ⟨-, hb, hab, hlt, hmin⟩ := h
  by_contra hc
  push Not at hc
  exact absurd (hmin p ⟨hc, hpb⟩) (by
    have := hshallow b hpb hb
    omega)

open Classical in
/-- ★★★★★★★ **窓の根 `p` は、窓の全内部列の `le0` 祖先**。 -/
theorem le0_root_of_shallow {M : TrioSeq} {p : ℕ} (hp : p < M.length)
    (hshallow : ∀ x, p < x → x < M.length → entry M 0 p < entry M 0 x) :
    ∀ j, p < j → j < M.length → le0 M p j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hpj hj
    obtain ⟨a, haj, hpa, halt, hamax⟩ :
        ∃ a, a < j ∧ p ≤ a ∧ entry M 0 a < entry M 0 j ∧
          ∀ x, a < x → x < j → entry M 0 j ≤ entry M 0 x := by
      classical
      have hpT : p ∈ (Finset.range j).filter
          (fun x => p ≤ x ∧ entry M 0 x < entry M 0 j) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨hpj, le_refl _, hshallow j hpj hj⟩
      have hTne : ((Finset.range j).filter
          (fun x => p ≤ x ∧ entry M 0 x < entry M 0 j)).Nonempty := ⟨p, hpT⟩
      have hmem := Finset.max'_mem _ hTne
      simp only [Finset.mem_filter, Finset.mem_range] at hmem
      refine ⟨Finset.max' _ hTne, hmem.1, hmem.2.1, hmem.2.2, ?_⟩
      intro x hx1 hx2
      by_contra hc
      push Not at hc
      have hxT : x ∈ (Finset.range j).filter
          (fun x => p ≤ x ∧ entry M 0 x < entry M 0 j) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨hx2, by omega, hc⟩
      exact absurd (Finset.le_max' _ x hxT) (by omega)
    have hstep : nextrel0 M a j :=
      ⟨by omega, hj, haj, halt, fun x hx => hamax x hx.1 hx.2⟩
    rcases Nat.eq_or_lt_of_le hpa with hpe | hplt
    · refine ⟨hp, hj, ?_⟩
      rw [hpe]
      exact Relation.ReflTransGen.single hstep
    · obtain ⟨-, -, hrt⟩ := ih a haj hplt (by omega)
      exact ⟨hp, hj, hrt.tail hstep⟩

/-- ★★★★★★★ **(W12b) の答え**: 窓の根が行 0 で狭義最浅なら
（＝ `hr0_wnd`、L3 の §221 で**無料**）、

    ★ 窓の内部列 `j` の `nextrel0` の親は**必ず窓の中**
    ★★ しかも **窓の根 `p` 自身が `j` の `le0` 祖先**

⟹ ⟹ ★★★ **証人の候補は必ず窓の中にある**。⟹ 残るのは**行 1 の条件だけ**。 -/
theorem window_witness_in_window {M : TrioSeq} {p j : ℕ} (hp : p < M.length)
    (hshallow : ∀ x, p < x → x < M.length → entry M 0 p < entry M 0 x)
    (hpj : p < j) (hj : j < M.length) :
    le0 M p j ∧ (∀ a, nextrel0 M a j → p ≤ a) :=
  ⟨le0_root_of_shallow hp hshallow j hpj hj,
   fun _ h => nextrel0_src_ge_of_shallow hshallow hpj h⟩


theorem nextrel0_drop_iff {M : TrioSeq} (p c d : ℕ) :
    nextrel0 (M.drop p) c d ↔ nextrel0 M (p + c) (p + d) := by
  have hlen : (M.drop p).length = M.length - p := List.length_drop
  constructor
  · rintro ⟨hc, hd, hcd, hlt, hmin⟩
    rw [hlen] at hc hd
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩
    · rw [entry_drop, entry_drop] at hlt; exact hlt
    · intro x hx
      have h := hmin (x - p) ⟨by omega, by omega⟩
      rw [entry_drop, entry_drop, show p + (x - p) = x from by omega] at h
      exact h
  · rintro ⟨hc, hd, hcd, hlt, hmin⟩
    refine ⟨by rw [hlen]; omega, by rw [hlen]; omega, by omega, ?_, ?_⟩
    · rw [entry_drop, entry_drop]; exact hlt
    · intro x hx
      rw [entry_drop, entry_drop]
      exact hmin (p + x) ⟨by omega, by omega⟩

theorem rtg0_drop_of {M : TrioSeq} {p c d : ℕ}
    (h : Relation.ReflTransGen (nextrel0 (M.drop p)) c d) :
    Relation.ReflTransGen (nextrel0 M) (p + c) (p + d) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail x y _ hxy ih => exact ih.tail ((nextrel0_drop_iff p x y).mp hxy)

theorem le0_drop_of {M : TrioSeq} {p c d : ℕ} (hc : p + c < M.length)
    (hd : p + d < M.length) (h : le0 (M.drop p) c d) : le0 M (p + c) (p + d) := by
  obtain ⟨-, -, hrt⟩ := h
  exact ⟨hc, hd, rtg0_drop_of hrt⟩

theorem le0_drop_to {M : TrioSeq} {p c d : ℕ} (hp : p ≤ c)
    (h : le0 M c d) : le0 (M.drop p) (c - p) (d - p) := by
  obtain ⟨hcl, hdl, hrt⟩ := h
  have hlen : (M.drop p).length = M.length - p := List.length_drop
  have hcd : c ≤ d := rtg0_index_le hrt
  exact ⟨by rw [hlen]; omega, by rw [hlen]; omega, rtg0_drop hp hrt⟩

/-- ★★★★★★★ **`nextrel1` も窓へ移る**（`le0` 祖先が両向きに移るから）。 -/
theorem nextrel1_drop_of {M : TrioSeq} {p c d : ℕ} (hc : p + c < M.length)
    (hd : p + d < M.length) (h : nextrel1 (M.drop p) c d) :
    nextrel1 M (p + c) (p + d) := by
  obtain ⟨-, -, hcd, hlt, hle0, hmin⟩ := h
  refine ⟨hc, hd, by omega, ?_, le0_drop_of hc hd hle0, ?_⟩
  · rw [entry_drop, entry_drop] at hlt; exact hlt
  · intro x hx
    have hxlt : x < M.length := hx.2.1
    have hle : le0 (M.drop p) (x - p) d := by
      have hh := le0_drop_to (p := p) (show p ≤ x by omega) hx.2
      rwa [show p + d - p = d from by omega] at hh
    have h := hmin (x - p) ⟨by omega, hle⟩
    rw [entry_drop, entry_drop, show p + (x - p) = x from by omega] at h
    exact h


theorem no_row0_parent_from_before_block {A Q : TrioSeq} {d e n j c : ℕ}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hj : j < Q.length) (hj0 : 0 < j)
    (hc : c < (A ++ mTower Q d e n).length) :
    ¬ nextrel0 (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        c ((A ++ mTower Q d e n).length + j) := by
  set P := A ++ mTower Q d e n with hP
  set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
  set M := P ++ B.take (j + 1) with hM
  have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
  have hTlen : (B.take (j + 1)).length = j + 1 := by
    rw [List.length_take, hBlen]; omega
  have hMlen : M.length = P.length + (j + 1) := by
    rw [hM, List.length_append, hTlen]
  have hshallow : ∀ x, P.length < x → x < M.length →
      entry M 0 P.length < entry M 0 x := by
    intro x hx1 hx2
    rw [hMlen] at hx2
    obtain ⟨r, rfl⟩ : ∃ r, x = P.length + r := ⟨x - P.length, by omega⟩
    have hr : 0 < r ∧ r < j + 1 := by omega
    have e0 : entry M 0 P.length = entry Q 0 0 + d * n := by
      have h : entry M 0 P.length = entry (B.take (j + 1)) 0 0 := by
        rw [hM]; simpa using entry_append_right P (B.take (j + 1)) 0 0
      rw [h, Wset.entry_take (show (0:ℕ) < j + 1 by omega), hB, entry0_Lift1,
        entry0_shiftr01 (W := Q) (d0 := d * n) (d1 := 0) (p := 0)
          (by simpa using (show 0 < Q.length by omega))]
    have er : entry M 0 (P.length + r) = entry Q 0 r + d * n := by
      rw [hM, entry_append_right, Wset.entry_take (show r < j + 1 by omega), hB,
        entry0_Lift1,
        entry0_shiftr01 (W := Q) (d0 := d * n) (d1 := 0) (p := r)
          (by simpa using (show r < Q.length by omega))]
    rw [e0, er]
    have := hr0 r hr.1 (by omega)
    omega
  intro hcon
  exact absurd (nextrel0_src_ge_of_shallow hshallow (by omega) hcon) (by omega)


/-- ★★★ `le1` の鎖が接頭辞から `T` に入るなら、**越境点が取れる**。 -/
theorem rtg1_cross_point {A T : TrioSeq} {y b : ℕ} (hy : y < A.length)
    (h : Relation.ReflTransGen (nextrel1 (A ++ T)) y b) :
    b < A.length ∨ ∃ c m', c < A.length ∧ m' < T.length ∧
      nextrel1 (A ++ T) c (A.length + m') ∧
      Relation.ReflTransGen (nextrel1 (A ++ T)) (A.length + m') b := by
  induction h with
  | refl => exact Or.inl hy
  | @tail c b _ hcb ih =>
      rcases ih with hc | ⟨c0, m0, hc0, hm0, hcr, hrt⟩
      · rcases Nat.lt_or_ge b A.length with hb | hb
        · exact Or.inl hb
        · have hblen : b < (A ++ T).length := hcb.2.1
          have hbT : b - A.length < T.length := by
            rw [List.length_append] at hblen; omega
          have hbe : b = A.length + (b - A.length) := by omega
          refine Or.inr ⟨c, b - A.length, hc, hbT, ?_, ?_⟩
          · rw [← hbe]; exact hcb
          · rw [← hbe]
      · exact Or.inr ⟨c0, m0, hc0, hm0, hcr, hrt.tail hcb⟩

/-- ★★★★★★ **行 2 の壁は「的の `le1` 祖先が非ブロッカー」＋ `hcone` だけで立つ**
（`hnb` の ∀ が「的の祖先」に縮む）。 -/
theorem no_nextrel2_cross_of_anc {A T : TrioSeq} {m : ℕ}
    (hmin : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    (hanc : ∀ m', 0 < m' → m' < T.length →
      Relation.ReflTransGen (nextrel1 (A ++ T)) (A.length + m') (A.length + m) →
      entry T 1 0 < entry T 1 m')
    (hcone : entry T 2 0 < entry T 2 m)
    {c : ℕ} (hc : c < A.length) (_hm : m < T.length) (hm0 : 0 < m) :
    ¬ nextrel2 (A ++ T) c (A.length + m) := by
  intro h
  obtain ⟨-, hlen, -, -, hle1, hmin2⟩ := h
  obtain ⟨-, -, hrt⟩ := hle1
  rcases rtg1_cross_point hc hrt with hb | ⟨c0, m0, hc0, hm0T, hcr, hrt2⟩
  · omega
  · rcases Nat.eq_zero_or_pos m0 with h0 | hp
    · subst h0
      have hA : A.length < (A ++ T).length := by
        have := hcr.2.1; omega
      have hroot : le1 (A ++ T) A.length (A.length + m) := by
        refine ⟨hA, hlen, ?_⟩
        have hh := hrt2
        rwa [show A.length + 0 = A.length from by omega] at hh
      have hval := hmin2 A.length ⟨by omega, hroot⟩
      rw [entry_append_right, show A.length = A.length + 0 from by omega,
        entry_append_right] at hval
      omega
    · have hbl := nextrel1_cross_is_blocker hmin hc0 hm0T hp hcr
      exact absurd (hanc m0 hp hm0T hrt2) (by omega)


/-- `nextrel1` の始点は一意（最小性から）。 -/
theorem nextrel1_src_unique {M : TrioSeq} {c1 c2 b : ℕ}
    (h1 : nextrel1 M c1 b) (h2 : nextrel1 M c2 b) : c1 = c2 := by
  obtain ⟨-, -, hc1, hlt1, hle1, hmin1⟩ := h1
  obtain ⟨-, -, hc2, hlt2, hle2, hmin2⟩ := h2
  rcases Nat.lt_trichotomy c1 c2 with h | h | h
  · exact absurd (hmin1 c2 ⟨h, hle2⟩) (by omega)
  · exact h
  · exact absurd (hmin2 c1 ⟨h, hle1⟩) (by omega)

theorem rtg1_index_le {M : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel1 M) a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl _
  | tail _ hstep ih => exact le_trans ih (le_of_lt hstep.2.2.1)

/-- ★★★ 鎖の一意性: 的の `le1` 祖先は、**根からの鎖の上にある**。 -/
theorem rtg1_merge {M : TrioSeq} {m : ℕ}
    (h0 : Relation.ReflTransGen (nextrel1 M) 0 m) :
    ∀ m', Relation.ReflTransGen (nextrel1 M) m' m →
      Relation.ReflTransGen (nextrel1 M) 0 m' := by
  induction h0 with
  | refl =>
      intro m' h
      have := rtg1_index_le h
      have hm0 : m' = 0 := by omega
      rw [hm0]
  | @tail c m hac hcm ih =>
      intro m' h
      rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c', hc1, hc2⟩
      · rw [← h1]
        exact hac.tail hcm
      · exact ih m' (by rw [nextrel1_src_unique hc2 hcm] at hc1; exact hc1)

/-- ★★★★★★★ **`hanc` は「的が根の錐の中」1 本から出る**。 -/
theorem hanc_of_cone {T : TrioSeq} {m : ℕ}
    (hcone : Relation.ReflTransGen (nextrel1 T) 0 m) :
    ∀ m', 0 < m' → Relation.ReflTransGen (nextrel1 T) m' m →
      entry T 1 0 < entry T 1 m' := by
  intro m' hm'0 hrt
  have h0 := rtg1_merge hcone m' hrt
  rcases Relation.ReflTransGen.cases_tail h0 with h1 | ⟨c, hc1, hc2⟩
  · omega
  · refine Nat.lt_of_le_of_lt ?_ hc2.2.2.2.1
    clear hc2
    induction hc1 with
    | refl => exact le_refl _
    | tail _ hstep ih => exact le_trans ih (le_of_lt hstep.2.2.2.1)


/-- ★★★★ **行 1: 的が非ブロッカーなら、親の始点は必ずブロックの根以降**。 -/
theorem nextrel1_src_ge_of_shallow {M : TrioSeq} {p a b : ℕ}
    (hshallow : ∀ x, p < x → x < M.length → entry M 0 p < entry M 0 x)
    (hp : p < M.length) (hpb : p < b) (hb : b < M.length)
    (hnb : entry M 1 p < entry M 1 b) (h : nextrel1 M a b) : p ≤ a := by
  by_contra hc
  push Not at hc
  have hle0 : le0 M p b := le0_root_of_shallow hp hshallow b hpb hb
  exact absurd (h.2.2.2.2.2 p ⟨hc, hle0⟩) (by omega)

/-- ★★★★ **行 2: 的が行 1 の錐の中で行 2 も上なら、親の始点はブロックの根以降**。 -/
theorem nextrel2_src_ge_of_cone {M : TrioSeq} {p a b : ℕ}
    (hcone : le1 M p b) (hnb2 : entry M 2 p < entry M 2 b)
    (h : nextrel2 M a b) : p ≤ a := by
  by_contra hc
  push Not at hc
  exact absurd (h.2.2.2.2.2 p ⟨hc, hcone⟩) (by omega)

/-- ★★★★★★ **3 行そろい**: 的が「行 0 で根より深い ∧ 行 1 で根より上 ∧ 行 2 で根より上」なら、
**どの行でもブロックの根より前の列は親になれない**。 -/
theorem nextR_src_ge_of_cone {M : TrioSeq} {p a b r : ℕ}
    (hshallow : ∀ x, p < x → x < M.length → entry M 0 p < entry M 0 x)
    (hp : p < M.length) (hpb : p < b) (hb : b < M.length)
    (hnb1 : entry M 1 p < entry M 1 b)
    (hcone : le1 M p b) (hnb2 : entry M 2 p < entry M 2 b)
    (h : nextR M r a b) : p ≤ a := by
  unfold nextR at h
  by_cases h0 : r = 0
  · rw [if_pos h0] at h
    exact nextrel0_src_ge_of_shallow hshallow hpb h
  · rw [if_neg h0] at h
    by_cases h1 : r = 1
    · rw [if_pos h1] at h
      exact nextrel1_src_ge_of_shallow hshallow hp hpb hb hnb1 h
    · rw [if_neg h1] at h
      exact nextrel2_src_ge_of_cone hcone hnb2 h


/-- ★★★ 証人を `nextrel1` の親に取れば **`hcls` は推移律で自動**。 -/
theorem witness_of_nextrel1 {V : TrioSeq} {y t : ℕ} (h : nextrel1 V y t) :
    y < t ∧ le0 V y t ∧ entry V 1 y < entry V 1 t ∧ (le1 V 0 y → le1 V 0 t) := by
  refine ⟨h.2.2.1, h.2.2.2.2.1, h.2.2.2.1, ?_⟩
  intro hy
  exact ⟨hy.1, h.2.1, hy.2.2.tail h⟩

open Classical in
/-- ★★★★★ 逆: **証人があれば `nextrel1` の親が存在する**（`le0` 祖先の最大元）。 -/
theorem nextrel1_of_witness {V : TrioSeq} {y t : ℕ}
    (hyt : y < t) (hle0 : le0 V y t) (hlt : entry V 1 y < entry V 1 t) :
    ∃ y', nextrel1 V y' t := by
  have ht : t < V.length := hle0.2.1
  have hyl : y < V.length := hle0.1
  have hyT : y ∈ (Finset.range t).filter
      (fun x => le0 V x t ∧ entry V 1 x < entry V 1 t) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hyt, hle0, hlt⟩
  have hTne : ((Finset.range t).filter
      (fun x => le0 V x t ∧ entry V 1 x < entry V 1 t)).Nonempty := ⟨y, hyT⟩
  have hmem := Finset.max'_mem _ hTne
  simp only [Finset.mem_filter, Finset.mem_range] at hmem
  obtain ⟨hmt, hmle0, hmlt⟩ := hmem
  refine ⟨_, hmle0.1, ht, hmt, hmlt, hmle0, ?_⟩
  intro x hx
  by_contra hc
  push Not at hc
  have hxt : x < t := by
    rcases Nat.lt_or_ge x t with h | h
    · exact h
    · exfalso
      have := hx.2
      have hxle : x ≤ t := rtg0_index_le this.2.2
      have hxe : x = t := by omega
      rw [hxe] at hc
      omega
  have hxT : x ∈ (Finset.range t).filter
      (fun x => le0 V x t ∧ entry V 1 x < entry V 1 t) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hxt, hx.2, hc⟩
  exact absurd (Finset.le_max' _ x hxT) (by omega)


theorem le1_root_of_hlocQ {V : TrioSeq}
    (hpar : ∀ t, 0 < t → t < V.length → 0 < entry V 1 t → ∃ y, nextrel1 V y t)
    (hnz : ∀ t, 0 < t → t < V.length → 0 < entry V 1 t) :
    ∀ t, t < V.length → le1 V 0 t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    rcases Nat.eq_zero_or_pos t with h0 | hp
    · subst h0
      exact ⟨ht, ht, Relation.ReflTransGen.refl⟩
    · obtain ⟨y, hy⟩ := hpar t hp ht (hnz t hp ht)
      have hyt : y < t := hy.2.2.1
      obtain ⟨-, -, hrt⟩ := ih y hyt (by omega)
      exact ⟨by omega, ht, hrt.tail hy⟩

/-- ★★★★★★★ ⟹ **`hlocQ` ＋「行 1 が 0 の列が無い」で、私の行 2 の壁の前提が出る**。 -/
theorem hanc_of_hlocQ {V : TrioSeq}
    (hpar : ∀ t, 0 < t → t < V.length → 0 < entry V 1 t → ∃ y, nextrel1 V y t)
    (hnz : ∀ t, 0 < t → t < V.length → 0 < entry V 1 t)
    {m : ℕ} (hm : m < V.length) :
    ∀ m', 0 < m' → Relation.ReflTransGen (nextrel1 V) m' m →
      entry V 1 0 < entry V 1 m' :=
  hanc_of_cone (le1_root_of_hlocQ hpar hnz m hm).2.2


/-- ★★★★★ **`hnz` は連続部分列へそのまま移る**（根が変わっても壊れない）。 -/
theorem hnz_drop {M : TrioSeq} (p : ℕ)
    (hnz : ∀ i, 0 < i → i < M.length → 0 < entry M 1 i) :
    ∀ t, 0 < t → t < (M.drop p).length → 0 < entry (M.drop p) 1 t := by
  intro t ht0 ht
  rw [List.length_drop] at ht
  rw [entry_drop]
  exact hnz (p + t) (by omega) (by omega)

/-- ★★★★★ **`hnz` は `take` でも壊れない**。 -/
theorem hnz_take {M : TrioSeq} (k : ℕ)
    (hnz : ∀ i, 0 < i → i < M.length → 0 < entry M 1 i) :
    ∀ t, 0 < t → t < (M.take k).length → 0 < entry (M.take k) 1 t := by
  intro t ht0 ht
  rw [List.length_take] at ht
  rw [Wset.entry_take (by omega)]
  exact hnz t ht0 (by omega)

/-- ★★★★★★ **`hnz` は塔へも移る**（`Lift1` は行 1 を下げず、`shiftr01` は変えない）。 -/
theorem hnz_mTower {Q : TrioSeq} (hQ1 : 0 < Q.length)
    (hnz : ∀ i, 0 < i → i < Q.length → 0 < entry Q 1 i)
    (hroot : 0 < entry Q 1 0) {d e n : ℕ} :
    ∀ l, 0 < l → l < (mTower Q d e n).length → 0 < entry (mTower Q d e n) 1 l := by
  intro l hl0 hl
  have hlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  rw [hlen] at hl
  have hi : l % Q.length < Q.length := Nat.mod_lt _ hQ1
  have hk : l / Q.length < n := by
    refine Nat.div_lt_of_lt_mul ?_
    rw [Nat.mul_comm]; exact hl
  have hsplit : l = (l / Q.length) * Q.length + l % Q.length := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod l Q.length).symm
  have hge := entry1_mTower_ge (Q := Q) (d := d) (e := e) (n := n)
    (k := l / Q.length) (i := l % Q.length) hk hi
  rw [← hsplit] at hge
  rcases Nat.eq_zero_or_pos (l % Q.length) with h0 | hp
  · rw [h0] at hge; omega
  · have := hnz _ hp hi
    omega


/-- ★★★ (a) **行 1 が 0 の非根の列は、必ず錐の外**（`nextrel1` の単調性だけ）。 -/
theorem row1_zero_not_le1 {Q : TrioSeq} {i : ℕ} (hi : 0 < i) (h : entry Q 1 i = 0) :
    ¬ le1 Q 0 i :=
  blocker_not_le1 (by omega) (by omega)

open Classical in
/-- ★★★★ (b) **ブロックの行 1 = 0 の列 ⟺ `Q` の行 1 = 0 の列**（非根について）。 -/
theorem row1_zero_block_iff (Q : TrioSeq) {d e n k i : ℕ}
    (hk : k < n) (hi : i < Q.length) (hi0 : 0 < i) :
    entry (mTower Q d e n) 1 (k * Q.length + i) = 0 ↔ entry Q 1 i = 0 := by
  rw [entry1_mTower_block_formula Q hk hi]
  constructor
  · intro h
    split at h <;> omega
  · intro h
    rw [if_neg (row1_zero_not_le1 hi0 h), h]

/-- ★★ ブロックの**根**の行 1 = 0 の条件（`e*k = 0` も要る）。 -/
theorem row1_zero_blockRoot_iff {Q : TrioSeq} (hQne : Q ≠ []) {d e n k : ℕ} (hk : k < n) :
    entry (mTower Q d e n) 1 (k * Q.length) = 0 ↔ entry Q 1 0 = 0 ∧ e * k = 0 := by
  rw [entry1_mTower_blockRoot hQne d e n k hk]
  omega


/-- ★★★★★ **的が非ブロッカーなら `hlocQ` の行 1 成分は自動で立つ**。 -/
theorem hlocQ_row1_of_nonblocker {V : TrioSeq}
    (hr0V : ∀ l, 0 < l → l < V.length → entry V 0 0 < entry V 0 l)
    {t : ℕ} (ht : t < V.length) (ht0 : 0 < t)
    (hnb : entry V 1 0 < entry V 1 t) :
    ∃ y, y < t ∧ le0 V y t ∧ entry V 1 y < entry V 1 t ∧ (le1 V 0 y → le1 V 0 t) := by
  have hV : 0 < V.length := by omega
  have hle0 : le0 V 0 t := le0_root_of_shallow hV hr0V t ht0 ht
  obtain ⟨y', hy'⟩ := nextrel1_of_witness ht0 hle0 hnb
  exact ⟨y', witness_of_nextrel1 hy'⟩

/-- ★★★★★ 対偶: **`hlocQ` の行 1 成分が破れる列は、必ずブロッカー**。 -/
theorem blocker_of_hlocQ_row1_fail {V : TrioSeq}
    (hr0V : ∀ l, 0 < l → l < V.length → entry V 0 0 < entry V 0 l)
    {t : ℕ} (ht : t < V.length) (ht0 : 0 < t)
    (hfail : ¬ ∃ y, y < t ∧ le0 V y t ∧ entry V 1 y < entry V 1 t ∧
      (le1 V 0 y → le1 V 0 t)) :
    entry V 1 t ≤ entry V 1 0 := by
  by_contra hc
  push Not at hc
  exact hfail (hlocQ_row1_of_nonblocker hr0V ht ht0 hc)


/-- 反例の窓。 -/
def coneCtrV : TrioSeq := [(1, 5, 0), (2, 3, 0)]

theorem coneCtrV_len : coneCtrV.length = 2 := rfl

/-- ✅ `hnz` は成り立つ。 -/
theorem coneCtrV_hnz : ∀ i, 0 < i → i < coneCtrV.length → 0 < entry coneCtrV 1 i := by
  intro i hi0 hi
  rw [coneCtrV_len] at hi
  have : i = 1 := by omega
  subst this
  show 0 < entry coneCtrV 1 1
  unfold entry coneCtrV
  simp

/-- ⛔ それでも的は**錐の外**。⟹ **`hnz` は錐の遺伝を救わない**。 -/
theorem coneCtrV_not_cone : ¬ le1 coneCtrV 0 1 :=
  blocker_not_le1 (by omega) (by decide)


/-- ★★★★★★★ **窓は `W` の元**（水準は `lev M p`）。 -/
theorem window_mem_W {u : ℕ} {M : TrioSeq} (h : M ∈ W u) (p k : ℕ) :
    (M.drop p).take k ∈ W (lev M p) :=
  W_take (W_drop h p) k

/-- ★★★★★ `wnd P B j p` の形に合わせたもの
（`wnd P B j p = ((P ++ B.take (j+1)).drop (P.length + p)).take (j - p)`）。 -/
theorem wnd_mem_W {u : ℕ} {P B : TrioSeq} {j p : ℕ}
    (h : P ++ B.take (j + 1) ∈ W u) :
    ((P ++ B.take (j + 1)).drop (P.length + p)).take (j - p)
      ∈ W (lev (P ++ B.take (j + 1)) (P.length + p)) :=
  window_mem_W h (P.length + p) (j - p)


/-- R2 の新条件 C4: **行 1 は `le0` の向きに狭義増加**。 -/
def C4 (Q : TrioSeq) : Prop :=
  ∀ y j, y < j → j < Q.length → le0 Q y j → entry Q 1 y < entry Q 1 j

/-- ★★★★★★ **C4 ⟹ ブロッカーが無い**（根は全列の `le0` 祖先だから）。 -/
theorem hnbQ_of_C4 {Q : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hc4 : C4 Q) :
    ∀ i, 0 < i → i < Q.length → entry Q 1 0 < entry Q 1 i := by
  intro i hi0 hi
  exact hc4 0 i hi0 hi (le0_root_of_shallow (by omega) hr0 i hi0 hi)

/-- ★★★★★★★ **C4 ⟹ 全列が錐の中**。 -/
theorem le1_all_of_C4 {Q : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hc4 : C4 Q) {q : ℕ} (hq : q < Q.length) : le1 Q 0 q :=
  le1_all_of_hnbQ hr0 (hnbQ_of_C4 hr0 hc4) hq

/-- ★★★★★★★ **(C4-2) C4 ⟹ `hlocQ` の行 1 成分**（`hr0` の下）。 -/
theorem hlocQ_row1_of_C4 {Q : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hc4 : C4 Q) {t : ℕ} (ht : t < Q.length) (ht0 : 0 < t) :
    ∃ y, y < t ∧ le0 Q y t ∧ entry Q 1 y < entry Q 1 t ∧ (le1 Q 0 y → le1 Q 0 t) :=
  hlocQ_row1_of_nonblocker hr0 ht ht0 (hnbQ_of_C4 hr0 hc4 t ht0 ht)

/-- ★★★★★ **(C4-1) C4 は `drop` で遺伝する**。 -/
theorem C4_drop {M : TrioSeq} (hc4 : C4 M) (p : ℕ) : C4 (M.drop p) := by
  intro y j hyj hj hle0
  have hlen : (M.drop p).length = M.length - p := List.length_drop
  rw [hlen] at hj
  have hle0' : le0 M (p + y) (p + j) := by
    have hh := le0_drop_of (M := M) (p := p) (c := y) (d := j) (by omega) (by omega) hle0
    exact hh
  have := hc4 (p + y) (p + j) (by omega) (by omega) hle0'
  rw [entry_drop, entry_drop]
  exact this

/-- ★★★★★ **C4 は `take` でも遺伝する**。 -/
theorem C4_take {M : TrioSeq} (hc4 : C4 M) (k : ℕ) : C4 (M.take k) := by
  rcases Nat.lt_or_ge M.length k with hk | hk
  · rwa [List.take_of_length_le (by omega)]
  · intro y j hyj hj hle0
    have hlen : (M.take k).length = min k M.length := List.length_take
    have hjk : j < k := by omega
    have hjM : j < M.length := by omega
    have hle0' : le0 M y j := (le0_take (X := M) (l := k) (a := y) (b := j) hk hjk).mp hle0
    rw [Wset.entry_take hjk, Wset.entry_take (show y < k by omega)]
    exact hc4 y j hyj hjM hle0'


def c4CtrM : TrioSeq := [(0, 0, 0), (1, 0, 0)]

theorem c4CtrM_len : c4CtrM.length = 2 := rfl

theorem c4CtrM_zeroRow2 : ∀ p ∈ c4CtrM, p.2.2 = 0 := by decide

theorem c4CtrM_lev : lev c4CtrM 0 = 0 := by
  unfold lev c4CtrM entry
  simp

/-- ★★ 反例は **すべての `u` で `W u` に入る**。 -/
theorem c4CtrM_mem_W (u : ℕ) : c4CtrM ∈ W u := by
  rw [mem_Wself_iff]
  exact ⟨zeroRow2_mem_Wself c4CtrM_zeroRow2, by rw [c4CtrM_lev]; omega⟩

theorem c4CtrM_le0 : le0 c4CtrM 0 1 := by
  refine ⟨by rw [c4CtrM_len]; omega, by rw [c4CtrM_len]; omega,
    Relation.ReflTransGen.single ?_⟩
  refine ⟨by rw [c4CtrM_len]; omega, by rw [c4CtrM_len]; omega, by omega, ?_, ?_⟩
  · show entry c4CtrM 0 0 < entry c4CtrM 0 1
    unfold entry c4CtrM
    simp
  · intro j hj
    omega

/-- ⛔⛔ **反例: `W` の元だが C4 が偽**。 -/
theorem c4CtrM_not_C4 : ¬ C4 c4CtrM := by
  intro h
  have := h 0 1 (by omega) (by rw [c4CtrM_len]; omega) c4CtrM_le0
  have h0 : entry c4CtrM 1 0 = 0 := by unfold entry c4CtrM; simp
  have h1 : entry c4CtrM 1 1 = 0 := by unfold entry c4CtrM; simp
  omega

/-- ⛔⛔⛔ **`W ⟹ C4` は偽**。 -/
theorem W_not_C4 : ¬ (∀ u : ℕ, ∀ Q ∈ W u, C4 Q) := by
  intro h
  exact c4CtrM_not_C4 (h 0 c4CtrM (c4CtrM_mem_W 0))


/-- ★★★ **塔の全ブロックの根は行 2 = 0**（`hz0` から）。⟹ 行 2 の親の候補になる。 -/
theorem blockRoot_row2_zero {Q : TrioSeq} (hQ1 : 0 < Q.length)
    (hz0 : entry Q 2 0 = 0) {d e n k : ℕ} (hk : k < n) :
    entry (mTower Q d e n) 2 (k * Q.length) = 0 := by
  rw [entry2_mTower_blockRoot Q d e n k hk hQ1]
  exact hz0

/-- ★★★ 接頭辞つき版。 -/
theorem prefix_blockRoot_row2_zero {A Q : TrioSeq} (hQ1 : 0 < Q.length)
    (hz0 : entry Q 2 0 = 0) {d e n k : ℕ} (hk : k < n) :
    entry (A ++ mTower Q d e n) 2 (A.length + k * Q.length) = 0 := by
  rw [entry_append_right]
  exact blockRoot_row2_zero hQ1 hz0 hk


def c4CtrM2 : TrioSeq := [(0, 0, 0), (1, 1, 0), (2, 1, 0)]

theorem c4CtrM2_len : c4CtrM2.length = 3 := rfl

theorem c4CtrM2_zeroRow2 : ∀ p ∈ c4CtrM2, p.2.2 = 0 := by decide

theorem c4CtrM2_lev : lev c4CtrM2 0 = 0 := by
  unfold lev c4CtrM2 entry
  simp

/-- ★★ **すべての `u` で `W u` の元**（`D_1 ∈ W u` は要りません）。 -/
theorem c4CtrM2_mem_W (u : ℕ) : c4CtrM2 ∈ W u := by
  rw [mem_Wself_iff]
  exact ⟨zeroRow2_mem_Wself c4CtrM2_zeroRow2, by rw [c4CtrM2_lev]; omega⟩

/-- ✅ **`hnz` は真**。 -/
theorem c4CtrM2_hnz : ∀ i, 0 < i → i < c4CtrM2.length → 0 < entry c4CtrM2 1 i := by
  intro i hi0 hi
  rw [c4CtrM2_len] at hi
  rcases (by omega : i = 1 ∨ i = 2) with h | h <;> subst h <;>
    · unfold entry c4CtrM2
      simp

theorem c4CtrM2_le0 : le0 c4CtrM2 1 2 := by
  refine ⟨by rw [c4CtrM2_len]; omega, by rw [c4CtrM2_len]; omega,
    Relation.ReflTransGen.single ?_⟩
  refine ⟨by rw [c4CtrM2_len]; omega, by rw [c4CtrM2_len]; omega, by omega, ?_, ?_⟩
  · show entry c4CtrM2 0 1 < entry c4CtrM2 0 2
    unfold entry c4CtrM2
    simp
  · intro j hj
    omega

/-- ⛔ それでも C4 は偽。 -/
theorem c4CtrM2_not_C4 : ¬ C4 c4CtrM2 := by
  intro h
  have hlt := h 1 2 (by omega) (by rw [c4CtrM2_len]; omega) c4CtrM2_le0
  have h1 : entry c4CtrM2 1 1 = 1 := by unfold entry c4CtrM2; simp
  have h2 : entry c4CtrM2 1 2 = 1 := by unfold entry c4CtrM2; simp
  omega

/-- ⛔⛔⛔ **`W ∧ hnz ⟹ C4` は偽**（留保なし）。 -/
theorem W_hnz_not_C4 :
    ¬ (∀ u : ℕ, ∀ Q ∈ W u,
        (∀ i, 0 < i → i < Q.length → 0 < entry Q 1 i) → C4 Q) := by
  intro h
  exact c4CtrM2_not_C4 (h 0 c4CtrM2 (c4CtrM2_mem_W 0) c4CtrM2_hnz)


/-- `nextrel1` を連続部分列へ落とす向き（`M` ⟹ `M.drop p`）。 -/
theorem nextrel1_drop_to {M : TrioSeq} {p c d : ℕ}
    (h : nextrel1 M (p + c) (p + d)) : nextrel1 (M.drop p) c d := by
  obtain ⟨hc, hd, hcd, hlt, hle0, hmin⟩ := h
  have hlen : (M.drop p).length = M.length - p := List.length_drop
  refine ⟨by rw [hlen]; omega, by rw [hlen]; omega, by omega, ?_, ?_, ?_⟩
  · rw [entry_drop, entry_drop]; exact hlt
  · have hh := le0_drop_to (M := M) (p := p) (show p ≤ p + c by omega) hle0
    rwa [show p + c - p = c from by omega, show p + d - p = d from by omega] at hh
  · intro x hx
    rw [entry_drop, entry_drop]
    refine hmin (p + x) ⟨by omega, ?_⟩
    have hxl : x < (M.drop p).length := hx.2.1
    rw [hlen] at hxl
    exact le0_drop_of (by omega) (by omega) hx.2

/-- ★★ 接頭辞つきの `le1` の鎖を、`T` の中の鎖に落とす。 -/
theorem rtg1_append_to {A T : TrioSeq} {c d : ℕ}
    (h : Relation.ReflTransGen (nextrel1 (A ++ T)) (A.length + c) (A.length + d)) :
    Relation.ReflTransGen (nextrel1 T) c d := by
  have hdrop : (A ++ T).drop A.length = T := by simp
  have key : ∀ (a b : ℕ), Relation.ReflTransGen (nextrel1 (A ++ T)) a b →
      A.length ≤ a →
      Relation.ReflTransGen (nextrel1 T) (a - A.length) (b - A.length) := by
    intro a b hr ha
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | @tail x y hxy hy ih =>
        refine ih.tail ?_
        have hxge : A.length ≤ x := le_trans ha (rtg1_index_le hxy)
        have hxy' : x < y := hy.2.2.1
        have hstep := nextrel1_drop_to (M := A ++ T) (p := A.length)
          (c := x - A.length) (d := y - A.length)
          (by rw [show A.length + (x - A.length) = x from by omega,
                show A.length + (y - A.length) = y from by omega]
              exact hy)
        rwa [hdrop] at hstep
  have hk := key _ _ h (by omega)
  rwa [show A.length + c - A.length = c from by omega,
    show A.length + d - A.length = d from by omega] at hk

/-- ★★★★★★ 前提は `hmin`（＝ `hr0`）＋ `hz0` ＋ **「的が錐の中」**だけ。 -/
theorem no_nextR_srow_cross_of_cone {A T : TrioSeq}
    (hmin : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    (hz0 : entry T 2 0 = 0)
    {c m : ℕ} (hc : c < A.length) (hm : m < T.length) (hm0 : 0 < m)
    (hcone : le1 T 0 m) :
    ¬ nextR (A ++ T) (srow (A ++ T) (A.length + m)) c (A.length + m) := by
  have hnb1 : entry T 1 0 < entry T 1 m := entry1_lt_of_le1_ne hcone (by omega)
  have e1 : entry (A ++ T) 1 (A.length + m) = entry T 1 m := entry_append_right A T 1 m
  have e2 : entry (A ++ T) 2 (A.length + m) = entry T 2 m := entry_append_right A T 2 m
  unfold srow
  rw [e1, e2]
  by_cases h2 : 0 < entry T 2 m
  · rw [if_pos h2]
    unfold nextR
    rw [if_neg (by omega), if_neg (by omega)]
    refine no_nextrel2_cross_of_anc hmin ?_ (by omega) hc hm hm0
    intro m' hm'0 hm'l hrt
    exact hanc_of_cone hcone.2.2 m' hm'0 (rtg1_append_to hrt)
  · rw [if_neg h2]
    by_cases h1 : 0 < entry T 1 m
    · rw [if_pos h1]
      unfold nextR
      rw [if_neg (by omega), if_pos rfl]
      exact no_nextrel1_cross_of_cone hmin hc hm hm0 hnb1
    · rw [if_neg h1]
      unfold nextR
      rw [if_pos rfl]
      intro h
      exact absurd (nextrel0_cross_root hmin hc hm h) (by omega)


/-- `srow` は接頭辞を付けても変わらない（右側の列について）。 -/
theorem srow_append_right (A T : TrioSeq) (m : ℕ) :
    srow (A ++ T) (A.length + m) = srow T m := by
  unfold srow
  rw [entry_append_right, entry_append_right]

/-- ★★★★★★ **(H-CONE) `hasParent_peel_of_noCross` の入力そのもの**。
的が錐の中なら、**接頭辞のどの列も `srow` の行の親になれない**。 -/
theorem noCross_srow_of_cone {A T : TrioSeq}
    (hmin : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    (hz0 : entry T 2 0 = 0)
    {m : ℕ} (hm : m < T.length) (hm0 : 0 < m) (hcone : le1 T 0 m) :
    ∀ y, y < A.length →
      ¬ nextR (A ++ T) (srow (A ++ T) (A.length + m)) y (A.length + m) :=
  fun _ hy => no_nextR_srow_cross_of_cone hmin hz0 hy hm hm0 hcone


/-- ★★★★★ **行 1 の孤児は、必ず根に対してブロッカー**。
（`hr0` の下では根が全列の `le0` 祖先なので、非ブロッカーなら親が作れてしまう。） -/
theorem row1_orphan_is_blocker {T : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    {m : ℕ} (hm : m < T.length) (hm0 : 0 < m)
    (hnp : ¬ hasParent T 1 m) : entry T 1 m ≤ entry T 1 0 := by
  by_contra hc
  push Not at hc
  have hle0 : le0 T 0 m := le0_root_of_shallow (by omega) hr0 m hm0 hm
  obtain ⟨y', hy'⟩ := nextrel1_of_witness hm0 hle0 hc
  refine hnp ⟨y', ?_, ?_⟩
  · show nextR T 1 y' m
    unfold nextR; rw [if_neg (by omega), if_pos rfl]; exact hy'
  · intro b hb
    unfold nextR at hb
    rw [if_neg (by omega), if_pos rfl] at hb
    exact nextrel1_src_unique hb hy'

/-- ★★★★★ ⟹ **接頭辞から来る行 1 の親は、`T` の根より行 1 で下**。 -/
theorem prefix_parent_row1_lt_root {A T : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    {m c : ℕ} (hm : m < T.length) (hm0 : 0 < m)
    (hnp : ¬ hasParent T 1 m)
    (h : nextrel1 (A ++ T) c (A.length + m)) :
    entry (A ++ T) 1 c < entry T 1 0 := by
  have hb := row1_orphan_is_blocker hr0 hm hm0 hnp
  have hlt := h.2.2.2.1
  rw [entry_append_right] at hlt
  omega

/-- ★★★★★★ ⟹ **錐の外でも壁が立つ十分条件**:
「**接頭辞の全列の行 1 が `T` の根の行 1 以上**」。
⟹ ★ `rsum`（行 0 版）の**行 1 版**。⟹ ⟹ 行 1 の孤児について、接頭辞は親を供給できない。 -/
theorem no_prefix_row1_parent_of_high_A {A T : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    {m : ℕ} (hm : m < T.length) (hm0 : 0 < m)
    (hnp : ¬ hasParent T 1 m)
    (hA : ∀ y, y < A.length → entry T 1 0 ≤ entry (A ++ T) 1 y) :
    ∀ c, c < A.length → ¬ nextrel1 (A ++ T) c (A.length + m) := by
  intro c hc h
  exact absurd (prefix_parent_row1_lt_root hr0 hm hm0 hnp h) (by
    have := hA c hc; omega)

/-- ★★★ 対偶: **壁が破れるなら、接頭辞に「`T` の根より行 1 が下の列」がある**。 -/
theorem exists_low_row1_of_prefix_parent {A T : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    {m c : ℕ} (hm : m < T.length) (hm0 : 0 < m) (hc : c < A.length)
    (hnp : ¬ hasParent T 1 m)
    (h : nextrel1 (A ++ T) c (A.length + m)) :
    ∃ y, y < A.length ∧ entry (A ++ T) 1 y < entry T 1 0 :=
  ⟨c, hc, prefix_parent_row1_lt_root hr0 hm hm0 hnp h⟩


/-- ★★★★★ **行 1 の孤児の `le0` 祖先は、全部「的以上」**。 -/
theorem orphan_row1_min {T : TrioSeq} {m : ℕ} (hnp : ¬ hasParent T 1 m) :
    ∀ x, x < m → le0 T x m → entry T 1 m ≤ entry T 1 x := by
  intro x hx hle0
  by_contra hc
  push Not at hc
  obtain ⟨y', hy'⟩ := nextrel1_of_witness hx hle0 hc
  refine hnp ⟨y', ?_, ?_⟩
  · show nextR T 1 y' m
    unfold nextR; rw [if_neg (by omega), if_pos rfl]; exact hy'
  · intro b hb
    unfold nextR at hb
    rw [if_neg (by omega), if_pos rfl] at hb
    exact nextrel1_src_unique hb hy'

open Classical in
/-- ★★★★★★★ **接頭辞の行 1 の親の存在は、単純な条件と同値**（孤児の前提の下で）。 -/
theorem prefix_parent_iff_of_orphan {A T : TrioSeq} {m : ℕ}
    (hm : m < T.length) (hnp : ¬ hasParent T 1 m) :
    (∃ c, c < A.length ∧ nextrel1 (A ++ T) c (A.length + m))
      ↔ (∃ y, y < A.length ∧ le0 (A ++ T) y (A.length + m) ∧
           entry (A ++ T) 1 y < entry T 1 m) := by
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, h.2.2.2.2.1, ?_⟩
    have := h.2.2.2.1
    rw [entry_append_right] at this
    exact this
  · rintro ⟨y0, hy0, hle00, hlt0⟩
    have hTgt : A.length + m < (A ++ T).length := by
      rw [List.length_append]; omega
    have hyT : y0 ∈ (Finset.range A.length).filter
        (fun y => le0 (A ++ T) y (A.length + m) ∧
          entry (A ++ T) 1 y < entry T 1 m) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hy0, hle00, hlt0⟩
    have hTne : ((Finset.range A.length).filter
        (fun y => le0 (A ++ T) y (A.length + m) ∧
          entry (A ++ T) 1 y < entry T 1 m)).Nonempty := ⟨y0, hyT⟩
    have hmem := Finset.max'_mem _ hTne
    simp only [Finset.mem_filter, Finset.mem_range] at hmem
    obtain ⟨hcA, hcle0, hclt⟩ := hmem
    refine ⟨_, hcA, hcle0.1, hTgt, by omega, ?_, hcle0, ?_⟩
    · rw [entry_append_right]; exact hclt
    · intro x hx
      rw [entry_append_right]
      rcases Nat.lt_or_ge x A.length with hxA | hxA
      · by_contra hcon
        push Not at hcon
        have hxT : x ∈ (Finset.range A.length).filter
            (fun y => le0 (A ++ T) y (A.length + m) ∧
              entry (A ++ T) 1 y < entry T 1 m) := by
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨hxA, hx.2, hcon⟩
        exact absurd (Finset.le_max' _ x hxT) (by omega)
      · obtain ⟨x', rfl⟩ : ∃ x', x = A.length + x' := ⟨x - A.length, by omega⟩
        rw [entry_append_right]
        rcases Nat.eq_or_lt_of_le (show x' ≤ m from by
          have := rtg0_index_le hx.2.2.2; omega) with hxe | hxlt
        · rw [hxe]
        · have hle0T : le0 T x' m := by
            have hh := le0_drop_to (M := A ++ T) (p := A.length)
              (show A.length ≤ A.length + x' from by omega) hx.2
            have hdrop : (A ++ T).drop A.length = T := by simp
            rwa [hdrop, show A.length + x' - A.length = x' from by omega,
              show A.length + m - A.length = m from by omega] at hh
          exact orphan_row1_min hnp x' hxlt hle0T


/-- ★★★ (W24) team-lead の 1 行: **根の行 1 が 0 なら `rsum1` は自動**。 -/
theorem rsum1_of_root_row1_zero {A T : TrioSeq} (h : entry T 1 0 = 0) :
    ∀ y, y < A.length → entry T 1 0 ≤ entry (A ++ T) 1 y := by
  intro y _
  rw [h]
  exact Nat.zero_le _

/-- ★★★★ ⟹ 壁の版（`hA` を「根の行 1 = 0」に置き換えたもの）。 -/
theorem no_prefix_row1_parent_of_root_zero {A T : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    {m : ℕ} (hm : m < T.length) (hm0 : 0 < m)
    (hnp : ¬ hasParent T 1 m) (hroot1 : entry T 1 0 = 0) :
    ∀ c, c < A.length → ¬ nextrel1 (A ++ T) c (A.length + m) :=
  no_prefix_row1_parent_of_high_A hr0 hm hm0 hnp (rsum1_of_root_row1_zero hroot1)

/-- ★★★★★★★ **もっと強い**: 根の行 1 が 0 なら、**行 1 の孤児はそもそも存在しない**。 -/
theorem no_row1_orphan_of_root_zero {T : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    {m : ℕ} (hm : m < T.length) (hm0 : 0 < m)
    (hroot1 : entry T 1 0 = 0) (hpos : 0 < entry T 1 m) :
    hasParent T 1 m := by
  by_contra hnp
  have := row1_orphan_is_blocker hr0 hm hm0 hnp
  omega

/-- ★ 組み立ての形: **塔＋ブロックの根の行 1 は `Q` の根の行 1**。
⟹ ですから条件は **`entry Q 1 0 = 0`**。 -/
theorem entry1_tower_append_root {Q B : TrioSeq} (hQne : Q ≠ []) {d e n : ℕ} (hn : 0 < n) :
    entry (mTower Q d e n ++ B) 1 0 = entry Q 1 0 := by
  have hlen : 0 < (mTower Q d e n).length := by
    rw [mTower_length]
    exact Nat.mul_pos hn (List.length_pos_iff.mpr hQne)
  rw [entry_append_left _ _ hlen]
  have := entry1_mTower_blockRoot hQne d e n 0 hn
  simpa using this


theorem rtg0_through_p {M : TrioSeq} {p y b : ℕ}
    (hshallow : ∀ x, p < x → x < M.length → entry M 0 p < entry M 0 x)
    (hy : y < p) {h : Relation.ReflTransGen (nextrel0 M) y b} (hpb : p < b) :
    Relation.ReflTransGen (nextrel0 M) y p ∧
      Relation.ReflTransGen (nextrel0 M) p b := by
  induction h with
  | refl => omega
  | @tail c b hyc hcb ih =>
      have hpc : p ≤ c := nextrel0_src_ge_of_shallow hshallow hpb hcb
      rcases Nat.eq_or_lt_of_le hpc with he | hlt
      · refine ⟨?_, ?_⟩
        · rw [he]; exact hyc
        · rw [he]; exact Relation.ReflTransGen.single hcb
      · obtain ⟨h1, h2⟩ := ih hlt
        exact ⟨h1, h2.tail hcb⟩

/-- ★★★★★ **`le0` 版**: 道は必ず `p` を通る。 -/
theorem le0_through_p {M : TrioSeq} {p y j : ℕ}
    (hshallow : ∀ x, p < x → x < M.length → entry M 0 p < entry M 0 x)
    (hp : p < M.length) (hy : y < p) (hpj : p < j)
    (h : le0 M y j) : le0 M y p ∧ le0 M p j := by
  obtain ⟨hyl, hjl, hrt⟩ := h
  obtain ⟨h1, h2⟩ := rtg0_through_p hshallow hy (h := hrt) hpj
  exact ⟨⟨hyl, hp, h1⟩, ⟨hp, hjl, h2⟩⟩

/-- `hr0 T` から `A ++ T` の `hshallow`（`p := |A|`）を作る。 -/
theorem hshallow_append_of_hr0 {A T : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l) :
    ∀ x, A.length < x → x < (A ++ T).length →
      entry (A ++ T) 0 A.length < entry (A ++ T) 0 x := by
  intro x hx1 hx2
  rw [List.length_append] at hx2
  obtain ⟨r, rfl⟩ : ∃ r, x = A.length + r := ⟨x - A.length, by omega⟩
  have e0 : entry (A ++ T) 0 A.length = entry T 0 0 := by
    simpa using entry_append_right A T 0 0
  have er : entry (A ++ T) 0 (A.length + r) = entry T 0 r := entry_append_right A T 0 r
  rw [e0, er]
  exact hr0 r (by omega) (by omega)

/-- ★★★★★★ **(W25) 証人は「`T` の根の `le0` 祖先」に絞れる**。
⟹ ★ 私の同値（§329）＋「道は必ず根を通る」（上）の合成。 -/
theorem prefix_parent_iff_of_orphan_through_root {A T : TrioSeq} {m : ℕ}
    (hr0 : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    (hm : m < T.length) (hm0 : 0 < m) (hnp : ¬ hasParent T 1 m) :
    (∃ c, c < A.length ∧ nextrel1 (A ++ T) c (A.length + m))
      ↔ (∃ y, y < A.length ∧ le0 (A ++ T) y A.length ∧
           entry (A ++ T) 1 y < entry T 1 m) := by
  have hshallow := hshallow_append_of_hr0 (A := A) hr0
  have hAlen : A.length < (A ++ T).length := by rw [List.length_append]; omega
  have hroot : le0 (A ++ T) A.length (A.length + m) :=
    le0_root_of_shallow hAlen hshallow (A.length + m) (by omega)
      (by rw [List.length_append]; omega)
  rw [prefix_parent_iff_of_orphan hm hnp]
  constructor
  · rintro ⟨y, hy, hle0, hlt⟩
    exact ⟨y, hy, (le0_through_p hshallow hAlen hy (by omega) hle0).1, hlt⟩
  · rintro ⟨y, hy, hle0, hlt⟩
    refine ⟨y, hy, ⟨hle0.1, hroot.2.1, hle0.2.2.trans hroot.2.2⟩, hlt⟩

end H12Export
end TRIO
