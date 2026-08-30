/-
L106.lean: 課題 L105 の**合成点**。

`L105Cap.lean`（L3）と `H12H2.lean`（H12）の成果を合わせて、
R2 の測度 **`(|V|, rankDE d e)`** の減少を組む場所。

⚠ **`H12H2.lean` は H12 の作業ファイルで、いまも編集されている。**
**⟹ ここには `import` せず、必要な補題を**署名を逐語で**写す**（team-lead の規則）。

⚠ **本文中の割合はすべて特定の箱での実測である。**
**箱は `tools/dbms/H1-NOTES.md`（H12）と `tools/dbms/R2-NOTES.md`（R2）にある。**
-/

import L105Cap

namespace TRIO
namespace L106

open Wset
open L105
open Classical

/-! ## 1. ★★★★★★ `rank` の減少（R2 の測度の第 2 成分）

R2 の機構（そのまま）:

> **非減少（`|V'| = |V|`）⟺ 親が直前のブロックの根。**
> **ブロック根どうしは、その行がリフトを受けない限り値が等しい。**
> **`nextrel_i` は狭義不等号を要求 ⟹ 親になれるのは**リフトを受けている行だけ**。**
> **行 0 ＝ `shiftr01 (d*k)` ⟹ `0 < d`。行 1 ＝ `Lift1 (e*k)` ⟹ `0 < e`。**
> **行 2 ＝ リフトされない ⟹ **決して親になれない**。**
> **⟹ `oper` は `srow = 1` で `e' = 0`、`srow = 0` で `d' = e' = 0`。**
> **⟹ **`rankDE` が非減少の段ごとに真に減る** ⟹ **非減少は高々 2 段**。**

`L105Cap` に緑で入っているもの（§198-§199）:

    `rankDE`（`(0<d) + (0<e)`）／`rankDE_le_two`
    `not_nextrel2_blockRoots` … **行 2 は親になれない**
    `d_pos_of_nextrel0_blockRoots` … 行 0 は `0 < d` が要る
    `e_pos_of_nextrel1_blockRoots` … 行 1 は `0 < e` が要る
    `mTower_entry0_root` / `mTower_entry1_root` / `mTower_entry2_root`

**⟹ 以下がその合成である。** -/

/-- **★★★★★★★ `rank` は非減少の段で真に減る。**

前提を逐語で:

    `hle`  … 足す列の `srow` が `1` 以下（`not_nextrel2_blockRoots` から出る）
    `hdd`  … 親と的の行 0 の差が `d`（ブロック根どうしなら `mTower_entry0_root` から）
    `h1`   … `srow = 1` なら `0 < e`（`e_pos_of_nextrel1_blockRoots` から）
    `h0`   … `srow = 0` なら `0 < d`（`d_pos_of_nextrel0_blockRoots` から）

結論は **`oper` が作る `(d', e')` の `rankDE` が、もとの `(d, e)` のそれより真に小さい**。 -/
theorem rankDE_oper_lt {M : TrioSeq} {j0 d e : ℕ}
    (hle : srow M (M.length - 1) ≤ 1)
    (hdd : entry M 0 (M.length - 1) - entry M 0 j0 = d)
    (h1 : srow M (M.length - 1) = 1 → 0 < e)
    (h0 : srow M (M.length - 1) = 0 → 0 < d) :
    rankDE
        (if 0 < srow M (M.length - 1) then entry M 0 (M.length - 1) - entry M 0 j0
          else 0)
        (if 1 < srow M (M.length - 1) then entry M 1 (M.length - 1) - entry M 1 j0
          else 0)
      < rankDE d e := by
  unfold rankDE
  rw [if_neg (show ¬ (1 < srow M (M.length - 1)) from by omega)]
  rcases Nat.eq_zero_or_pos (srow M (M.length - 1)) with hz | hp
  · -- `srow = 0`: `d' = e' = 0`、そして `0 < d`
    rw [if_neg (show ¬ (0 < srow M (M.length - 1)) from by omega)]
    have hdpos : 0 < d := h0 hz
    rw [if_pos hdpos]
    split_ifs <;> omega
  · -- `srow = 1`: `d' = d`、`e' = 0`、そして `0 < e`
    have hs1 : srow M (M.length - 1) = 1 := by omega
    have hepos : 0 < e := h1 hs1
    rw [if_pos hp, hdd, if_pos hepos]
    split_ifs <;> omega

/-! ### 1.1 ⟹ 何が残っているか

    ✅ **`rank` の減少**（上）… 前提 4 本はすべて `L105Cap` §198-§199 から供給できる
    ⛔ **「非減少 ⟺ 親がブロック根」** … H12 の `blockRoot_window_eq_of_root` /
       `blockRoot_window_lt_of_ne_root`（緑）を**ここに写す**必要がある
    ⛔ **測度 `(|V|, rankDE)` の整礎帰納そのもの**

⚠ **教訓 14**: 上は **`rank` が減ることだけ**である。
**「非減少の段でだけ減ればよい」ことは、`|V|` の側と合わせて初めて意味を持つ。** -/


/-! ## 2. ★★★★★★ H12 の成果（`lean/H12Export.lean` から写したもの）

⚠ **`H12H2.lean` は H12 の作業ファイルなので `import` しない**（team-lead の規則）。
**⟹ H12 が**依存閉包だけを集めた** `H12Export.lean`（31 定理・710 行・緑・衝突 0）を作ってくれた。**
**⟹ ★ **緑であること自体が「依存閉包に欠けが無い」証明**である。**

⚠ **私は最初 `H12H2.lean` を**まるごと**（1803 行）写したが、H12 の export に差し替えた。**
**⟹ team-lead の「使うものだけ」がこれで満たされる。1803 → 710 行。** -/


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

/-! ## 200. ★★★★★★★ 場合分けの接続: **どちらの枝でも辞書式 `(|V|, rankDE)` が減る**

R2 の測度（`(|V|, rank(d,e))` の辞書式）を Lean で組みます。**材料は全部そろっています:**

    **枝 1（`p_rel ≥ 1`）** … `|V| < |Q|` … §186（`|V| = j − p`）／ H12 `blockRoot_window_lt_of_ne_root`
    **枝 2（`p_rel = 0`）** … `|V| = |Q|` だが **`rankDE` が減る** … §198・§199 ＋ 下の `rankDE_lt_of_blockRoot_parent`
    **二分法** … H12 `blockRoot_window_eq_iff`（窓 `= |Q|` ⟺ 親がブロック根）

⚠ **`Prod.Lex` の整礎性そのものは H12 が並行で作っています。ここでは「1 段で減る」だけ。** -/

/-! ### 200.1 まず抽象の合成（純粋に算術）

**選言「第 1 成分が減る ∨（第 1 成分が同じ ∧ 第 2 成分が減る）」から `Prod.Lex`。** -/

theorem lex_of_lt_or {a b a' b' : ℕ}
    (h : a' < a ∨ (a' = a ∧ b' < b)) :
    Prod.Lex (α := ℕ) (β := ℕ) (· < ·) (· < ·) (a', b') (a, b) := by
  rcases h with h | ⟨h1, h2⟩
  · exact Prod.Lex.left _ _ h
  · subst h1; exact Prod.Lex.right _ h2

/-! ### 200.2 枝 2 の本体: **親がブロック根なら `rankDE` が真に減る**

`oper` の出す新しいリフト量は（§186 の逐語）

    `d0 = if 0 < srow then entry 0 j1 − entry 0 j0 else 0`
    `d1 = if 1 < srow then entry 1 j1 − entry 1 j0 else 0`

**両方がブロック根（`j1 = m*|Q|`、`j0 = k*|Q|`）のとき、行ごとに:**

    **`srow = 2`** … §198 `not_nextrel2_blockRoots` で**不可能**
    **`srow = 1`** … `d1 = 0`（`¬ 1 < 1`）、`d0 = d*(m−k)`。
                 §199 で `0 < e` ⟹ `rankDE d e ≥ (if 0<d) + 1 > rankDE d0 0`
    **`srow = 0`** … `d0 = d1 = 0` ⟹ `rankDE = 0`。§199 で `0 < d` ⟹ `rankDE d e ≥ 1`

**⟹ ★ どの場合も真に減ります。** -/

theorem rankDE_lt_of_blockRoot_parent {Q : TrioSeq} {d e n k m : ℕ}
    (hQ : 0 < Q.length) (hk : k < n) (hm : m < n) (hkm : k < m)
    (hnr : nextR (mTower Q d e n) (srow (mTower Q d e n) (m * Q.length))
             (k * Q.length) (m * Q.length)) :
    rankDE
        (if 0 < srow (mTower Q d e n) (m * Q.length) then
          entry (mTower Q d e n) 0 (m * Q.length)
            - entry (mTower Q d e n) 0 (k * Q.length) else 0)
        (if 1 < srow (mTower Q d e n) (m * Q.length) then
          entry (mTower Q d e n) 1 (m * Q.length)
            - entry (mTower Q d e n) 1 (k * Q.length) else 0)
      < rankDE d e := by
  have h0m : entry (mTower Q d e n) 0 (m * Q.length) = entry Q 0 0 + d * m :=
    mTower_entry0_root hm hQ
  have h0k : entry (mTower Q d e n) 0 (k * Q.length) = entry Q 0 0 + d * k :=
    mTower_entry0_root hk hQ
  -- 行 2 は不可能（§198）
  have hs2 : ¬ (1 < srow (mTower Q d e n) (m * Q.length)) := by
    intro hc
    have hnr' := hnr
    unfold nextR at hnr'
    rw [if_neg (by omega), if_neg (by omega)] at hnr'
    exact not_nextrel2_blockRoots hk hm hQ hnr'
  rw [if_neg hs2]
  rcases Nat.eq_zero_or_pos (srow (mTower Q d e n) (m * Q.length)) with hz | hp
  · -- srow = 0 ⟹ d0 = d1 = 0、そして 0 < d（§199）
    rw [if_neg (by omega)]
    have hnr' := hnr
    unfold nextR at hnr'
    rw [if_pos hz] at hnr'
    have hd : 0 < d := d_pos_of_nextrel0_blockRoots hk hm hQ hnr'
    unfold rankDE
    rw [if_pos hd]
    split_ifs <;> omega
  · -- srow = 1 ⟹ d1 = 0、d0 = d*(m−k)、そして 0 < e（§199）
    have hs1 : srow (mTower Q d e n) (m * Q.length) = 1 := by omega
    rw [if_pos hp]
    have hnr' := hnr
    unfold nextR at hnr'
    rw [hs1] at hnr'
    rw [if_neg (by omega), if_pos rfl] at hnr'
    have he : 0 < e := e_pos_of_nextrel1_blockRoots hk hm hQ hnr'
    rw [h0m, h0k]
    have hdk : d * k ≤ d * m := Nat.mul_le_mul_left d (by omega)
    have hsub : entry Q 0 0 + d * m - (entry Q 0 0 + d * k) = d * m - d * k := by omega
    rw [hsub]
    unfold rankDE
    rw [if_pos he]
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · have : d * m - d * k = 0 := by rw [hd0]; simp
      rw [this]
      split_ifs <;> omega
    · have : 0 < d * m - d * k := by
        have h1 : d * (k + 1) ≤ d * m := Nat.mul_le_mul_left d (by omega)
        have h2 : d * (k + 1) = d * k + d := Nat.mul_succ d k
        omega
      rw [if_pos this, if_pos hd0]
      split_ifs <;> omega

/-- **`hasParent` ＋「親がブロック根」の形**（H12 の `blockRoot_window_eq_iff` の右辺に合う形）。 -/
theorem rankDE_lt_of_blockRoot_parent' {Q : TrioSeq} {d e n k m : ℕ}
    (hQ : 0 < Q.length) (hk : k < n) (hm : m < n) (hkm : k < m)
    (hp : hasParent (mTower Q d e n) (srow (mTower Q d e n) (m * Q.length))
            (m * Q.length))
    (hpe : parent (mTower Q d e n) (srow (mTower Q d e n) (m * Q.length))
            (m * Q.length) = k * Q.length) :
    rankDE
        (if 0 < srow (mTower Q d e n) (m * Q.length) then
          entry (mTower Q d e n) 0 (m * Q.length)
            - entry (mTower Q d e n) 0 (k * Q.length) else 0)
        (if 1 < srow (mTower Q d e n) (m * Q.length) then
          entry (mTower Q d e n) 1 (m * Q.length)
            - entry (mTower Q d e n) 1 (k * Q.length) else 0)
      < rankDE d e := by
  have hnr := parent_nextR hp
  rw [hpe] at hnr
  exact rankDE_lt_of_blockRoot_parent hQ hk hm hkm hnr

/-! ### 200.3 ★★ そして **枝 1 と枝 2 の合成**

**H12 の `blockRoot_window_eq_iff` が二分法を与えるので、`j = 0` の段はこう割れます:**

    **窓 `< |Q|`** ⟹ 第 1 成分が減る ⟹ `Prod.Lex` ✓
    **窓 `= |Q|`** ⟹ 親はブロック根 ⟹ `rankDE` が減る（§200.2）⟹ `Prod.Lex` ✓

**⟹ ★ 下がその合成です。前提は「窓の値」と「rankDE の値」だけで、
`W` の話は一切入りません。⟹ 測度の部分だけが独立に緑になります。** -/

theorem lex_step_blockRoot {Q : TrioSeq} {d e n k w r : ℕ}
    (hQne : Q ≠ []) (hd : 0 < d) (he : 0 < e) (hk : k + 1 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hp : hasParent (mTower Q d e n) 1 ((k + 1) * Q.length))
    (hw : w = (k + 1) * Q.length - parent (mTower Q d e n) 1 ((k + 1) * Q.length))
    (hwle : w ≤ Q.length)
    (hrank : parent (mTower Q d e n) 1 ((k + 1) * Q.length) = k * Q.length →
      r < rankDE d e) :
    Prod.Lex (α := ℕ) (β := ℕ) (· < ·) (· < ·) (w, r) (Q.length, rankDE d e) := by
  refine lex_of_lt_or ?_
  by_cases hc : w = Q.length
  · right
    refine ⟨hc, hrank ?_⟩
    have hiff := blockRoot_window_eq_iff hQne hd he hk hr0 hp
    exact hiff.mp (by rw [← hw]; exact hc)
  · left; omega

/-! ### 200.4 ⟹ R2 の 6 行が **全部** Lean になりました

    ✅ **行 2 は決して親になれない** … §198 `not_nextrel2_blockRoots`
    ✅ **行 0 は `0 < d` が要る** … §199 `d_pos_of_nextrel0_blockRoots`
    ✅ **行 1 は `0 < e` が要る** … §199 `e_pos_of_nextrel1_blockRoots`
    ✅ **`srow = 1` で `e' = 0`、`srow = 0` で `d' = e' = 0`** … §198 `rankDE_oper_*`
    ✅ **非減少 ⟺ `p_rel = 0`** … H12 `blockRoot_window_eq_iff`
    ✅ **⟹ `rank` が非減少の段ごとに真に減る** … `rankDE_lt_of_blockRoot_parent`（上）
    ✅ **⟹ 辞書式が 1 段で減る** … `lex_step_blockRoot`（上）

⚠ **教訓 14**: 上は **1 段**の話です。**「停止する」は言えていません。**
**⟹ 残るのは (i) `Prod.Lex` の整礎性（H12 が並行）と
(ii) その帰納を `W` の membership に接続する部分（§169 `prefixTowerClosed_final` の形）。**

⚠ **そして `lex_step_blockRoot` の `hrank` は**含意**で渡しています。**
**理由: 枝 1 では `rankDE` について何も言えない（`r` は任意でよい）から。**
**⟹ `hwle`（`w ≤ |Q|`）だけが両枝に共通の前提です。** -/

/-! ## 201. ★★★★★★★★ `hstep` から **錐の条件が消えます**

§169 `prefixTowerClosed_final` は `hstep` に

    **`0 < j → le1 Q 0 j → 親 ≥ (A ++ mTower).length`**

を渡していました。**`le1 Q 0 j`（錐の中）が付いていたのは、錐の外を扱えなかったからです。**

**⟹ ★ H12 の `prefix_window_of_outOfCone_all'` が**錐の外**を埋めました。**
**⟹ ⟹ 2 つを合わせると、`le1 Q 0 j` が**消えます**。**

⚠ **1 つだけ弱くなります: 錐の外では `hasParent` が**ただでは出ません**。**
**⟹ なので新しい形は `0 < j → hasParent … → 親 ≥ …` です。**
**⟹ 消費側は §186 を使うときにどのみち `hasParent` を持っているので、実質は損しません。** -/

open Classical in
theorem prefixTowerClosed_final_noCone {u : ℕ} {A M : TrioSeq} {d e : ℕ}
    (hA : A ∈ W u) (hM2 : 2 ≤ M.length) (he : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0M : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hbase : entry M.dropLast 0 0 = 0)
    (hz0 : entry M.dropLast 2 0 = 0)
    (hstep : ∀ (n j : ℕ), j < M.dropLast.length →
      (0 < j →
        hasParent (A ++ mTower M.dropLast d e n
            ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
          (srow (A ++ mTower M.dropLast d e n
            ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
            (A ++ mTower M.dropLast d e n
              ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length)
          (A ++ mTower M.dropLast d e n
            ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length →
        (A ++ mTower M.dropLast d e n).length ≤
          parent (A ++ mTower M.dropLast d e n
              ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
            (srow (A ++ mTower M.dropLast d e n
              ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
              (A ++ mTower M.dropLast d e n
                ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length)
            (A ++ mTower M.dropLast d e n
              ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length) →
      (∀ j', j' ≤ j →
        A ++ mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j' ∈ W u) →
      A ++ mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1) ∈ W u) :
    ∀ n, A ++ mTower M.dropLast d e n ∈ W u := by
  have hdl : M.dropLast.length = M.length - 1 := List.length_dropLast
  -- `Q = M.dropLast` の上の行 0 の狭義単調
  have hr0Q : ∀ l, 0 < l → l < M.dropLast.length →
      entry M.dropLast 0 0 < entry M.dropLast 0 l := by
    intro l hl0 hl1
    rw [hdl] at hl1
    rw [List.dropLast_eq_take, Wset.entry_take (show (0 : ℕ) < M.length - 1 by omega),
      Wset.entry_take hl1]
    exact hr0M l hl0 (by omega)
  refine prefixTowerClosed_final hA hr0Q hz0 ?_
  intro n j hj hcone hall
  refine hstep n j hj (fun hj1 hpar0 => ?_) hall
  by_cases hc : le1 M 0 (0 + j)
  · -- 錐の中: §169 が渡してくれる前提をそのまま使う
    refine hcone hj1 ?_
    rw [List.dropLast_eq_take]
    refine (Wset.le1_take (X := M) (l := M.length - 1) (a := 0) (b := j)
      (by omega) (by rw [hdl] at hj; omega)).mpr ?_
    simpa using hc
  · -- 錐の外: H12 の窓補題
    exact prefix_window_of_outOfCone_all' hM2 he hd0e hr0M hlp hbase hj hj1 hc hpar0

/-! ## 202. ★★★★★★★★ §186 の**接頭辞つき**版 —— 実は**塔はいりません**

§186 `snocStep_oper_tower` は「`mTower Q d e n ++ B.take (j+1)` の親が同じブロックにあれば、
展開は `接頭辞 ++ mTower V d0 d1 m` で `|V| = j − p`」でした。

**⟹ ★ 証明を読み直すと、使っているのは**長さの算術**と 2 本の一般補題だけです:**

    `Lcone.oper_eq_gexp_gen` … 展開 ＝ `gexp`（`M` について完全に一般）
    §165 `gexp_eq_take_append_mTower` … `gexp` ＝ `take ++ mTower`（同じく一般）

**⟹ ⟹ `mTower Q d e n` の部分は**何でもよい**。`P ++ B.take (j+1)` で書けます。**
**⟹ ⟹ ★ これで §186 も、その接頭辞つき版（`P := A ++ mTower Q d e n`）も、両方**同じ 1 本**です。**

⚠ **これは「一般化したら簡単になった」例です。**
**⟹ 私は §186 を `mTower` に貼りついた形で書いていました。塔は一度も使っていませんでした。** -/

open Classical in
theorem snocStep_oper_pre {P B : TrioSeq} {j p m : ℕ}
    (hjB : j < B.length) (hpj : p < j)
    (hz : ¬ (entry (P ++ B.take (j + 1)) 0 ((P ++ B.take (j + 1)).length - 1) = 0 ∧
      entry (P ++ B.take (j + 1)) 1 ((P ++ B.take (j + 1)).length - 1) = 0 ∧
      entry (P ++ B.take (j + 1)) 2 ((P ++ B.take (j + 1)).length - 1) = 0))
    (hpar : hasParent (P ++ B.take (j + 1))
      (srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1))
      ((P ++ B.take (j + 1)).length - 1))
    (hpe : parent (P ++ B.take (j + 1))
      (srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1))
      ((P ++ B.take (j + 1)).length - 1) = P.length + p) :
    ∃ (V : TrioSeq) (d0 d1 : ℕ), V.length = j - p ∧
      (P ++ B.take (j + 1))⟦m⟧ = (P ++ B.take p) ++ mTower V d0 d1 m := by
  set T := P ++ B.take (j + 1) with hT
  have hTl : T.length = P.length + (j + 1) := by
    rw [hT, List.length_append, List.length_take, Nat.min_eq_left (by omega)]
  have hL : T.length - 1 ≠ 0 := by omega
  have hLb : T.length - 1 - (P.length + p) = j - p := by omega
  have hle : P.length + p + (j - p) ≤ T.length := by omega
  refine ⟨(T.drop (P.length + p)).take (j - p),
    (if 0 < srow T (T.length - 1) then entry T 0 (T.length - 1)
      - entry T 0 (P.length + p) else 0),
    (if 1 < srow T (T.length - 1) then entry T 1 (T.length - 1)
      - entry T 1 (P.length + p) else 0), ?_, ?_⟩
  · rw [List.length_take, List.length_drop]; omega
  · rw [oper_eq_gexp_gen m hL hz hpar, hpe, hLb, gexp_eq_take_append_mTower hle]
    congr 1
    rw [hT, List.take_append, List.take_of_length_le (by omega),
      Nat.add_sub_cancel_left, List.take_take, Nat.min_eq_left (by omega)]

/-! ### 202.1 ⟹ §186 は 1 行の系になります（形の確認） -/

open Classical in
theorem snocStep_oper_tower_pre {A Q : TrioSeq} {d e n j p m : ℕ}
    (hj : j < Q.length) (hpj : p < j)
    (hz : ¬ (entry (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 0
        ((A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1) = 0 ∧
      entry (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 1
        ((A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1) = 0 ∧
      entry (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 2
        ((A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1) = 0))
    (hpar : hasParent (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (srow (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        ((A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1))
      ((A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1))
    (hpe : parent (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (srow (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        ((A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1))
      ((A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1)
      = (A ++ mTower Q d e n).length + p) :
    ∃ (V : TrioSeq) (d0 d1 : ℕ), V.length = j - p ∧
      (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))⟦m⟧
      = (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take p)
        ++ mTower V d0 d1 m := by
  have hBlen : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length = Q.length := by
    rw [Lift1_length, shiftr01_length]
  exact snocStep_oper_pre (P := A ++ mTower Q d e n)
    (B := Lift1 (shiftr01 (d * n) 0 Q) (e * n)) (by omega) hpj hz hpar hpe

/-! ### 202.2 ⟹ **測度の帰納に必要な「1 段の形」がそろいました**

    **`j ≥ 1` かつ親が同ブロック** … `snocStep_oper_tower_pre`（上）で `|V| = j − p < |Q|` ⟹ **枝 1**
    **`j ≥ 1` の親の位置** … §201 `prefixTowerClosed_final_noCone`（錐の条件なし）
    **`j = 0`** … H12 `blockRoot_window_eq_iff` ＋ §200 `rankDE_lt_of_blockRoot_parent` ⟹ **枝 2**
    **辞書式** … §200 `lex_step_blockRoot`

⚠ **残るのは 2 つだけです:**

    **(i)** `Prod.Lex` の整礎性 … **H12 が並行**
    **(ii)** 帰納の遺伝する前提（`hr0(V)` / `hz0(V)` / `hd0e(V)` / `hlp(V)`）… **核**

**⟹ (ii) が R2 の測った「残差 3.4〜6.2%、9〜10% で頭打ち」の正体です。** -/

/-! ## 203. ★★★★★★★★ **`Prod.Lex` は要りません。`rankDE ≤ 2` なので `ℕ` に潰せます**

§200 で辞書式 `(|V|, rankDE)` を使いました。**ですが `rankDE ≤ 2`（§198 `rankDE_le_two`）です。**

> **⟹ ★ 辞書式は `3 * |V| + rankDE` で**ふつうの `ℕ`**に埋まります。**
> **⟹ ⟹ 整礎性は `Nat` の強帰納だけ。`Prod.Lex` も `WellFounded` も要りません。**

**確かめ（2 行）:**

    `w < L` ⟹ `3w + r ≤ 3w + 2 < 3(w+1) ≤ 3L ≤ 3L + R`
    `w = L ∧ r < R` ⟹ `3w + r < 3w + R`

⚠ **「有界な第 2 成分をもつ辞書式は `ℕ` に潰せる」は一般の手筋です。**
**⟹ 私は `Prod.Lex` を H12 に振ってしまいました。振る前に `rankDE ≤ 2` を思い出すべきでした。** -/

def natMeasure (L r : ℕ) : ℕ := 3 * L + r

theorem natMeasure_lt {L R w r : ℕ} (hR : R ≤ 2) (hr : r ≤ 2)
    (h : w < L ∨ (w = L ∧ r < R)) :
    natMeasure w r < natMeasure L R := by
  unfold natMeasure
  rcases h with h | ⟨h1, h2⟩ <;> omega

/-- ★★ **§200 の合成を `ℕ` の測度で書き直したもの**（`Prod.Lex` なし）。 -/
theorem natMeasure_step_blockRoot {Q : TrioSeq} {d e n k w : ℕ} {d0 d1 : ℕ}
    (hQne : Q ≠ []) (hd : 0 < d) (he : 0 < e) (hk : k + 1 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hp : hasParent (mTower Q d e n) 1 ((k + 1) * Q.length))
    (hw : w = (k + 1) * Q.length - parent (mTower Q d e n) 1 ((k + 1) * Q.length))
    (hwle : w ≤ Q.length)
    (hrank : parent (mTower Q d e n) 1 ((k + 1) * Q.length) = k * Q.length →
      rankDE d0 d1 < rankDE d e) :
    natMeasure w (rankDE d0 d1) < natMeasure Q.length (rankDE d e) := by
  refine natMeasure_lt (rankDE_le_two d e) (rankDE_le_two d0 d1) ?_
  by_cases hc : w = Q.length
  · right
    refine ⟨hc, hrank ?_⟩
    exact (blockRoot_window_eq_iff hQne hd he hk hr0 hp).mp (by rw [← hw]; exact hc)
  · left; omega

/-! ### 203.1 ⟹ 整礎帰納は `Nat.strong_induction_on` **1 つ**で済みます

**⟹ ★ H12 に振った `Prod.Lex` の整礎性は**不要**になりました。**

⚠ **教訓（私の失敗）:** **振る前に「第 2 成分は有界か」を見る。**
**有界なら辞書式は要りません。`rankDE ≤ 2` は §198 で**私が**証明していました。** -/

/-! ## 204. ★★★★★★★★ 測度による強帰納の**骨組み** —— 残る義務が **1 本**になります

§200-§203 で「1 段で測度が減る」はそろいました。**それを `W` の membership に繋ぎます。**

**⟹ ★ 骨組みは `W` の中身にも `mTower` の中身にも依りません。書けるのは:**

> **「前提 `P` を満たす対象は、`P` を満たし測度の小さい対象がすべて片づいていれば、片づく」**
> **⟹ ⟹ ならば `P` を満たす対象はすべて片づく。**

**これは `Nat.strong_induction_on` そのものです。⟹ §203 で `Prod.Lex` を捨てたので `ℕ` 1 本。** -/

theorem tower_of_measure_step {u : ℕ}
    (P : TrioSeq → ℕ → ℕ → Prop) (meas : TrioSeq → ℕ → ℕ → ℕ)
    (hstep : ∀ Q d e, P Q d e →
      (∀ V d0 d1, P V d0 d1 → meas V d0 d1 < meas Q d e →
        ∀ A, A ∈ W u → ∀ m, A ++ mTower V d0 d1 m ∈ W u) →
      ∀ A, A ∈ W u → ∀ n, A ++ mTower Q d e n ∈ W u) :
    ∀ Q d e, P Q d e → ∀ A, A ∈ W u → ∀ n, A ++ mTower Q d e n ∈ W u := by
  have key : ∀ s Q d e, meas Q d e ≤ s → P Q d e →
      ∀ A, A ∈ W u → ∀ n, A ++ mTower Q d e n ∈ W u := by
    intro s
    induction s with
    | zero =>
      intro Q d e hle hP A hA n
      exact hstep Q d e hP
        (fun _ _ _ _ hlt _ _ _ => absurd hlt (by omega)) A hA n
    | succ s ih =>
      intro Q d e hle hP A hA n
      exact hstep Q d e hP
        (fun V d0 d1 hPV hlt A' hA' m => ih V d0 d1 (by omega) hPV A' hA' m) A hA n
  intro Q d e hP A hA n
  exact key (meas Q d e) Q d e (le_refl _) hP A hA n

/-! ### 204.1 ⟹ ★ **残る義務が `hstep` 1 本になりました**

`tower_of_measure_step` に

    `meas Q d e := natMeasure Q.length (rankDE d e) = 3 * |Q| + rankDE d e`（§203）
    `P Q d e := `（§201 の前提の束）

を入れると、証明すべきは **`hstep` だけ**です。そしてその中身は:

    **`mem_of_oper_mem`** で `∀ m ≥ 1, S⟦m⟧ ∈ W u` に落とす
    **§201** で `j ≥ 1` の親の位置（`≥ (A ++ mTower).length`）を得る（**錐の条件なし**）
    **§202** で `S⟦m⟧ = (A ++ mTower Q d e n ++ B.take p) ++ mTower V d0 d1 m`、`|V| = j − p`
    **§203** で測度が減ることを言う
    **帰納法の仮定**を `V d0 d1` に当てる

⚠⚠ **そのとき `P V d0 d1` が要ります。⟹ ★ これが**唯一残る穴**です（＝ 核）。**

### 204.2 ★ そして `j = 0` は**場合分けではありません**（今日わかったこと）

§202 は `P` と `B` について**完全に一般**です。`j = 0` の段は

    `S = A ++ mTower Q d e n ++ B.take 1`
      `= (A ++ mTower Q d e (n−1)) ++ (第 (n−1) ブロック ++ B).take (|Q| + 1)`

と読み替えれば、**`P' := A ++ mTower Q d e (n−1)`、`j' := |Q|`、`p := p_rel`** で
**同じ §202** が使えます。⟹ `|V| = |Q| − p_rel`。

> **⟹ ★ ⟹ `j = 0` と `j ≥ 1` は「§202 の同じ 1 本」の**別の引数**です。**
> **⟹ ⟹ 分かれるのは「`|V|` がいくつか」だけ:**
>
>     `j ≥ 1`                  ⟹ `|V| = j − p ≤ j < |Q|`  … **必ず減る**
>     `j = 0` かつ `p_rel ≥ 1` ⟹ `|V| = |Q| − p_rel < |Q|` … **減る**
>     `j = 0` かつ `p_rel = 0` ⟹ `|V| = |Q|`（減らない）  … **`rankDE` が減る**（§200）

⚠ **team-lead に「排中律つきの尽くしが要る」と書きましたが、**言い過ぎでした**。**
**⟹ §202 が一般なので、尽くす必要があるのは「`p` の値」だけです。⟹ `p < j` は
`nextR_index_lt`（親 < 子）から**ただで**出ます。**

⚠ **ただし `j = 0` の読み替え（`mTower_append` ＋ `take` の付け替え）は
**Lean ではまだ書いていません**。⟹ そこは残っています。 -/

/-! ## 205. ★★★★★★ `j = 0` の読み替え —— **1 ブロック手前から見る**

§204.2 で書いた読み替えを Lean にします。**これで `j = 0` の段も §202 の引数になります。**

    `mTower Q d e (n+1) ++ block_{n+1}.take j`
      `= mTower Q d e n ++ (block_n ++ block_{n+1}).take (|Q| + j)`

**⟹ 左辺の `j = 0` は、右辺では `j' = |Q|`（`≥ 1`）です。**
**⟹ ⟹ ★ 「`j = 0` だから親が前のブロック」という**例外**が、
「`j' = |Q|` で親が同じ `B'` の中」という**通常の場合**になります。** -/

theorem mTower_take_reassoc (Q : TrioSeq) (d e n j : ℕ) :
    mTower Q d e (n + 1) ++ (Lift1 (shiftr01 (d * (n + 1)) 0 Q) (e * (n + 1))).take j
      = mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)
            ++ Lift1 (shiftr01 (d * (n + 1)) 0 Q) (e * (n + 1))).take (Q.length + j) := by
  have hlen : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length = Q.length := by
    rw [Lift1_length, shiftr01_length]
  have hfull : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (Q.length + j)
      = Lift1 (shiftr01 (d * n) 0 Q) (e * n) :=
    List.take_of_length_le (by omega)
  rw [mTower_succ, List.append_assoc]
  congr 1
  rw [List.take_append, hfull, hlen, Nat.add_sub_cancel_left]

/-- 接頭辞つきの形（消費側がそのまま使えるもの）。 -/
theorem prefix_mTower_take_reassoc (A Q : TrioSeq) (d e n j : ℕ) :
    A ++ mTower Q d e (n + 1)
      ++ (Lift1 (shiftr01 (d * (n + 1)) 0 Q) (e * (n + 1))).take j
      = A ++ (mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)
            ++ Lift1 (shiftr01 (d * (n + 1)) 0 Q) (e * (n + 1))).take (Q.length + j)) := by
  rw [List.append_assoc, mTower_take_reassoc]

/-! ### 205.1 ⟹ ★ これで **§202 の `p < j` が `j = 0` でも意味を持ちます**

読み替えたあと `j' = |Q| + 0 = |Q| ≥ 1` なので、`p < j'` は
`nextR_index_lt`（親 < 子）から**ただで**出ます。

    親 `= (A ++ mTower Q d e n).length + p_rel`、`p_rel < |Q| = j'` ✓

**⟹ §202 が使えて `|V| = j' − p_rel = |Q| − p_rel`。§204.2 の表のとおりです。**

⚠ **ただし「親が `(A ++ mTower Q d e n).length` 以上」（＝ 1 ブロック手前で止まる）は
この補題からは出ません。⟹ それは H12 の `blockRoot_parent_prevBlock` です。**
**⟹ ⟹ そちらは `0 < d`・`0 < e`・`hr0` が要ります。** -/

/-! ## 206. ★★★★★★★★★ **総組み立て** —— 残る義務を **`hsnoc` 1 本**に絞る

§204 の骨組みに §201 を差し込みます。**そのために前提の束を述語 1 つにまとめます。**

⚠ **§201 は `M` について述べていて、塔の底は `M.dropLast` です。**
**⟹ `tower_of_measure_step` の `P` は `(Q, d, e)` だけの述語でないといけません。**
**⟹ ⟹ `M` を**存在量化**して逃がします。** -/

/-- ★ §201 `prefixTowerClosed_final_noCone` の前提の束（`M` は存在量化）。 -/
def TowerP (Q : TrioSeq) (d e : ℕ) : Prop :=
  ∃ M : TrioSeq, M.dropLast = Q ∧ 2 ≤ M.length ∧ 0 < e ∧
    entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d ∧
    (∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l) ∧
    le1 M 0 (0 + M.dropLast.length) ∧
    entry M.dropLast 0 0 = 0 ∧ entry M.dropLast 2 0 = 0

/-- ★ 測度（§203 のもの）。 -/
def towerMeas (Q : TrioSeq) (d e : ℕ) : ℕ := natMeasure Q.length (rankDE d e)

open Classical in
/-- ★★★★★ **総組み立て**: 「1 段の snoc」だけ示せば、族全体が `W u` に入る。

**残る義務は `hsnoc` 1 本です。**そしてその引数はすべてそろっています:

    `TowerP Q d e`  … 前提の束
    **帰納法の仮定** … 測度の小さい `(V, d0, d1)` は片づいている
    `A ∈ W u` / `j < |Q|` / **親の位置**（`j ≥ 1`、**錐の条件なし**）/ 短い接頭辞は全部 `W u` -/
theorem towerClosed_of_snoc {u : ℕ}
    (hsnoc : ∀ (Q : TrioSeq) (d e : ℕ), TowerP Q d e →
      (∀ V d0 d1, TowerP V d0 d1 → towerMeas V d0 d1 < towerMeas Q d e →
        ∀ A, A ∈ W u → ∀ m, A ++ mTower V d0 d1 m ∈ W u) →
      ∀ (A : TrioSeq), A ∈ W u → ∀ (n j : ℕ), j < Q.length →
        (0 < j →
          hasParent (A ++ mTower Q d e n
              ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
            (srow (A ++ mTower Q d e n
              ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
              (A ++ mTower Q d e n
                ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length)
            (A ++ mTower Q d e n
              ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length →
          (A ++ mTower Q d e n).length ≤
            parent (A ++ mTower Q d e n
                ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
              (srow (A ++ mTower Q d e n
                ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
                (A ++ mTower Q d e n
                  ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length)
              (A ++ mTower Q d e n
                ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length) →
        (∀ j', j' ≤ j →
          A ++ mTower Q d e n
            ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j' ∈ W u) →
        A ++ mTower Q d e n
          ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1) ∈ W u) :
    ∀ Q d e, TowerP Q d e → ∀ A, A ∈ W u → ∀ n, A ++ mTower Q d e n ∈ W u := by
  refine tower_of_measure_step (u := u) TowerP towerMeas ?_
  intro Q d e hP hIH A hA n
  obtain ⟨M, hMQ, hM2, he, hd0e, hr0M, hlp, hbase, hz0⟩ := hP
  subst hMQ
  refine prefixTowerClosed_final_noCone hA hM2 he hd0e hr0M hlp hbase hz0 ?_ n
  intro n' j hj hpar hall
  exact hsnoc M.dropLast d e
    ⟨M, rfl, hM2, he, hd0e, hr0M, hlp, hbase, hz0⟩ hIH A hA n' j hj hpar hall

/-! ### 206.1 ⟹ ★ ここまでで**何が残っているか**が定理の文になりました

**`hsnoc` の証明の道筋（材料は全部緑です）:**

    **1.** `Wchar.mem_of_oper_mem`（`|S| ≥ 2`）で `∀ m ≥ 1, S⟦m⟧ ∈ W u` に落とす
    **2.** `j = 0` なら §205 `mTower_take_reassoc` で `j' = |Q|` に読み替える
    **3.** 親の位置を得る（`j ≥ 1` は `hpar` の前提から、`j = 0` は H12 `blockRoot_parent_prevBlock`）
    **4.** §202 `snocStep_oper_pre` で `S⟦m⟧ = (接頭辞) ++ mTower V d0 d1 m`、`|V| = j − p`
    **5.** 接頭辞が `W u` に入るのは `hall`（`p < j` なので射程内）
    **6.** §203 `natMeasure_lt` ＋ §200 `rankDE_lt_of_blockRoot_parent` で測度が減る
    **7.** **帰納法の仮定 `hIH` を当てる**

⚠⚠ **7 で `TowerP V d0 d1` が要ります。⟹ ★ これが**唯一残る穴**です。**

**`TowerP V d0 d1` を開くと、`V` の上の 4 つ（＋ `M'` の存在）:**

    **`hr0(V)`**  … `V` の行 0 が根から狭義単調
    **`hz0(V)`**  … `entry V 2 0 = 0`（既知の (H2')）
    **`hd0e(V)`** … `V` の末尾列の行 0 が「根 ＋ `d0`」
    **`hlp(V)`**  … `le1 V 0 (末尾)`

⚠ **教訓 14**: **`towerClosed_of_snoc` は「`hsnoc` ならば族が閉じる」しか言っていません。**
**`hsnoc` が真であることは示していません。⟹ `hsnoc` は**まだ証明されていません**。** -/

/-! ## 207. ⛔⛔⛔ **`hbase` は遺伝しません** —— `TowerP` の 7 本を全部監査しました

§206 で `TowerP` を作りましたが、**それが本当に使えるかを確かめていませんでした**（14 回目の轍）。
**⟹ 目標 `MTowerClosedS`（`L105Cap:5618`）が渡すのは 2 つだけです:**

    `Q ∈ W u` ／ `∀ j, 1 ≤ j → j < |Q| → entry Q 0 0 < entry Q 0 j`

**⟹ ★ `TowerP` の 7 本を 1 本ずつ監査しました:**

    **1. `2 ≤ |M|`（⟺ `1 ≤ |Q|`）** … ✅ ただ（`|Q| ≤ 1` は §81 `mTowerSingle_holds`、緑）
    **2. `0 < e`** … ⚠ `e = 0` は §112 `MTowerClosedS0 = ShiftTowerClosedS` ⟹ **別ルートで既知**
    **3. `hd0e`** … ✅ ただ（`M := Q ++ [c]` の `c` を**こちらが選べる**。`c.0 := entry Q 0 0 + d`）
    **4. `hr0M`（`l = |Q|` の分）** … ⚠ `entry Q 0 0 < entry Q 0 0 + d` ⟹ **`0 < d` が要る**
    **5. `hlp : le1 M 0 |Q|`** … ⛔ `c` の選び方に強い制約。**穴**
    **6. `hbase : entry Q 0 0 = 0`** … ⛔ 一般の `Q ∈ W u` では成りません。**穴**
    **7. `hz0 : entry Q 2 0 = 0`** … ⛔ team-lead 済み（`z = 1` で破れる）。**穴**

### 207.1 ⛔⛔ そして **6 は遺伝しません**。下で**証明します**（測定ではありません）

§202 の窓は `V = (T.drop (P.length + p)).take (j − p)` なので、

    **`entry V 0 0 = entry T 0 (P.length + p)`**（`entry_window`、下）

塔の場合 `P.length = n*|Q|` で `entry T 0 (n*|Q| + p) = entry Q 0 p + d*n`。
**⟹ `hr0` があれば `p ≥ 1` で `entry Q 0 0 < entry Q 0 p`。**

> **⟹ ★ `hbase(Q)`（`= 0`）を仮定すると、`p ≥ 1` の窓では `entry V 0 0 > 0`。**
> **⟹ ⟹ ⛔ **`hbase(V)` は偽**。**

⚠ **これは残差ではありません。`p ≥ 1` の段では**必ず**破れます。** -/

theorem entry_window (T : TrioSeq) {s L i t : ℕ} (ht : t < L) :
    entry ((T.drop s).take L) i t = entry T i (s + t) := by
  unfold entry
  rw [getD_take_drop ht]

/-- ★ 塔の中の窓の根の行 0（`p` 列目の値 ＋ 第 `n` ブロックのリフト）。 -/
theorem window_root_entry0 {Q : TrioSeq} {d e n j p : ℕ}
    (hjQ : j < Q.length) (hpj : p < j) :
    entry (((mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).drop
        (n * Q.length + p)).take (j - p)) 0 0
      = entry Q 0 p + d * n := by
  rw [entry_window _ (show 0 < j - p by omega),
    show n * Q.length + p + 0 = (mTower Q d e n).length + p from by
      rw [mTower_length]; omega,
    entry_append_right, Wset.entry_take (show p < j + 1 by omega), entry0_Lift1,
    entry0_shiftr01 (by omega)]

/-- ⛔⛔ **`hbase` は遺伝しません**: `p ≥ 1` の窓の根は行 0 が**正**。 -/
theorem window_root_entry0_pos {Q : TrioSeq} {d e n j p : ℕ}
    (hjQ : j < Q.length) (hp1 : 0 < p) (hpj : p < j)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hbase : entry Q 0 0 = 0) :
    0 < entry (((mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).drop
        (n * Q.length + p)).take (j - p)) 0 0 := by
  rw [window_root_entry0 hjQ hpj]
  have := hr0 p hp1 (by omega)
  omega

/-! ### 207.2 ⟹ ★ **これは `hbase` を消せという指示です**（設計の変更、核ではありません）

`hbase` は H12 の窓補題の中で **1 か所**にしか使われていません（`L106:704`）:

    `hroot : entry T 0 0 = 0` ⟹ `Column.hasParent_append_right` / `parent_append_right`
    （接頭辞 `A` を剥がして「親は塔の中」に落とすため）

**⟹ ★ 直し方の候補は 2 つです:**

    **(a)** `hasParent_append_right` の `hroot` を**弱める**
         （「根の行 0 が最小」など、**平行移動で不変**な条件に）
    **(b)** `Wset.nextR_src_ge`（`:2573`、**前提なし・行に依らない**）で剥がす
         ⚠ ただし `nextR_src_ge` は「塔の中に既に親がいる」を要求するので、
           `hasParent (A ++ T) → hasParent T` の向きには**そのままでは使えません**

**⟹ ⟹ (a) が本命です。`hbase` を `∀ l < |T|, entry T 0 0 ≤ entry T 0 l` に弱められれば、
それは `hr0` の弱い形なので**遺伝の見込みがあります**。**

### 207.3 ⚠ 私の失敗（14 回目と同じ）

**§206 で `TowerP` を作ったとき、「消費側が渡せるか」を確かめていませんでした。**
**⟹ 作ってから 30 分で自分で見つけましたが、順序が逆です。**
**⟹ ⟹ ★ **前提の束を定義したら、その場で消費側と突き合わせる**。** -/

/-! ## 208. ★★★★★★★★★ **`hbase` は消せます** —— 剥がすのをやめて、**下から積む**

§207 で `hbase` が遺伝しないと分かりました。**⟹ 索引を引いたら、直し方が既にありました。**

    **`Wset.hasParent_append_right_of`**（`:2604`、**前提なし**）… `hasParent T → hasParent (A ++ T)`
    **`Xbar.parent_append_right_of`**（`:34`、**前提なし**）… `parent (A ++ T) i (|A| + j) = |A| + parent T i j`

**⟹ ★ どちらも `hroot`（`entry T 0 0 = 0`）を**要求しません**。**

## なぜ `hbase` が要っていたか（向きの問題でした）

    `hasParent_append_right`（`Column:363`）… **`hasParent (A ++ T) ↔ hasParent T`**、`hroot` **要る**
    `hasParent_append_right_of`（`Wset:2604`）… **`hasParent T → hasParent (A ++ T)`**、`hroot` **要らない**

**⟹ ⟹ ★ `hroot` が要るのは**難しいほうの向き**（`A ++ T` から `T` へ**剥がす**）だけです。**
**⟹ ⟹ ⟹ 逆向き（`T` から `A ++ T` へ**積む**）は**ただ**です。**

> **⟹ ★★ ならば消費側に「塔の中の親」`hasParent T` を出させればよい。**
> **⟹ ⟹ そうすれば `hbase` は**一度も要りません**。**

⚠ **値段は正直に書きます: 前提が `hasParent (A ++ T)` から `hasParent T` に**強く**なります。**
**⟹ ですが `hasParent T → hasParent (A ++ T)` はただなので、消費側が損することはありません。** -/

open Classical in
/-- ★★★★ **`hbase` なしの接頭辞つき窓補題**。
前提は「**塔の中**の親」（`hasParent T`）で、`entry Q 0 0 = 0` は**要りません**。 -/
theorem prefix_window_of_outOfCone_noBase {A M : TrioSeq} {d e n j : ℕ}
    (hM2 : 2 ≤ M.length) (hd1pos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hj : j < M.dropLast.length) (hj1 : 0 < j)
    (hout : ¬ le1 M 0 (0 + j))
    (hpT : hasParent (mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
      (srow (mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
        (n * M.dropLast.length + j))
      (n * M.dropLast.length + j)) :
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
  have hTlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have hAT : (A ++ mTower Q d e n).length = A.length + n * Q.length := by
    rw [List.length_append, hTlen]
  have hassoc : A ++ mTower Q d e n
      ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1) = A ++ T := by
    rw [hT, List.append_assoc]
  have hpos' : (A ++ mTower Q d e n).length + j = A.length + (n * Q.length + j) := by
    rw [hAT]; omega
  rw [hassoc, hpos']
  have hsrow : srow (A ++ T) (A.length + (n * Q.length + j))
      = srow T (n * Q.length + j) := srow_append_right A T (n * Q.length + j)
  rw [hsrow]
  rw [parent_append_right_of A T hpT, hAT]
  have hcore := window_of_outOfCone_all (M := M) (d := d) (e := e) (n := n) (j := j)
    hM2 hd1pos hd0e hr0 hlp hj hj1 hout hpT
  rw [← hQ, ← hT] at hcore
  omega

/-! ### 208.1 ⟹ ★ `TowerP` から `hbase` が落ちます

**⟹ 残る穴は 2 本になりました:**

    **`hlp(V) = le1 V 0 (|V|−1)`** … 窓の根から末尾へ行 1 で到達
    **`hz0(V) = entry V 2 0 = 0`** … 既知の (H2')

⚠⚠ **ただし値段があります。逐語で書きます:**

**`hstep` が受け取る親の前提が `hasParent (A ++ T)` から `hasParent T`（塔の中）に変わります。**

**⟹ 消費側は `hasParent T` を出さないといけません。⟹ ★ その出どころは:**

    **錐の中** … `block_blockParent_all_cone`（ブロックの中）＋ `hasParent_append_right_of`（ただ）
    **錐の外** … ⛔ **まだありません**

**⟹ ⟹ ★ ⟹ `hbase` の穴が「錐の外で `hasParent` をブロックの中に出す」に**変わりました**。**
**⟹ これは §172 `block_blockParent_row1_outcone`（緑）が部分的に答えています。**

⚠ **教訓 14**: **`prefix_window_of_outOfCone_noBase` は緑ですが、
その `hpT` を**誰が出すのか**はまだ決まっていません。⟹ 穴が移動しただけかもしれません。** -/

/-! ## 209. ★★★★★★★ `hbase` を落とした `hstep`（§201 の差し替え）

§208 を §201 に差し込みます。**⟹ `hbase` が前提から消えます。**

⚠ **`prefixTowerClosed_final`（§169、`L105Cap:12118`）自体は `hbase` を持っていません。**
**⟹ `hbase` は H12 の錐の外の補題**だけ**から来ていました。⟹ そこを §208 に替えれば落ちます。**

⚠ **値段**: `hstep` が受け取る親の前提が **`hasParent T`（塔の中）**になります。
**⟹ `hasParent T → hasParent (A ++ T)` はただ（`Wset.hasParent_append_right_of`）なので、
消費側は損しません。** -/

open Classical in
theorem prefixTowerClosed_final_noBase {u : ℕ} {A M : TrioSeq} {d e : ℕ}
    (hA : A ∈ W u) (hM2 : 2 ≤ M.length) (he : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0M : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hz0 : entry M.dropLast 2 0 = 0)
    (hstep : ∀ (n j : ℕ), j < M.dropLast.length →
      (0 < j →
        hasParent (mTower M.dropLast d e n
            ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
          (srow (mTower M.dropLast d e n
              ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
            (n * M.dropLast.length + j))
          (n * M.dropLast.length + j) →
        (A ++ mTower M.dropLast d e n).length ≤
          parent (A ++ mTower M.dropLast d e n
              ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
            (srow (A ++ mTower M.dropLast d e n
              ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
              (A ++ mTower M.dropLast d e n
                ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length)
            (A ++ mTower M.dropLast d e n
              ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length) →
      (∀ j', j' ≤ j →
        A ++ mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j' ∈ W u) →
      A ++ mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1) ∈ W u) :
    ∀ n, A ++ mTower M.dropLast d e n ∈ W u := by
  have hdl : M.dropLast.length = M.length - 1 := List.length_dropLast
  have hr0Q : ∀ l, 0 < l → l < M.dropLast.length →
      entry M.dropLast 0 0 < entry M.dropLast 0 l := by
    intro l hl0 hl1
    rw [hdl] at hl1
    rw [List.dropLast_eq_take, Wset.entry_take (show (0 : ℕ) < M.length - 1 by omega),
      Wset.entry_take hl1]
    exact hr0M l hl0 (by omega)
  refine prefixTowerClosed_final hA hr0Q hz0 ?_
  intro n j hj hcone hall
  refine hstep n j hj (fun hj1 hpT => ?_) hall
  by_cases hc : le1 M 0 (0 + j)
  · refine hcone hj1 ?_
    rw [List.dropLast_eq_take]
    refine (Wset.le1_take (X := M) (l := M.length - 1) (a := 0) (b := j)
      (by omega) (by rw [hdl] at hj; omega)).mpr ?_
    simpa using hc
  · rw [prefixTake_length A M.dropLast d e n j hj]
    exact prefix_window_of_outOfCone_noBase hM2 he hd0e hr0M hlp hj hj1 hc hpT

/-! ### 209.1 ⟹ `TowerP` から `hbase` を落とした版 -/

/-- ★ §209 の前提の束（`hbase` なし）。 -/
def TowerP' (Q : TrioSeq) (d e : ℕ) : Prop :=
  ∃ M : TrioSeq, M.dropLast = Q ∧ 2 ≤ M.length ∧ 0 < e ∧
    entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d ∧
    (∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l) ∧
    le1 M 0 (0 + M.dropLast.length) ∧
    entry M.dropLast 2 0 = 0

open Classical in
/-- ★★★★★ **総組み立て（`hbase` なし）**。残る義務は `hsnoc` 1 本。 -/
theorem towerClosed_of_snoc' {u : ℕ}
    (hsnoc : ∀ (Q : TrioSeq) (d e : ℕ), TowerP' Q d e →
      (∀ V d0 d1, TowerP' V d0 d1 → towerMeas V d0 d1 < towerMeas Q d e →
        ∀ A, A ∈ W u → ∀ m, A ++ mTower V d0 d1 m ∈ W u) →
      ∀ (A : TrioSeq), A ∈ W u → ∀ (n j : ℕ), j < Q.length →
        (0 < j →
          hasParent (mTower Q d e n
              ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
            (srow (mTower Q d e n
                ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
              (n * Q.length + j))
            (n * Q.length + j) →
          (A ++ mTower Q d e n).length ≤
            parent (A ++ mTower Q d e n
                ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
              (srow (A ++ mTower Q d e n
                ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
                (A ++ mTower Q d e n
                  ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length)
              (A ++ mTower Q d e n
                ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length) →
        (∀ j', j' ≤ j →
          A ++ mTower Q d e n
            ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j' ∈ W u) →
        A ++ mTower Q d e n
          ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1) ∈ W u) :
    ∀ Q d e, TowerP' Q d e → ∀ A, A ∈ W u → ∀ n, A ++ mTower Q d e n ∈ W u := by
  refine tower_of_measure_step (u := u) TowerP' towerMeas ?_
  intro Q d e hP hIH A hA n
  obtain ⟨M, hMQ, hM2, he, hd0e, hr0M, hlp, hz0⟩ := hP
  subst hMQ
  refine prefixTowerClosed_final_noBase hA hM2 he hd0e hr0M hlp hz0 ?_ n
  intro n' j hj hpar hall
  exact hsnoc M.dropLast d e
    ⟨M, rfl, hM2, he, hd0e, hr0M, hlp, hz0⟩ hIH A hA n' j hj hpar hall

/-! ### 209.2 ⟹ ★ 残る穴は **2 本 ＋ 1 本**

    ⛔ **`hlp(V)`** … 窓の根から末尾へ行 1 で到達（`TowerP'` の中）
    ⛔ **`hz0(V)`** … `entry V 2 0 = 0`（既知の (H2')）
    ⛔ **`hpT`（錐の外）** … 錐の外の列が**自分のブロックの中**に親を持つ（§208 で移動した穴）

⚠ **`hpT` は「穴が減った」のではなく「置き換わった」ものです。**
**⟹ ですが `hbase` は**必ず**破れました（§207、証明済み）。`hpT` は破れると決まっていません。**
**⟹ ⟹ ★ H12 の実測では「錐の外 ＝ 行 2 の孤児」が 98.8〜100%。⟹ 見込みはあります。** -/

/-! ## 210. ★★★★★★★ §208 で移動した穴を**名前つきの 1 本**に詰めました

§208/§209 で `hpT`（**塔の中**の親）が要るようになりました。**出どころを作ります。**

**索引を引きました（手筋）。ブロックの中の親は**行ごとに**そろっています:**

    **行 0** … §154 `block_blockParent_row0`（`hr0` だけ。**錐の条件なし**）✅
    **行 2** … §173 `block_hasParent_row2_iff`（`Q.take (j+1)` に落ちる。**無条件**）✅
    **行 1・錐の外** … §172 `block_blockParent_row1_outcone`
              ⚠ **`hhigh : entry Q 1 0 < entry Q 1 j` が要る**

**⟹ ★ ⟹ 残るのは 1 つだけです: **`0 < entry Q 1 j` かつ `entry Q 1 j ≤ entry Q 1 0`**。**
**⟹ ⟹ これが「ブロッカー」（非根で行 1 が根以下の列）そのものです（§162.2 の語彙）。** -/

theorem block_blockParent_all_outcone {Q : TrioSeq} {d e n j : ℕ}
    (hj : j < Q.length) (hj1 : 0 < j)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hout : ¬ le1 Q 0 j)
    (h2 : 0 < entry Q 2 j → hasParent (Q.take (j + 1)) 2 j)
    (h1 : 0 < entry Q 1 j → entry Q 1 0 < entry Q 1 j) :
    hasParent ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (srow ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) j) j := by
  set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
  have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
  have hE1 : entry (B.take (j + 1)) 1 j
      = entry Q 1 j + (if le1 Q 0 j then e * n else 0) := by
    rw [Wset.entry_take (X := B) (l := j + 1) (i := 1) (j := j) (by omega)]
    show (B.getD j (0, 0, 0)).2.1 = _
    rw [hB, block_getD hj]
  have hE2 : entry (B.take (j + 1)) 2 j = entry Q 2 j := by
    rw [hB, entry2_block_take (by omega),
      Wset.entry_take (X := Q) (l := j + 1) (i := 2) (j := j) (by omega)]
  unfold srow
  by_cases h2p : 0 < entry (B.take (j + 1)) 2 j
  · rw [if_pos h2p]
    rw [hE2] at h2p
    exact block_blockParent_row2' hj (h2 h2p)
  · by_cases h1p : 0 < entry (B.take (j + 1)) 1 j
    · rw [if_neg h2p, if_pos h1p]
      rw [hE1, if_neg hout, Nat.add_zero] at h1p
      exact block_blockParent_row1_outcone hj hr0 hout (h1 h1p)
    · rw [if_neg h2p, if_neg h1p]
      exact block_blockParent_row0 hj hj1 hr0

/-! ### 210.1 ★ ブロックの中の親を**塔の中**へ持ち上げる（**前提なし**） -/

theorem tower_hasParent_of_block {Q : TrioSeq} {d e n j : ℕ}
    (hloc : hasParent ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (srow ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) j) j) :
    hasParent (mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (srow (mTower Q d e n
          ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        (n * Q.length + j))
      (n * Q.length + j) := by
  have hTlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have hsrow : srow (mTower Q d e n
      ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) (n * Q.length + j)
      = srow ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) j := by
    rw [show n * Q.length + j = (mTower Q d e n).length + j from by rw [hTlen]]
    exact srow_append_right _ _ j
  rw [hsrow, show n * Q.length + j = (mTower Q d e n).length + j from by rw [hTlen]]
  exact hasParent_append_right_of _ _ hloc

/-! ### 210.2 ⟹ ★★ **`hpT` は「ブロッカー」1 本に詰まりました**

**§210 ＋ §210.1 を合わせると、`j ≥ 1` の**錐の外**の列について `hpT` が出ます。前提は:**

    `hr0`（消費側が渡す）
    **`h2`** … `0 < entry Q 2 j → hasParent (Q.take (j+1)) 2 j`（**行 2 の孤児でない**）
    **`h1`** … `0 < entry Q 1 j → entry Q 1 0 < entry Q 1 j`（**ブロッカーでない**）

⚠ **`h1` と `h2` はどちらも `Q` **だけ**についての条件です。塔にも接頭辞にも依りません。**
**⟹ ★ ⟹ だから `TowerP'` に足せます。⟹ ⟹ 問題は**遺伝するか**だけになります。**

⚠⚠ **教訓 27**: **`h1` は `Q` の**すべての**`j` について要るわけではありません。**
**「錐の外で `srow = 1` の `j`」だけです。⟹ 分母を小さく取れます。**

### 210.3 ⟹ H12 の実測との突き合わせ

> **H12 (C2)**: 「錐の外 ＝ 行 2 の孤児」は **98.8〜100%**、100% ではない。

**⟹ ★ これは `h2` の残差（`0 < entry Q 2 j` なのに `Q.take (j+1)` の中に行 2 の親がいない）です。**
**⟹ ⟹ そして「錐の外 ＝ 行 2 の孤児」が成り立つとき、`srow = 2` なので **`h1` は空**になります。**
**⟹ ⟹ ⟹ つまり `h1` の分母は**その 0〜1.2%**の中にあります。⟹ **小さいはずです**。**

⚠ **教訓 14**: 上は**私の読み**です。H12 に確かめてもらいます。 -/

/-! ## 211. ★★★★★★★★★ **親の位置の前提が完全に消えます**（`hstep` の最終形）

§209 は `hstep` に `0 < j → **`hasParent T`** → 親 ≥ …` を渡していました。
**⟹ §210 で `hasParent T` が（`Q` だけの 2 条件のもとで）出るようになりました。**
**⟹ ⟹ ★ だから `hstep` に渡すのは **`0 < j → 親 ≥ …`** だけでよい。**

**加わる前提は 2 本、どちらも `Q` **だけ**の条件です:**

    **`h2out`** … 錐の外で行 2 が正なら、`Q.take (j+1)` の中に行 2 の親がいる
    **`h1out`** … 錐の外で行 1 が正なら、根より行 1 が高い（＝ **ブロッカーでない**）

⚠ **どちらも「`j ≥ 1` かつ**錐の外**の `j`」についてだけです（教訓 27、分母は小さい）。** -/

open Classical in
theorem prefixTowerClosed_final_full {u : ℕ} {A M : TrioSeq} {d e : ℕ}
    (hA : A ∈ W u) (hM2 : 2 ≤ M.length) (he : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0M : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hz0 : entry M.dropLast 2 0 = 0)
    (h2out : ∀ j, 0 < j → j < M.dropLast.length → ¬ le1 M.dropLast 0 j →
      0 < entry M.dropLast 2 j → hasParent (M.dropLast.take (j + 1)) 2 j)
    (h1out : ∀ j, 0 < j → j < M.dropLast.length → ¬ le1 M.dropLast 0 j →
      0 < entry M.dropLast 1 j → entry M.dropLast 1 0 < entry M.dropLast 1 j)
    (hstep : ∀ (n j : ℕ), j < M.dropLast.length →
      (0 < j →
        (A ++ mTower M.dropLast d e n).length ≤
          parent (A ++ mTower M.dropLast d e n
              ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
            (srow (A ++ mTower M.dropLast d e n
              ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
              (A ++ mTower M.dropLast d e n
                ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length)
            (A ++ mTower M.dropLast d e n
              ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length) →
      (∀ j', j' ≤ j →
        A ++ mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j' ∈ W u) →
      A ++ mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1) ∈ W u) :
    ∀ n, A ++ mTower M.dropLast d e n ∈ W u := by
  have hdl : M.dropLast.length = M.length - 1 := List.length_dropLast
  have hr0Q : ∀ l, 0 < l → l < M.dropLast.length →
      entry M.dropLast 0 0 < entry M.dropLast 0 l := by
    intro l hl0 hl1
    rw [hdl] at hl1
    rw [List.dropLast_eq_take, Wset.entry_take (show (0 : ℕ) < M.length - 1 by omega),
      Wset.entry_take hl1]
    exact hr0M l hl0 (by omega)
  refine prefixTowerClosed_final_noBase hA hM2 he hd0e hr0M hlp hz0 ?_
  intro n j hj hp hall
  refine hstep n j hj (fun hj1 => ?_) hall
  refine hp hj1 ?_
  -- ★ `hpT` を作る
  by_cases hc : le1 M.dropLast 0 j
  · -- 錐の中: §163 `block_blockParent_all_cone` ＋ §162.9 `h2_cone`（H12 の 6 行）
    exact tower_hasParent_of_block (Q := M.dropLast) (d := d) (e := e) (n := n)
      (block_blockParent_all_cone hj hj1 hr0Q hc
        (fun hpos => h2_cone hz0 j hj1 hj hpos hc))
  · -- 錐の外: §210
    exact tower_hasParent_of_block (Q := M.dropLast) (d := d) (e := e) (n := n)
      (block_blockParent_all_outcone hj hj1 hr0Q hc
        (fun hpos => h2out j hj1 hj hc hpos)
        (fun hpos => h1out j hj1 hj hc hpos))

/-! ### 211.1 ⟹ ★★★ **`TowerP''`**: 遺伝させるべき条件が**これで全部**です

**⟹ ★ `hstep` に渡す親の位置の前提が**完全に消えました**。**
**⟹ ⟹ 残るのは「この 6 本が窓 `V` に遺伝するか」だけです。** -/

/-- ★★★ 遺伝させるべき条件の**最終形**（親の位置はもう前提に出てきません）。 -/
def TowerP'' (Q : TrioSeq) (_d _e : ℕ) : Prop :=
  0 < Q.length ∧
    (∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) ∧
    (∀ q, q < Q.length → entry Q 2 q ≤ 1)

/-! ### 211.2 ⟹ ★★ **`M` が消えました**（あとから分かったこと）

⚠ **最初は `M`（`Q` の 1 列長い版）を存在量化していました。**
**⟹ H12 の錐の外の窓補題（`hd0e` / `hlp` / `hbase` が要る）を使っていたからです。**

**⟹ ★ ですが §219 の `parent_bound_pos` は §167 `prefixSnocStep_parent_sameBlock` を使います。**
**⟹ ⟹ §167 は **`hloc`（ブロックの中の親）だけ**で、錐の条件も `hbase` も `hd0e` も `hlp` も
**要りません**。⟹ ⟹ ★ だから `M` ごと消せました。**

    ⛔ ~~`hd0e`~~ … `0 < d` に置き換え（`hd0e` ＋ `hr0M` が含意していたもの）
    ⛔ ~~`hlp`~~  … **一度も使っていませんでした**
    ⛔ ~~`hbase`~~ … §208 で消した

**⟹ ⟹ ★★ 遺伝が問題になるのは **3 本**です:**

    **`hz0`**   … `entry Q 2 0 = 0`（既知の (H2')）
    **`h2out`** … 錐の外で行 2 が正なら `Q.take (j+1)` に行 2 の親（**行 2 の孤児でない**）
    **`h1out`** … 錐の外で行 1 が正なら根より高い（**ブロッカーでない**）

**そして残り 4 本は遺伝が**易しい**はずです:**

    `0 < |Q|` / `0 < d` / `0 < e` / `hr0`（行 0 が根から狭義単調）

⚠ **教訓 14**: **「易しいはず」は**測っても証明してもいません**。**

⚠⚠ **そして H12 の錐の外の窓補題（`window_of_outOfCone_all` 系）は
**この道では使いません**。⟹ H12 に伝える必要があります。**
**⟹ 代わりに H12 の `blockRoot_parent_prevBlock` 系が §215 で効いています。** -/

/-! ## 212. ★★★★★★★ `hsnoc` の `j ≥ 1` の枝を組みます

§211 で親の位置は前提から消えました。**次は `hsnoc` そのものです。**

**⟹ まず §211 の中で作った `hpT` を、名前つきで外に出します（再利用のため）。** -/

theorem hr0_of_TowerP'' {Q : TrioSeq} {d e : ℕ} (hP : TowerP'' Q d e) :
    ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l := hP.2.1

/-- ★ `z < 2` の断片（行 2 ≤ 1）。**窓に遺伝します**（§224.5）。 -/
theorem hz1_of_TowerP'' {Q : TrioSeq} {d e : ℕ} (hP : TowerP'' Q d e) :
    ∀ q, q < Q.length → entry Q 2 q ≤ 1 := hP.2.2

theorem ne_of_TowerP'' {Q : TrioSeq} {d e : ℕ} (hP : TowerP'' Q d e) : Q ≠ [] :=
  List.ne_nil_of_length_pos hP.1

/-- ★ **錐の中の列**は `TowerP''` だけでブロックの中に親を持つ（§163 ＋ §162.9）。 -/
theorem block_hasParent_cone {Q : TrioSeq} {d e : ℕ} (n : ℕ)
    (hP : TowerP'' Q d e) (hz0 : entry Q 2 0 = 0)
    {j : ℕ} (hj : j < Q.length) (hj1 : 0 < j) (hc : le1 Q 0 j) :
    hasParent ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (srow ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) j) j :=
  block_blockParent_all_cone hj hj1 (hr0_of_TowerP'' hP) hc
    (fun hpos => h2_cone hz0 j hj1 hj hpos hc)

/-! ### 212.1 §202 を**存在量化なし**で書き直します（証人を名前で呼ぶため） -/

/-- 窓（§202 の明示の証人）。 -/
def wnd (P B : TrioSeq) (j p : ℕ) : TrioSeq :=
  ((P ++ B.take (j + 1)).drop (P.length + p)).take (j - p)

/-- 新しい行 0 のリフト量。 -/
noncomputable def wd0 (P B : TrioSeq) (j p : ℕ) : ℕ :=
  if 0 < srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1) then
    entry (P ++ B.take (j + 1)) 0 ((P ++ B.take (j + 1)).length - 1)
      - entry (P ++ B.take (j + 1)) 0 (P.length + p) else 0

/-- 新しい行 1 のリフト量。 -/
noncomputable def wd1 (P B : TrioSeq) (j p : ℕ) : ℕ :=
  if 1 < srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1) then
    entry (P ++ B.take (j + 1)) 1 ((P ++ B.take (j + 1)).length - 1)
      - entry (P ++ B.take (j + 1)) 1 (P.length + p) else 0

theorem wnd_length {P B : TrioSeq} {j p : ℕ}
    (hjB : j < B.length) (hpj : p < j) : (wnd P B j p).length = j - p := by
  have hTl : (P ++ B.take (j + 1)).length = P.length + (j + 1) := by
    rw [List.length_append, List.length_take, Nat.min_eq_left (by omega)]
  unfold wnd
  rw [List.length_take, List.length_drop, hTl]
  omega

open Classical in
/-- ★ §202 の**証人つき**の形。 -/
theorem snocStep_oper_pre_eq {P B : TrioSeq} {j p m : ℕ}
    (hjB : j < B.length) (hpj : p < j)
    (hz : ¬ (entry (P ++ B.take (j + 1)) 0 ((P ++ B.take (j + 1)).length - 1) = 0 ∧
      entry (P ++ B.take (j + 1)) 1 ((P ++ B.take (j + 1)).length - 1) = 0 ∧
      entry (P ++ B.take (j + 1)) 2 ((P ++ B.take (j + 1)).length - 1) = 0))
    (hpar : hasParent (P ++ B.take (j + 1))
      (srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1))
      ((P ++ B.take (j + 1)).length - 1))
    (hpe : parent (P ++ B.take (j + 1))
      (srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1))
      ((P ++ B.take (j + 1)).length - 1) = P.length + p) :
    (P ++ B.take (j + 1))⟦m⟧
      = (P ++ B.take p) ++ mTower (wnd P B j p) (wd0 P B j p) (wd1 P B j p) m := by
  set T := P ++ B.take (j + 1) with hT
  have hTl : T.length = P.length + (j + 1) := by
    rw [hT, List.length_append, List.length_take, Nat.min_eq_left (by omega)]
  have hL : T.length - 1 ≠ 0 := by omega
  have hLb : T.length - 1 - (P.length + p) = j - p := by omega
  have hle : P.length + p + (j - p) ≤ T.length := by omega
  unfold wnd wd0 wd1
  rw [oper_eq_gexp_gen m hL hz hpar, hpe, hLb, gexp_eq_take_append_mTower hle]
  congr 1
  rw [hT, List.take_append, List.take_of_length_le (by omega),
    Nat.add_sub_cancel_left, List.take_take, Nat.min_eq_left (by omega)]

/-- ★ **接頭辞 ＋ 窓 ＝ 1 つ長い接頭辞**（(U2) を消す鍵）。 -/
theorem prefix_append_wnd {P B : TrioSeq} {j p : ℕ} (hpj : p < j) :
    (P ++ B.take p) ++ wnd P B j p = P ++ B.take j := by
  unfold wnd
  have hd : (P ++ B.take (j + 1)).drop (P.length + p) = (B.take (j + 1)).drop p := by
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      Nat.add_sub_cancel_left]
  rw [hd, List.append_assoc]
  congr 1
  have h1 : ((B.take (j + 1)).drop p).take (j - p)
      = ((B.take (j + 1)).take (p + (j - p))).drop p := by
    rw [List.take_drop]
  have h2 : p + (j - p) = j := by omega
  rw [h1, h2, List.take_take, Nat.min_eq_left (by omega)]
  have h3 : (B.take j).take p = B.take p := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  rw [← h3, List.take_append_drop]


/-! ## 221. ★★★★★★★★ **遺伝の 3 本のうち 2 本は無料**でした（§170 の再発見）

**索引を引きました（手筋）。§170 に書いてありました:**

    **`Lcone.window_of_rtg0`**（`:456`、**無条件**）… 行 0 の鎖があれば「窓の根が狭義に最浅」
    **`L105Cap.window_root_shallow`**（§170、緑）… それを窓 `(M.drop j0).take Lb` の言葉に直す

**⟹ ★ そして行 0 の鎖は `parent_nextR` ＋ `nextR_le0` から**ただ**で出ます。**
**⟹ ⟹ ★★ つまり **`hr0(V)` は無料**です。⟹ 遺伝の義務は **`hz0(V)` 1 本**になります。**

⚠ **私は §170 で自分でこれを書いていました（「(H1) は前提として書く必要がない」）。**
**⟹ ⟹ その 50 節あとで `TowerP''` に `hr0` を入れて「遺伝が問題」と書きました。**
**⟹ ⟹ ⟹ **自分の緑を忘れていました**。⟹ 手筋（索引を引く）を自分の節にも使うべきでした。** -/

open Classical in
/-- ★★ **窓の `hr0` は無料**（親が居ることだけから出る）。 -/
theorem hr0_wnd {P B : TrioSeq} {j p : ℕ} (hjB : j < B.length) (hpj : p < j)
    (hpar : hasParent (P ++ B.take (j + 1))
      (srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1))
      ((P ++ B.take (j + 1)).length - 1))
    (hpe : parent (P ++ B.take (j + 1))
      (srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1))
      ((P ++ B.take (j + 1)).length - 1) = P.length + p) :
    ∀ l, 0 < l → l < (wnd P B j p).length →
      entry (wnd P B j p) 0 0 < entry (wnd P B j p) 0 l := by
  set T := P ++ B.take (j + 1) with hT
  have hTl : T.length = P.length + (j + 1) := by
    rw [hT, List.length_append, List.length_take, Nat.min_eq_left (by omega)]
  have hlast : T.length - 1 = P.length + j := by omega
  have hle0 : le0 T (P.length + p) (T.length - 1) := by
    have h := nextR_le0 (parent_nextR hpar)
    rw [hpe] at h
    exact h
  have hrtg : Relation.ReflTransGen (nextrel0 T) (P.length + p) (P.length + j) := by
    rw [← hlast]; exact hle0.2.2
  have hup : ∀ l, P.length + p < l → l ≤ P.length + p + (j - p) →
      entry T 0 (P.length + p) < entry T 0 l := by
    intro l hl0 hl1
    exact window_of_rtg0 hrtg (by omega) l hl0 (by omega)
  have hres := window_root_shallow (M := T) (j0 := P.length + p) (Lb := j - p)
    (by omega) hup
  unfold wnd
  exact hres

/-- ★ 窓の長さは `1` 以上。 -/
theorem wnd_pos {P B : TrioSeq} {j p : ℕ} (hjB : j < B.length) (hpj : p < j) :
    0 < (wnd P B j p).length := by
  rw [wnd_length hjB hpj]; omega

/-! ### 221.1 ⟹ ★★★ **`HeredPos` / `HeredZero` は `hz0(V)` だけになります**

`TowerP''` は 3 本（`0 < |Q|` / `hr0` / `hz0`）で、そのうち

    `0 < |V|` … `wnd_pos`（上、**無料**）
    `hr0(V)`  … `hr0_wnd`（上、**無料**）
    `hz0(V)`  … ⛔ **残る唯一の核**（＝ 既知の (H2')）

**⟹ ★★★ ⟹ **核は「窓の根の行 2 が 0 か」1 本**になりました。** -/

/-- ⛔ **核（唯一）**: 窓の根の行 2 が 0。 -/
def HeredZ2 : Prop :=
  ∀ (P B : TrioSeq) (j p : ℕ), j < B.length → p < j →
    hasParent (P ++ B.take (j + 1))
      (srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1))
      ((P ++ B.take (j + 1)).length - 1) →
    parent (P ++ B.take (j + 1))
      (srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1))
      ((P ++ B.take (j + 1)).length - 1) = P.length + p →
    entry (wnd P B j p) 2 0 = 0


/-! ## 224. ⟹ **§224 は歴史です**（§225 で `HeredZ2` ごと消えました）

⚠ **以下の §224.x は「`HeredZ2`（窓の根の行 2 が 0）を核として絞る」道でした。**
**⟹ ★ §225 `Row2RootOrph` で `hz0` を `TowerP''` から落としたので、
**`HeredZ2` / `HeredZ2core` / `RootZ2` は最終定理では使いません**。**
**⟹ ⟹ 残してあるのは、`Row2RootOrph` が偽だったときの**代替の道**としてです。**

---

## 224. ★★★★★★ `HeredZ2` を **`srow ≤ 1` に絞ります**

`HeredZ2` は「窓の根の行 2 が 0」＝「**バッドルートの列の行 2 が 0**」です。

**⟹ ★ `srow = 2` の段は**ただ**です。`nextrel2` が `entry 2 (親) < entry 2 (末尾)` を要求し、
`z < 2` の断片では `entry 2 (末尾) ≤ 1` なので `entry 2 (親) = 0`。**

⚠ **`W u` は `zle1` で閉じていません**（H12 `W_not_zle1_closed`: `[(0,0,2)] ∈ W 2`）。
**⟹ ですから `entry T 2 (末尾) ≤ 1` は**前提として渡す**必要があります。**
**⟹ ⟹ プロジェクトは `z < 2` の断片が対象なので、これは自然な前提です。** -/

open Classical in
/-- ★★ **`srow = 2` の段の `HeredZ2` は無料**（末尾列の行 2 が `≤ 1` なら）。 -/
theorem heredZ2_of_srow2 {P B : TrioSeq} {j p : ℕ} (hpj : p < j)
    (hpar : hasParent (P ++ B.take (j + 1))
      (srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1))
      ((P ++ B.take (j + 1)).length - 1))
    (hpe : parent (P ++ B.take (j + 1))
      (srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1))
      ((P ++ B.take (j + 1)).length - 1) = P.length + p)
    (hs2 : 1 < srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1))
    (hlast : entry (P ++ B.take (j + 1)) 2
      ((P ++ B.take (j + 1)).length - 1) ≤ 1) :
    entry (wnd P B j p) 2 0 = 0 := by
  set T := P ++ B.take (j + 1) with hT
  have hnr := parent_nextR hpar
  rw [hpe] at hnr
  unfold nextR at hnr
  rw [if_neg (by omega), if_neg (by omega)] at hnr
  have hlt := hnr.2.2.2.1
  unfold wnd
  rw [← hT, entry_window T (show 0 < j - p by omega), Nat.add_zero]
  omega

/-! ### 224.1 ⟹ ★ **残るのは `srow ≤ 1` の段だけ**

**⟹ そして `p = 0`（親がブロックの根）なら、窓の根は `Q` の根なので
`entry V 2 0 = entry Q 2 0 = 0`（`hz0(Q)`）で**やはり無料**です。**

**⟹ ⟹ ★★ ⟹ `HeredZ2` の残差は**

    **`srow ≤ 1` ∧ `p ≥ 1`**（＝ バッドルートが**ブロックの非根**で、その行 2 が正）

**⟹ ⟹ ⟹ ★ R2 の 98.4〜99.8% の残差 0.2〜1.6% は、ここに集中しているはずです。**

⚠ **教訓 14**: 最後の 2 行は**私の予想**です。R2 に測ってもらいます。
⚠ **そして `p = 0` の無料化は Lean では書いていません**（`entry T 2 P.length = entry Q 2 0`
の計算が要ります）。⟹ 上の `heredZ2_of_srow2` だけが緑です。 -/

/-! ### 224.2 ★★ `p = 0` の段の `HeredZ2` も**ただ**（窓の根が `Q` の根） -/

theorem entry2_block_root {Q : TrioSeq} (d e n : ℕ) (hQ1 : 0 < Q.length) :
    entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 2 0 = entry Q 2 0 := by
  show ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).getD 0 (0, 0, 0)).2.2 = _
  rw [block_getD (d := d) (e := e) (n := n) hQ1]

open Classical in
/-- ★ **`j ≥ 1` の段で `p = 0`**（親がブロックの根）なら `HeredZ2` は `hz0(Q)` そのもの。 -/
theorem heredZ2_of_p_zero {A Q : TrioSeq} {d e n j : ℕ}
    (hQ1 : 0 < Q.length) (hj1 : 0 < j) (hz0 : entry Q 2 0 = 0) :
    entry (wnd (A ++ mTower Q d e n)
      (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) j 0) 2 0 = 0 := by
  set P := A ++ mTower Q d e n with hPdef
  set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
  have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
  unfold wnd
  rw [entry_window _ (show 0 < j - 0 by omega), Nat.add_zero, Nat.add_zero]
  have h := entry_append_right P (B.take (j + 1)) 2 0
  rw [Nat.add_zero] at h
  rw [h, Wset.entry_take (show (0 : ℕ) < j + 1 by omega), hB,
    entry2_block_root d e n hQ1]
  exact hz0

open Classical in
/-- ★ **`j = 0` の段で `p = 0`**（親が 1 つ前のブロックの根）も同じ。 -/
theorem heredZ2_of_p_zero_pair {A Q : TrioSeq} {d e k : ℕ}
    (hQ1 : 0 < Q.length) (hz0 : entry Q 2 0 = 0) :
    entry (wnd (A ++ mTower Q d e k)
      (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
        ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))) Q.length 0) 2 0 = 0 := by
  set P := A ++ mTower Q d e k with hPdef
  set B0 := Lift1 (shiftr01 (d * k) 0 Q) (e * k) with hB0
  set B1 := Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1)) with hB1
  have hB0len : B0.length = Q.length := by rw [hB0, Lift1_length, shiftr01_length]
  unfold wnd
  rw [entry_window _ (show 0 < Q.length - 0 by omega), Nat.add_zero, Nat.add_zero]
  have h := entry_append_right P ((B0 ++ B1).take (Q.length + 1)) 2 0
  rw [Nat.add_zero] at h
  rw [h, Wset.entry_take (show (0 : ℕ) < Q.length + 1 by omega),
    entry_append_left _ _ (show (0 : ℕ) < B0.length by omega), hB0,
    entry2_block_root d e k hQ1]
  exact hz0

/-! ### 224.3 ⟹ ★★★ **`HeredZ2` の残差が式で書けました**

**§224 ＋ §224.2 より、`HeredZ2` が要るのは**

    **`srow (末尾) ≤ 1` ∧ `p ≥ 1`**

**の段**だけ**です。⟹ 他は全部無料:**

    `srow = 2` … §224 `heredZ2_of_srow2`（`entry 2 (末尾) ≤ 1` のもとで）
    `p = 0`    … §224.2 `heredZ2_of_p_zero` / `_pair`（`hz0(Q)` から）

**⟹ ★★ ⟹ R2 の 98.4〜99.8% の残差 0.2〜1.6% は、この 1 か所に集中しているはずです。**

⚠ **教訓 14**: 「集中しているはず」は**私の予想**です。**測ってもらいます。** -/

/-! ### 224.4 ★★★ 核を **`HeredZ2core`**（`srow ≤ 1` ∧ `p ≥ 1`）に絞る道具 -/

/-- ⛔ **核（最小形）**: `srow ≤ 1` かつ `p ≥ 1` の段での「窓の根の行 2 が 0」。 -/
def HeredZ2core : Prop :=
  ∀ (P B : TrioSeq) (j p : ℕ), j < B.length → 0 < p → p < j →
    srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1) ≤ 1 →
    hasParent (P ++ B.take (j + 1))
      (srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1))
      ((P ++ B.take (j + 1)).length - 1) →
    parent (P ++ B.take (j + 1))
      (srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1))
      ((P ++ B.take (j + 1)).length - 1) = P.length + p →
    entry (wnd P B j p) 2 0 = 0

/-- 塔 ＋ ブロック接頭辞の末尾列の行 2 は `Q` の行 2。 -/
theorem entry2_tower_last {A Q : TrioSeq} (d e n : ℕ) {j : ℕ} :
    entry (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 2
      ((A ++ mTower Q d e n).length + j) = entry Q 2 j := by
  rw [entry_append_right, entry2_block_take (show j < j + 1 by omega),
    Wset.entry_take (show j < j + 1 by omega)]

open Classical in
/-- ★★ **`j ≥ 1` の段の `HeredZ2` は核 ＋ `z < 2` から出る**。 -/
theorem heredZ2_pos_of_core {A Q : TrioSeq} {d e n j p : ℕ}
    (hz2 : HeredZ2core) (hQ1 : 0 < Q.length) (hz0 : entry Q 2 0 = 0)
    (hz1 : ∀ q, q < Q.length → entry Q 2 q ≤ 1)
    (hj : j < Q.length) (hj1 : 0 < j) (hpj : p < j)
    (hpar : hasParent (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (srow (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        ((A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1))
      ((A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1))
    (hpe : parent (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (srow (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        ((A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1))
      ((A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1)
      = (A ++ mTower Q d e n).length + p) :
    entry (wnd (A ++ mTower Q d e n)
      (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) j p) 2 0 = 0 := by
  set P := A ++ mTower Q d e n with hPdef
  set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
  have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
  have hTl : (P ++ B.take (j + 1)).length = P.length + (j + 1) := by
    rw [List.length_append, List.length_take, hBlen, Nat.min_eq_left (by omega)]
  have hlastidx : (P ++ B.take (j + 1)).length - 1 = P.length + j := by omega
  rcases Nat.eq_zero_or_pos p with hp0 | hp1
  · rw [hp0]; exact heredZ2_of_p_zero hQ1 hj1 hz0
  · by_cases hs : 1 < srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1)
    · refine heredZ2_of_srow2 hpj hpar hpe hs ?_
      rw [hlastidx, hPdef, hB]
      rw [entry2_tower_last (A := A) d e n]
      exact hz1 j hj
    · exact hz2 P B j p (by omega) hp1 hpj (by omega) hpar hpe

/-! ### 224.5 ★★ `z < 2`（行 2 ≤ 1）は**窓に遺伝します** -/

theorem entry2_wnd {A Q : TrioSeq} {d e n j p t : ℕ} (hpj : p < j)
    (ht : t < j - p) :
    entry (wnd (A ++ mTower Q d e n)
      (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) j p) 2 t = entry Q 2 (p + t) := by
  set P := A ++ mTower Q d e n with hPdef
  set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
  have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
  unfold wnd
  rw [entry_window _ ht,
    show P.length + p + t = P.length + (p + t) from by omega, entry_append_right,
    hB, entry2_block_take (show p + t < j + 1 by omega),
    Wset.entry_take (show p + t < j + 1 by omega)]

theorem entry2_wnd_pair {A Q : TrioSeq} {d e k p t : ℕ} (hp : p < Q.length)
    (ht : t < Q.length - p) :
    entry (wnd (A ++ mTower Q d e k)
      (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
        ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))) Q.length p) 2 t
      = entry Q 2 (p + t) := by
  set P := A ++ mTower Q d e k with hPdef
  set B0 := Lift1 (shiftr01 (d * k) 0 Q) (e * k) with hB0
  set B1 := Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1)) with hB1
  have hB0len : B0.length = Q.length := by rw [hB0, Lift1_length, shiftr01_length]
  unfold wnd
  rw [entry_window _ ht,
    show P.length + p + t = P.length + (p + t) from by omega, entry_append_right,
    Wset.entry_take (show p + t < Q.length + 1 by omega),
    entry_append_left _ _ (show p + t < B0.length by omega), hB0]
  show ((Lift1 (shiftr01 (d * k) 0 Q) (e * k)).getD (p + t) (0, 0, 0)).2.2 = _
  rw [block_getD (d := d) (e := e) (n := k) (show p + t < Q.length by omega)]

/-! ## 213. ★★★★★★★★★ **`hsnoc` の `j ≥ 1` の枝が緑になりました**

材料が全部そろったので組みます。**残る前提は「窓に `TowerP''` が遺伝する」1 本だけです。** -/

open Classical in
theorem hsnoc_pos {u : ℕ} {A Q : TrioSeq} {d e n j : ℕ}
    (hP : TowerP'' Q d e)
    (hIH : ∀ V d0 d1, TowerP'' V d0 d1 → towerMeas V d0 d1 < towerMeas Q d e →
      ∀ A', A' ∈ W u → A' ++ V ∈ W u → ∀ m, A' ++ mTower V d0 d1 m ∈ W u)
    (hj : j < Q.length) (hj1 : 0 < j)
    (hloc : hasParent ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (srow ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) j) j)
    (hbound : (A ++ mTower Q d e n).length ≤
      parent (A ++ mTower Q d e n
          ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        (srow (A ++ mTower Q d e n
          ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
          ((A ++ mTower Q d e n).length + j))
        ((A ++ mTower Q d e n).length + j))
    (hall : ∀ j', j' ≤ j →
      A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j' ∈ W u)
:
    A ++ mTower Q d e n
      ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1) ∈ W u := by
  have hr0Q := hr0_of_TowerP'' hP
  set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
  set P := A ++ mTower Q d e n with hPdef
  have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
  have hQ1 : 0 < Q.length := by omega
  have hTlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have hPlen : P.length = A.length + n * Q.length := by
    rw [hPdef, List.length_append, hTlen]
  set S := P ++ B.take (j + 1) with hS
  have hSlen : S.length = P.length + (j + 1) := by
    rw [hS, List.length_append, List.length_take, hBlen, Nat.min_eq_left (by omega)]
  have hlast : S.length - 1 = P.length + j := by omega
  -- ★ 親が居ること（§212）
  have hpT := tower_hasParent_of_block (Q := Q) (d := d) (e := e) (n := n) hloc
  have hassoc : S = A ++ (mTower Q d e n ++ B.take (j + 1)) := by
    rw [hS, hPdef, List.append_assoc]
  have hidx : A.length + (n * Q.length + j) = P.length + j := by omega
  have hpar : hasParent S (srow S (S.length - 1)) (S.length - 1) := by
    rw [hlast, hassoc, ← hidx]
    rw [srow_append_right]
    exact hasParent_append_right_of _ _ hpT
  -- ★ 末尾列が全部 0 ではないこと
  have hE0 : entry S 0 (P.length + j) = entry Q 0 j + d * n := by
    rw [hS, show P.length + j = P.length + j from rfl, entry_append_right,
      Wset.entry_take (show j < j + 1 by omega), hB, entry0_Lift1,
      entry0_shiftr01 (by omega)]
  have hQj : 0 < entry Q 0 j := by have := hr0Q j hj1 hj; omega
  have hz : ¬ (entry S 0 (S.length - 1) = 0 ∧ entry S 1 (S.length - 1) = 0 ∧
      entry S 2 (S.length - 1) = 0) := by
    rw [hlast]
    intro hc
    rw [hE0] at hc
    omega
  -- ★ 親の位置
  set par := parent S (srow S (S.length - 1)) (S.length - 1) with hpardef
  have hbound' : P.length ≤ par := by rw [hpardef, hlast]; exact hbound
  have hltp : par < S.length - 1 := nextR_index_lt (parent_nextR hpar)
  set p := par - P.length with hpdef
  have hpj : p < j := by omega
  have hpe : par = P.length + p := by omega
  -- ★ 展開して帰納法の仮定を当てる
  refine mem_of_oper_mem ?_
  intro m _
  have heq := snocStep_oper_pre_eq (P := P) (B := B) (j := j) (p := p) (m := m)
    (by omega) hpj hz hpar (by rw [← hpardef, hpe])
  rw [← hS] at heq
  rw [heq]
  have hlen := wnd_length (P := P) (B := B) (j := j) (p := p) (by omega) hpj
  have hz1 := hz1_of_TowerP'' hP
  have hlenV := wnd_length (P := P) (B := B) (j := j) (p := p) (by omega) hpj
  refine hIH (wnd P B j p) (wd0 P B j p) (wd1 P B j p)
    ⟨wnd_pos (by omega) hpj, hr0_wnd (by omega) hpj hpar (by rw [← hpardef]; exact hpe),
      fun q hq => by
        rw [hlenV] at hq
        rw [entry2_wnd hpj hq]
        exact hz1 (p + q) (by omega)⟩ ?_
    (P ++ B.take p) (hall p (by omega))
    (by rw [prefix_append_wnd hpj]; exact hall j (le_refl j)) m
  unfold towerMeas
  refine natMeasure_lt (rankDE_le_two d e)
    (rankDE_le_two (wd0 P B j p) (wd1 P B j p)) ?_
  left
  rw [hlen]
  omega

/-! ## 214. ★★★★★★★★ `hsnoc` の `j = 0`（`n = k+1`）の枝

§205 の読み替えで `j = 0` は `j' = |Q|` の**通常の場合**になります（§204.2）。
**⟹ 測度の合成はそのまま。⟹ 違うのは「親がどこにいるか」だけです。**

⚠ **親の位置（`親 ≥ (A ++ mTower Q d e k).length` ＝ **高々 1 ブロック手前**）は
H12 の `blockRoot_parent_prevBlock` の仕事なので、ここでは**前提**にします。**
**⟹ ⟹ そこだけが未完で、測度の側は下で緑になります。** -/

open Classical in
theorem hsnoc_zero_of_parent {u : ℕ} {A Q : TrioSeq} {d e k p : ℕ} (hd : 0 < d)
    (hIH : ∀ V d0 d1, TowerP'' V d0 d1 → towerMeas V d0 d1 < towerMeas Q d e →
      ∀ A', A' ∈ W u → A' ++ V ∈ W u → ∀ m, A' ++ mTower V d0 d1 m ∈ W u)
    (hQ1 : 0 < Q.length)
    (hprefull : A ++ mTower Q d e k
      ++ (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
          ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take Q.length ∈ W u)
    (hpre : A ++ mTower Q d e k
      ++ (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
          ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take p ∈ W u)
    (hplt : p < Q.length)
    (hpar : hasParent
      (A ++ mTower Q d e k
        ++ (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
            ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take (Q.length + 1))
      (srow (A ++ mTower Q d e k
        ++ (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
            ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take (Q.length + 1))
        ((A ++ mTower Q d e k
        ++ (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
            ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take
              (Q.length + 1)).length - 1))
      ((A ++ mTower Q d e k
        ++ (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
            ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take
              (Q.length + 1)).length - 1))
    (hpe : parent
      (A ++ mTower Q d e k
        ++ (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
            ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take (Q.length + 1))
      (srow (A ++ mTower Q d e k
        ++ (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
            ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take (Q.length + 1))
        ((A ++ mTower Q d e k
        ++ (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
            ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take
              (Q.length + 1)).length - 1))
      ((A ++ mTower Q d e k
        ++ (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
            ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take
              (Q.length + 1)).length - 1)
      = (A ++ mTower Q d e k).length + p)
    (hz1 : ∀ q, q < Q.length → entry Q 2 q ≤ 1)
    (hrank : p = 0 →
      rankDE (wd0 (A ++ mTower Q d e k)
          (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
            ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))) Q.length p)
        (wd1 (A ++ mTower Q d e k)
          (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
            ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))) Q.length p)
        < rankDE d e)
:
    A ++ mTower Q d e (k + 1)
      ++ (Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take 1 ∈ W u := by
  set B0 := Lift1 (shiftr01 (d * k) 0 Q) (e * k) with hB0
  set B1 := Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1)) with hB1
  set P := A ++ mTower Q d e k with hPdef
  have hB0len : B0.length = Q.length := by rw [hB0, Lift1_length, shiftr01_length]
  have hB1len : B1.length = Q.length := by rw [hB1, Lift1_length, shiftr01_length]
  have hBlen : (B0 ++ B1).length = Q.length + Q.length := by
    rw [List.length_append, hB0len, hB1len]
  -- ★ §205 の読み替え
  have hre : A ++ mTower Q d e (k + 1) ++ B1.take 1
      = P ++ (B0 ++ B1).take (Q.length + 1) := by
    rw [hPdef, hB0, hB1, prefix_mTower_take_reassoc A Q d e k 1, List.append_assoc]
  rw [hre]
  set S := P ++ (B0 ++ B1).take (Q.length + 1) with hS
  have hSlen : S.length = P.length + (Q.length + 1) := by
    rw [hS, List.length_append, List.length_take, hBlen, Nat.min_eq_left (by omega)]
  have hlast : S.length - 1 = P.length + Q.length := by omega
  -- ★ 末尾列は第 (k+1) ブロックの根。行 0 は `entry Q 0 0 + d*(k+1)` で正
  have hE0 : entry S 0 (P.length + Q.length) = entry Q 0 0 + d * (k + 1) := by
    rw [hS, entry_append_right, Wset.entry_take (show Q.length < Q.length + 1 by omega),
      show Q.length = B0.length + 0 from by omega, entry_append_right, Nat.add_zero,
      hB1, entry0_Lift1, entry0_shiftr01 (by omega)]
  have hz : ¬ (entry S 0 (S.length - 1) = 0 ∧ entry S 1 (S.length - 1) = 0 ∧
      entry S 2 (S.length - 1) = 0) := by
    rw [hlast]
    intro hc
    rw [hE0] at hc
    have : 0 < d * (k + 1) := Nat.mul_pos hd (by omega)
    omega
  -- ★ 展開して帰納法の仮定を当てる
  refine mem_of_oper_mem ?_
  intro m _
  have heq := snocStep_oper_pre_eq (P := P) (B := B0 ++ B1) (j := Q.length)
    (p := p) (m := m) (by omega) hplt hz hpar hpe
  rw [← hS] at heq
  rw [heq]
  have hlen := wnd_length (P := P) (B := B0 ++ B1) (j := Q.length) (p := p)
    (by omega) hplt
  refine hIH _ _ _ ⟨wnd_pos (by omega) hplt,
    hr0_wnd (by omega) hplt hpar hpe,
    fun q hq => by
      rw [wnd_length (P := P) (B := B0 ++ B1) (j := Q.length) (p := p)
        (by omega) hplt] at hq
      rw [entry2_wnd_pair hplt hq]
      exact hz1 (p + q) (by omega)⟩
    ?_ (P ++ (B0 ++ B1).take p)
    (by rw [hPdef] at hpre ⊢; exact hpre)
    (by rw [prefix_append_wnd hplt]; rw [hPdef] at hprefull ⊢; exact hprefull) m
  unfold towerMeas
  refine natMeasure_lt (rankDE_le_two d e) (rankDE_le_two _ _) ?_
  rcases Nat.eq_zero_or_pos p with hp0 | hp1
  · right
    refine ⟨by rw [hlen, hp0]; omega, hrank hp0⟩
  · left
    rw [hlen]; omega

/-! ## 215. ★★★★★★★★ (U1): **ブロックの根の親は高々 1 ブロック手前**（接頭辞つき）

§214 で**前提**にしていた「親の位置」を証明します。**索引から 3 本見つけました:**

    **`Wset.hasParent_one_of`**（`:1823`）… `le0` の鎖の上に行 1 が小さい列が 1 つあれば**親は存在する**
    **`L105Cap.parent_ge_of_inner`**（`:7480`）… 塔の中に親がいれば、接頭辞は親になれない（**前提なし**）
    **H12 `blockRoot_parent_prevBlock`** … 塔の中で「高々 1 ブロック手前」

**⟹ ★ 3 本をつなぐだけで (U1) が出ます。** -/

/-- `mTower Q d e (k+1) ++ 第 (k+1) ブロックの根 1 列` は `mTower Q d e (k+2)` の接頭辞。 -/
theorem tower_snoc_root_eq_take (Q : TrioSeq) (d e k : ℕ) :
    mTower Q d e (k + 1)
        ++ (Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take 1
      = (mTower Q d e (k + 2)).take ((k + 1) * Q.length + 1) := by
  have hlen : (mTower Q d e (k + 1)).length = (k + 1) * Q.length :=
    mTower_length Q d e (k + 1)
  have hfull : (mTower Q d e (k + 1)).take ((k + 1) * Q.length + 1)
      = mTower Q d e (k + 1) := List.take_of_length_le (by omega)
  conv_rhs => rw [show k + 2 = (k + 1) + 1 from rfl, mTower_succ]
  rw [List.take_append, hfull, hlen, Nat.add_sub_cancel_left]

/-- ★★ **ブロックの根は行 1 の親を持つ**（証人は 1 つ前のブロックの根）。 -/
theorem blockRoot_hasParent_prev {Q : TrioSeq} {d e k : ℕ}
    (hQne : Q ≠ []) (hd : 0 < d) (he : 0 < e)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) :
    hasParent (mTower Q d e (k + 2)) 1 ((k + 1) * Q.length) := by
  have hQ1 : 0 < Q.length := List.length_pos_iff.mpr hQne
  have hTlen : (mTower Q d e (k + 2)).length = (k + 2) * Q.length :=
    mTower_length Q d e (k + 2)
  have hb1 : k * Q.length < (mTower Q d e (k + 2)).length := by
    rw [hTlen]
    exact Nat.lt_of_lt_of_le
      (show k * Q.length < (k + 1) * Q.length from by rw [Nat.succ_mul]; omega)
      (Nat.mul_le_mul_right _ (by omega))
  have hb2 : (k + 1) * Q.length < (mTower Q d e (k + 2)).length := by
    rw [hTlen]
    have h : (k + 2) * Q.length = (k + 1) * Q.length + Q.length :=
      Nat.succ_mul (k + 1) Q.length
    omega
  refine hasParent_one_of hb2 (show k * Q.length < (k + 1) * Q.length from by
      rw [Nat.succ_mul]; omega)
    ⟨hb1, hb2, rtg0_blockRoot_succ hQne hd (show k + 1 < k + 2 by omega) hr0⟩ ?_
  rw [entry1_mTower_blockRoot hQne d e (k + 2) k (by omega),
    entry1_mTower_blockRoot hQne d e (k + 2) (k + 1) (by omega)]
  have hmul : e * (k + 1) = e * k + e := Nat.mul_succ e k
  omega

/-- `take` を跨いで `parent` は同じ。 -/
theorem parent_take {X : TrioSeq} {l i b : ℕ} (hl : l ≤ X.length) (hb : b < l)
    (hp : hasParent (X.take l) i b) : parent (X.take l) i b = parent X i b := by
  have hpX : hasParent X i b := (hasParent_take hl hb).mp hp
  exact hpX.unique ((nextR_take hl hb).mp (parent_nextR hp)) (parent_nextR hpX)

/-! ### 215.1 ★★★ (U1) 本体 -/

open Classical in
theorem blockRoot_parent_ge_prefix {A Q : TrioSeq} {d e k : ℕ}
    (hQne : Q ≠ []) (hd : 0 < d) (he : 0 < e)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) :
    (A ++ mTower Q d e k).length ≤
      parent (A ++ (mTower Q d e (k + 1)
          ++ (Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take 1)) 1
        (A.length + (k + 1) * Q.length) := by
  have hQ1 : 0 < Q.length := List.length_pos_iff.mpr hQne
  set T := mTower Q d e (k + 1)
      ++ (Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take 1 with hTdef
  have hTeq : T = (mTower Q d e (k + 2)).take ((k + 1) * Q.length + 1) := by
    rw [hTdef]; exact tower_snoc_root_eq_take Q d e k
  have hTlen2 : (mTower Q d e (k + 2)).length = (k + 2) * Q.length :=
    mTower_length Q d e (k + 2)
  have hle : (k + 1) * Q.length + 1 ≤ (mTower Q d e (k + 2)).length := by
    rw [hTlen2]
    have h : (k + 2) * Q.length = (k + 1) * Q.length + Q.length :=
      Nat.succ_mul (k + 1) Q.length
    omega
  -- ★ 塔の中に親がいる
  have hpM := blockRoot_hasParent_prev (Q := Q) (d := d) (e := e) (k := k) hQne hd he hr0
  have hpT : hasParent T 1 ((k + 1) * Q.length) := by
    rw [hTeq]
    exact (hasParent_take hle (by omega)).mpr hpM
  -- ★ 親の位置（塔の中）
  have hpe : parent T 1 ((k + 1) * Q.length)
      = parent (mTower Q d e (k + 2)) 1 ((k + 1) * Q.length) := by
    rw [hTeq] at hpT ⊢
    exact parent_take hle (by omega) hpT
  have hge : k * Q.length ≤ parent (mTower Q d e (k + 2)) 1 ((k + 1) * Q.length) := by
    have hnr := parent_nextR hpM
    unfold nextR at hnr
    rw [if_neg (by omega), if_pos rfl] at hnr
    exact blockRoot_parent_prevBlock hQne hd he (show k + 1 < k + 2 by omega) hr0 hnr
  -- ★ 接頭辞を跨ぐ（前提なし）
  rw [parent_append_right_of A T hpT, List.length_append, mTower_length, hpe]
  omega

/-! ## 217. ★★★★★★ (U4): `p = 0` のとき `rankDE` が減る（`hrank`）

§216 が残した `hrank` を証明します。**`p = 0` ＝ 親が第 `k` ブロックの根なので:**

    `srow = 1` ⟹ `wd1 = 0`、`wd0 = entry S 0 (末尾) − entry S 0 (第 k ブロックの根)`
             `= (entry Q 0 0 + d*(k+1)) − (entry Q 0 0 + d*k) = **d**`
    ⟹ `rankDE d 0 = 1`（`0 < d`）、`rankDE d e = 2`（`0 < d`、`0 < e`）

**⟹ ★ `1 < 2`。⟹ §200 の一般形と同じことを、この形で直接出します。** -/

open Classical in
theorem hrank_blockRoot {A Q : TrioSeq} {d e k : ℕ}
    (hQne : Q ≠ []) (hd : 0 < d) (he : 0 < e) (hz0 : entry Q 2 0 = 0) :
    rankDE
      (wd0 (A ++ mTower Q d e k)
        (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
          ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))) Q.length 0)
      (wd1 (A ++ mTower Q d e k)
        (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
          ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))) Q.length 0)
      < rankDE d e := by
  have hQ1 : 0 < Q.length := List.length_pos_iff.mpr hQne
  set B0 := Lift1 (shiftr01 (d * k) 0 Q) (e * k) with hB0
  set B1 := Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1)) with hB1
  set P := A ++ mTower Q d e k with hPdef
  have hB0len : B0.length = Q.length := by rw [hB0, Lift1_length, shiftr01_length]
  have hB1len : B1.length = Q.length := by rw [hB1, Lift1_length, shiftr01_length]
  have hBlen : (B0 ++ B1).length = Q.length + Q.length := by
    rw [List.length_append, hB0len, hB1len]
  set S := P ++ (B0 ++ B1).take (Q.length + 1) with hS
  have hSlen : S.length = P.length + (Q.length + 1) := by
    rw [hS, List.length_append, List.length_take, hBlen, Nat.min_eq_left (by omega)]
  have hlast : S.length - 1 = P.length + Q.length := by omega
  -- 末尾列（第 (k+1) ブロックの根）
  have hEl : ∀ i, entry S i (P.length + Q.length) = entry B1 i 0 := by
    intro i
    rw [hS, entry_append_right, Wset.entry_take (show Q.length < Q.length + 1 by omega),
      show Q.length = B0.length + 0 from by omega, entry_append_right]
  -- 第 k ブロックの根
  have hEr : ∀ i, entry S i P.length = entry B0 i 0 := by
    intro i
    have h := entry_append_right P ((B0 ++ B1).take (Q.length + 1)) i 0
    simp only [Nat.add_zero] at h
    rw [hS, h, Wset.entry_take (show (0 : ℕ) < Q.length + 1 by omega),
      entry_append_left _ _ (show (0 : ℕ) < B0.length by omega)]
  have hB1_0 : entry B1 0 0 = entry Q 0 0 + d * (k + 1) := by
    rw [hB1, entry0_Lift1, entry0_shiftr01 (by omega)]
  have hB1_1 : entry B1 1 0 = entry Q 1 0 + e * (k + 1) := by
    rw [hB1]
    show ((Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).getD 0 (0, 0, 0)).2.1 = _
    rw [block_getD (d := d) (e := e) (n := k + 1) hQ1, if_pos (le1_refl hQ1)]
  have hB1_2 : entry B1 2 0 = entry Q 2 0 := by
    rw [hB1]
    show ((Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).getD 0 (0, 0, 0)).2.2 = _
    rw [block_getD (d := d) (e := e) (n := k + 1) hQ1]
  have hB0_0 : entry B0 0 0 = entry Q 0 0 + d * k := by
    rw [hB0, entry0_Lift1, entry0_shiftr01 (by omega)]
  -- `srow` は 1
  have hs1 : srow S (S.length - 1) = 1 := by
    rw [hlast]
    unfold srow
    rw [hEl 2, hEl 1, hB1_2, hB1_1, hz0]
    rw [if_neg (by omega), if_pos (by
      have : 0 < e * (k + 1) := Nat.mul_pos he (by omega)
      omega)]
  -- 計算
  have hw1 : wd1 P (B0 ++ B1) Q.length 0 = 0 := by
    unfold wd1
    rw [← hS, hs1, if_neg (by omega)]
  have hw0 : wd0 P (B0 ++ B1) Q.length 0 = d := by
    unfold wd0
    rw [← hS, hs1, if_pos (by omega), hlast, hEl 0, Nat.add_zero, hEr 0, hB1_0, hB0_0]
    have hmul : d * (k + 1) = d * k + d := Nat.mul_succ d k
    omega
  rw [hw0, hw1]
  unfold rankDE
  rw [if_pos he]
  split_ifs <;> omega

/-! ## 218. ★★★★★★★★★ (U2) を消します: **底のブロックは「作る」のではなく「もらう」**

⚠ (U2)（`n = 0` かつ `j = 0` ＝ `A` に直接 snoc）は `WSnoc` の形で、手が出ませんでした。

**⟹ ★ ですが `mTower Q d e 1 = Q`（§57 `mTower_one`）です。**
**⟹ ⟹ 底のブロックを**1 列ずつ作る**のをやめて、**`A ++ Q ∈ W u` を前提としてもらえば**、
`n = 0` の段は**そもそも現れません**。**

**⟹ ★ そしてそれは**両側で無料**です:**

    **消費側** … `A = []` なので `Q ∈ W u`。⟹ `MTowerClosedS` の仮定**そのもの** ✅
    **帰納の中** … `A' = P ++ B.take p`、`V` は窓なので
              **`A' ++ V = P ++ B.take j`** ⟹ `hall j` **そのもの** ✅

⟹ ⟹ ★★ **(U2) は「前提の置き方が悪かった」だけでした。** -/

/-! ### 218.1 ★★ 底のブロックをもらう版の外枠（§168 の差し替え） -/

theorem prefixTowerClosed_of_snocStepStrong1 {u : ℕ} {A Q : TrioSeq} {d e : ℕ}
    (hA : A ∈ W u) (hA1 : A ++ Q ∈ W u)
    (hstep : ∀ (n j : ℕ), 1 ≤ n → j < Q.length →
      (∀ j', j' ≤ j →
        A ++ mTower Q d e n
          ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j' ∈ W u) →
      A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1) ∈ W u) :
    ∀ n, A ++ mTower Q d e n ∈ W u := by
  have key : ∀ n, A ++ mTower Q d e (n + 1) ∈ W u := by
    intro n
    induction n with
    | zero => rw [mTower_one]; exact hA1
    | succ n ih =>
        have hall : ∀ j, j ≤ Q.length → ∀ j', j' ≤ j →
            A ++ mTower Q d e (n + 1)
              ++ (Lift1 (shiftr01 (d * (n + 1)) 0 Q) (e * (n + 1))).take j' ∈ W u := by
          intro j
          induction j with
          | zero =>
              intro _ j' hj'
              have : j' = 0 := by omega
              subst this
              simpa using ih
          | succ j ihj =>
              intro hj j' hj'
              rcases Nat.lt_or_ge j' (j + 1) with hlt | hge
              · exact ihj (by omega) j' (by omega)
              · have hje : j' = j + 1 := by omega
                subst hje
                exact hstep (n + 1) j (by omega) (by omega) (ihj (by omega))
        have hfull := hall Q.length le_rfl Q.length le_rfl
        rw [List.take_of_length_le (by rw [Lift1_length, shiftr01_length])] at hfull
        rw [show n + 1 + 1 = (n + 1) + 1 from rfl, mTower_succ, ← List.append_assoc]
        exact hfull
  intro n
  cases n with
  | zero => rw [mTower_zero, List.append_nil]; exact hA
  | succ n => exact key n

/-! ## 219. ★★★★★★ 最終配線のための小道具

★ **索引を引いて `Wset.W_take`（`:2120`、`M ∈ W u → M.take k ∈ W u`）を見つけました。**
**⟹ ★ `W u` は**接頭辞で閉じています**。⟹ 「短い接頭辞は全部 `W u`」は**ただ**でした。**
**⟹ ⟹ 私は §168 の `hall` を**苦労して回して**いましたが、1 本で済みます。** -/

open Classical in
/-- ★★ `j ≥ 1` の段の**親の位置**（前提は `TowerP''` だけ）。 -/
theorem parent_bound_pos {A Q : TrioSeq} {d e n j : ℕ}
    (hj : j < Q.length)
    (hloc : hasParent ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (srow ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) j) j) :
    (A ++ mTower Q d e n).length ≤
      parent (A ++ mTower Q d e n
          ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        (srow (A ++ mTower Q d e n
          ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
          ((A ++ mTower Q d e n).length + j))
        ((A ++ mTower Q d e n).length + j) := by
  set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
  have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
  have hlen1 : (A ++ mTower Q d e n ++ B.take (j + 1)).length
      = (A ++ mTower Q d e n).length + (j + 1) := by
    rw [List.length_append, List.length_take, hBlen, Nat.min_eq_left (by omega)]
  have hsrow : srow (A ++ mTower Q d e n ++ B.take (j + 1))
      ((A ++ mTower Q d e n).length + j) = srow (B.take (j + 1)) j :=
    srow_append_right _ _ j
  rw [hsrow]
  have hp : hasParent (A ++ mTower Q d e n ++ B.take (j + 1))
      (srow (B.take (j + 1)) j)
      ((A ++ mTower Q d e n ++ B.take (j + 1)).length - 1) := by
    rw [hlen1, show (A ++ mTower Q d e n).length + (j + 1) - 1
      = (A ++ mTower Q d e n).length + j from by omega]
    exact hasParent_append_right_of _ _ hloc
  have hres := prefixSnocStep_parent_sameBlock (A := A) (d := d) (e := e) (n := n)
    (i := srow (B.take (j + 1)) j) hj hloc hp
  rw [hlen1, show (A ++ mTower Q d e n).length + (j + 1) - 1
    = (A ++ mTower Q d e n).length + j from by omega] at hres
  exact hres

/-- ★ 第 `k` ブロックの接頭辞は `W_take` でただ。 -/
theorem prefix_block_take_mem {u : ℕ} {A Q : TrioSeq} {d e k p : ℕ}
    (hp : p ≤ Q.length) (h : A ++ mTower Q d e (k + 1) ∈ W u) :
    A ++ mTower Q d e k
      ++ (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
          ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take p ∈ W u := by
  set B0 := Lift1 (shiftr01 (d * k) 0 Q) (e * k) with hB0
  set B1 := Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1)) with hB1
  have hB0len : B0.length = Q.length := by rw [hB0, Lift1_length, shiftr01_length]
  have hcut : (B0 ++ B1).take p = B0.take p := by
    rw [List.take_append, show p - B0.length = 0 from by omega, List.take_zero,
      List.append_nil]
  have hfull : (mTower Q d e k).take (k * Q.length + p) = mTower Q d e k :=
    List.take_of_length_le (by rw [mTower_length]; omega)
  have hkey : A ++ mTower Q d e k ++ B0.take p
      = (A ++ mTower Q d e (k + 1)).take (A.length + (k * Q.length + p)) := by
    rw [mTower_succ, ← hB0, take_append_right, List.take_append, hfull,
      mTower_length, Nat.add_sub_cancel_left, List.append_assoc]
  rw [hcut, hkey]
  exact W_take h _

/-! ## 220. ★★★★★★★★★★ **最終配線** —— 残る義務は**遺伝 2 本**だけ

### 220.1 ★ まず `0 < d` は `TowerP''` から**出ます**（`TowerP3` は要りませんでした）

`hd0e` は `entry M 0 |Q| = entry M 0 0 + d`、`hr0M` は `entry M 0 0 < entry M 0 |Q|`。
**⟹ ★ 2 つを合わせると `entry M 0 0 < entry M 0 0 + d` ⟹ `0 < d`。**

⚠ **私は「`0 < d` は未確認の別ルート」と team-lead に書きました。⟹ **誤り**でした。**
**⟹ 前提の束の中で**既に含意されて**いました。** -/



/-! ### 220.2 遺伝（残る唯一の義務）を 2 本の述語にします -/

/-! ### 220.2b ★★★ `h2out` / `h1out` を**遺伝しない仮定**に置き換えます

⚠ **H12 の実測**: **`hloc`（ブロックの中に親がいる）は錐の外の列で 68.8% 失敗**。
**⟹ §210 は「`h2out` ∧ `h1out` ⟹ `hloc`」なので、`h2out`/`h1out` も 68.8% 以上失敗します。**

**⟹ ★ ですが `hloc` が失敗する列が**全体でも孤児**なら、`snoc_orphan_W` で**無料**です。**
**⟹ ⟹ だから要るのは「ブロックの中で孤児 ⟹ 全体でも孤児」だけ。**

> **⟹ ★★ これは `Q` の性質ではなく**族全体についての 1 つの仮定**です。**
> **⟹ ⟹ **遺伝させる必要がありません**。⟹ 遺伝の義務が 2 本減ります。** -/

/-- ⛔ **`OrphOK`**: ブロックの中で孤児なら、接頭辞と塔を付けても孤児のまま。 -/
def OrphOK : Prop :=
  ∀ (A Q : TrioSeq) (d e n j : ℕ), 0 < j → j < Q.length →
    ¬ hasParent ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        (srow ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) j) j →
    ¬ hasParent (A ++ mTower Q d e n
          ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        (srow (A ++ mTower Q d e n
          ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
          ((A ++ mTower Q d e n).length + j))
        ((A ++ mTower Q d e n).length + j)

/-! ## 223. ★★★★★★★★★ `0 < e` を落とします —— H12 の (q3b) が効きました

H12 が `blockRoot_parent_prevBlock_noE`（**`0 < e` 不要**）と
`blockRoot_parent_prevBlock_row0'`（**行 0 版**）を緑にしてくれました。

**⟹ ★ これで `j = 0` の枝から `0 < e` が落ちます。⟹ `ZeroEOK` が要らなくなります。**

⚠ **値段**: `0 < e` は **親の存在**にも使っていました（証人 ＝ 1 つ前のブロックの根）。
**⟹ ⟹ 落とすと、親が**居ない**場合が出ます。⟹ そこは **`snoc_orphan_W` で無料**にします。**
**⟹ ⟹ ⟹ ただし「塔の中で親なし ⟹ 全体でも親なし」が要ります（＝ `OrphOK0`）。**

⚠ **R2 の実測**: **`e = 0` でもブロック根の親は一度も飛び越えない（0/732140）、
核の形では親なし 100%** ⟹ **`OrphOK0` は見込みがあります**。 -/

/-- ⛔⛔ **`ZeroDOK`**（`d = 0` の塔）。§223.3 で消したつもりでしたが**戻しました**。
理由は §223.6（team-lead の指摘）: `d = 0` ではブロック根は**塔の中で**必ず孤児ですが、
**接頭辞 `A` が親を供給しうる**（H12 `hasParent0_prefix_blockRoot_iff_d_zero`、緑）。
⟹ ⟹ 孤児の枝に落ちず、`OrphOK0` の前件を満たしても後件が偽になります。 -/
def ZeroDOK (u : ℕ) : Prop :=
  ∀ (A Q : TrioSeq) (e : ℕ), TowerP'' Q 0 e → A ∈ W u → A ++ Q ∈ W u →
    ∀ n, A ++ mTower Q 0 e n ∈ W u

/-- ⛔ **`OrphOK0`**: ブロックの根が**塔の中**で孤児なら、接頭辞を付けても孤児。
⚠ **`0 < d` が要ります**（`d = 0` では H12 の定理が反例を与えます。§223.6）。 -/
def OrphOK0 : Prop :=
  ∀ (A Q : TrioSeq) (d e k : ℕ), 0 < d →
    ¬ hasParent (mTower Q d e (k + 1)
        ++ (Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take 1)
      (srow (mTower Q d e (k + 1)
        ++ (Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take 1)
        ((k + 1) * Q.length))
      ((k + 1) * Q.length) →
    ¬ hasParent (A ++ (mTower Q d e (k + 1)
        ++ (Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take 1))
      (srow (A ++ (mTower Q d e (k + 1)
        ++ (Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take 1))
        (A.length + (k + 1) * Q.length))
      (A.length + (k + 1) * Q.length)

/-- ★ ブロックの根の `srow` は `hz0` から `≤ 1`。 -/
theorem blockRoot_srow_le_one {Q : TrioSeq} {d e n k : ℕ}
    (hQ1 : 0 < Q.length) (hk : k < n) (hz0 : entry Q 2 0 = 0) :
    srow (mTower Q d e n) (k * Q.length) ≤ 1 := by
  have h2 : entry (mTower Q d e n) 2 (k * Q.length) = 0 := by
    rw [mTower_entry2_root hk hQ1]; exact hz0
  unfold srow
  rw [if_neg (by omega)]
  split_ifs <;> omega

/-- ★★ **`0 < e` なしのブロック根の親の位置**（塔の中）。 -/
theorem blockRoot_parent_ge_noE {Q : TrioSeq} {d e n k : ℕ}
    (hQne : Q ≠ []) (hd : 0 < d) (hk : k + 1 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hz0 : entry Q 2 0 = 0)
    (hp : hasParent (mTower Q d e n)
      (srow (mTower Q d e n) ((k + 1) * Q.length)) ((k + 1) * Q.length)) :
    k * Q.length ≤ parent (mTower Q d e n)
      (srow (mTower Q d e n) ((k + 1) * Q.length)) ((k + 1) * Q.length) := by
  have hQ1 : 0 < Q.length := List.length_pos_iff.mpr hQne
  have hs := blockRoot_srow_le_one (Q := Q) (d := d) (e := e) (n := n) (k := k + 1)
    hQ1 (by omega) hz0
  have hnr := parent_nextR hp
  rcases Nat.eq_zero_or_pos (srow (mTower Q d e n) ((k + 1) * Q.length)) with h0 | h1
  · rw [h0] at hnr hp ⊢
    exact blockRoot_parent_prevBlock_row0' hQ1 hd hk hp
  · have hs1 : srow (mTower Q d e n) ((k + 1) * Q.length) = 1 := by omega
    rw [hs1] at hnr ⊢
    unfold nextR at hnr
    rw [if_neg (by omega), if_pos rfl] at hnr
    exact blockRoot_parent_prevBlock_noE hQne hd hk hr0 hnr

/-! ### 223.1 ★★ `p = 0` の `rankDE` の減少（`0 < e` なし） -/

open Classical in
theorem hrank_blockRoot_noE {A Q : TrioSeq} {d e k : ℕ}
    (hQne : Q ≠ []) (hd : 0 < d) (hz0 : entry Q 2 0 = 0)
    (hpM : hasParent (mTower Q d e (k + 2))
      (srow (mTower Q d e (k + 2)) ((k + 1) * Q.length)) ((k + 1) * Q.length))
    (hpe0 : parent (mTower Q d e (k + 2))
      (srow (mTower Q d e (k + 2)) ((k + 1) * Q.length)) ((k + 1) * Q.length)
      = k * Q.length) :
    rankDE
      (wd0 (A ++ mTower Q d e k)
        (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
          ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))) Q.length 0)
      (wd1 (A ++ mTower Q d e k)
        (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
          ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))) Q.length 0)
      < rankDE d e := by
  have hQ1 : 0 < Q.length := List.length_pos_iff.mpr hQne
  set B0 := Lift1 (shiftr01 (d * k) 0 Q) (e * k) with hB0
  set B1 := Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1)) with hB1
  set P := A ++ mTower Q d e k with hPdef
  have hB0len : B0.length = Q.length := by rw [hB0, Lift1_length, shiftr01_length]
  have hB1len : B1.length = Q.length := by rw [hB1, Lift1_length, shiftr01_length]
  have hBlen : (B0 ++ B1).length = Q.length + Q.length := by
    rw [List.length_append, hB0len, hB1len]
  set S := P ++ (B0 ++ B1).take (Q.length + 1) with hS
  have hSlen : S.length = P.length + (Q.length + 1) := by
    rw [hS, List.length_append, List.length_take, hBlen, Nat.min_eq_left (by omega)]
  have hlast : S.length - 1 = P.length + Q.length := by omega
  have hEl : ∀ i, entry S i (P.length + Q.length) = entry B1 i 0 := by
    intro i
    rw [hS, entry_append_right, Wset.entry_take (show Q.length < Q.length + 1 by omega),
      show Q.length = B0.length + 0 from by omega, entry_append_right]
  have hEr : ∀ i, entry S i P.length = entry B0 i 0 := by
    intro i
    have h := entry_append_right P ((B0 ++ B1).take (Q.length + 1)) i 0
    simp only [Nat.add_zero] at h
    rw [hS, h, Wset.entry_take (show (0 : ℕ) < Q.length + 1 by omega),
      entry_append_left _ _ (show (0 : ℕ) < B0.length by omega)]
  have hB1_0 : entry B1 0 0 = entry Q 0 0 + d * (k + 1) := by
    rw [hB1, entry0_Lift1, entry0_shiftr01 (by omega)]
  have hB1_1 : entry B1 1 0 = entry Q 1 0 + e * (k + 1) := by
    rw [hB1]
    show ((Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).getD 0 (0, 0, 0)).2.1 = _
    rw [block_getD (d := d) (e := e) (n := k + 1) hQ1, if_pos (le1_refl hQ1)]
  have hB1_2 : entry B1 2 0 = entry Q 2 0 := by
    rw [hB1]
    show ((Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).getD 0 (0, 0, 0)).2.2 = _
    rw [block_getD (d := d) (e := e) (n := k + 1) hQ1]
  have hB0_0 : entry B0 0 0 = entry Q 0 0 + d * k := by
    rw [hB0, entry0_Lift1, entry0_shiftr01 (by omega)]
  -- `S` の末尾列の `srow` は `mTower Q d e (k+2)` のブロック根の `srow` と同じ
  have hsS : srow S (S.length - 1)
      = srow (mTower Q d e (k + 2)) ((k + 1) * Q.length) := by
    rw [hlast]
    unfold srow
    rw [hEl 2, hEl 1, hB1_2, hB1_1,
      mTower_entry2_root (show k + 1 < k + 2 by omega) hQ1,
      entry1_mTower_blockRoot hQne d e (k + 2) (k + 1) (by omega)]
  rcases Nat.eq_zero_or_pos (srow (mTower Q d e (k + 2)) ((k + 1) * Q.length))
    with h0 | h1
  · -- `srow = 0` ⟹ `wd0 = wd1 = 0`
    have hw0 : wd0 P (B0 ++ B1) Q.length 0 = 0 := by
      unfold wd0; rw [← hS, hsS, h0, if_neg (by omega)]
    have hw1 : wd1 P (B0 ++ B1) Q.length 0 = 0 := by
      unfold wd1; rw [← hS, hsS, h0, if_neg (by omega)]
    rw [hw0, hw1]
    unfold rankDE
    rw [if_pos hd]
    split_ifs <;> omega
  · -- `srow = 1` ⟹ 親がブロック根なので `nextrel1` ⟹ `0 < e`
    have hs1 : srow (mTower Q d e (k + 2)) ((k + 1) * Q.length) = 1 := by
      have := blockRoot_srow_le_one (Q := Q) (d := d) (e := e) (n := k + 2)
        (k := k + 1) hQ1 (by omega) hz0
      omega
    have hpe1 := hpe0
    rw [hs1] at hpe1
    have hnr := parent_nextR hpM
    rw [hs1] at hnr
    rw [hpe1] at hnr
    unfold nextR at hnr
    rw [if_neg (by omega), if_pos rfl] at hnr
    have he : 0 < e := e_pos_of_nextrel1_blockRoots (by omega) (by omega) hQ1 hnr
    have hw1 : wd1 P (B0 ++ B1) Q.length 0 = 0 := by
      unfold wd1; rw [← hS, hsS, hs1, if_neg (by omega)]
    have hw0 : wd0 P (B0 ++ B1) Q.length 0 = d := by
      unfold wd0
      rw [← hS, hsS, hs1, if_pos (by omega), hlast, hEl 0, Nat.add_zero, hEr 0,
        hB1_0, hB0_0]
      have hmul : d * (k + 1) = d * k + d := Nat.mul_succ d k
      omega
    rw [hw0, hw1]
    unfold rankDE
    rw [if_pos he]
    split_ifs <;> omega


/-! ### 223.3 ★★★★ `d = 0` ならブロックの根は**必ず孤児**

`d = 0` のとき塔は行 0 を**触りません**。⟹ 第 `k` ブロックの `q` 列目の行 0 は `entry Q 0 q`。

**⟹ ★ `hr0` より、塔のどの列も行 0 は `entry Q 0 0` **以上**です。**
**⟹ ⟹ ブロックの根の行 0 は `entry Q 0 0` ちょうど ⟹ **`nextrel0` の始点になれる列が無い**。**
**⟹ ⟹ ⟹ `le0` の祖先が自分しか無い ⟹ 行 1・行 2 の親も持てない（`nextR_le0`）。**

> **⟹ ★★ `ZeroDOK` は**要りません**。`d = 0` は「常に孤児」で `snoc_orphan_W` に落ちます。** -/

theorem blockRoot_orphan_of_d_zero {Q : TrioSeq} {e n k i : ℕ}
    (hQ1 : 0 < Q.length) (hk : k < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) :
    ¬ hasParent (mTower Q 0 e n) i (k * Q.length) := by
  intro hp
  have hTlen : (mTower Q 0 e n).length = n * Q.length := mTower_length Q 0 e n
  have hroot : entry (mTower Q 0 e n) 0 (k * Q.length) = entry Q 0 0 := by
    have := entry0_mTower_block Q 0 e n k 0 hk hQ1
    rw [Nat.add_zero, Nat.zero_mul, Nat.add_zero] at this
    exact this
  -- 塔のどの列も行 0 は `entry Q 0 0` 以上
  have hall : ∀ c, c < (mTower Q 0 e n).length →
      entry Q 0 0 ≤ entry (mTower Q 0 e n) 0 c := by
    intro c hc
    rw [hTlen] at hc
    have hq : c % Q.length < Q.length := Nat.mod_lt _ hQ1
    have hk' : c / Q.length < n := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hc)
    have hdec : c / Q.length * Q.length + c % Q.length = c := Nat.div_add_mod' c Q.length
    have h := entry0_mTower_block Q 0 e n (c / Q.length) (c % Q.length) hk' hq
    rw [hdec, Nat.zero_mul, Nat.add_zero] at h
    rw [h]
    rcases Nat.eq_zero_or_pos (c % Q.length) with h0 | h0
    · rw [h0]
    · exact le_of_lt (hr0 _ h0 hq)
  have hnr := parent_nextR hp
  have hlt : parent (mTower Q 0 e n) i (k * Q.length) < k * Q.length :=
    nextR_index_lt hnr
  obtain ⟨-, hbM, hrtg⟩ := nextR_le0 hnr
  rcases hrtg.cases_tail with heq | ⟨c, -, hcb⟩
  · omega
  · have h1 := hcb.2.2.2.1
    have h2 := hall c hcb.1
    rw [hroot] at h1
    omega


/-- ⛔ **`Row2RootOrph`**: 底の根の行 2 が正なら、塔のブロック根は**行 2 の孤児**。

**機構（H12 §198 `not_nextrel2_blockRoots`）**: 行 2 は `shiftr01` / `Lift1` で**変わらない**
⟹ ブロック根どうしの行 2 は**等しい** ⟹ `nextrel2` の狭義増加が取れない。

**⟹ ★ R2 実測 **35,244 / 35,244（100%）**、対照 A 0.832% / 対照 B 17.632% で鳴る。**

⚠ **これを仮定すると `hz0` が `TowerP''` から落ちます**（親がある枝で対偶から導出できるので）。
**⟹ ⟹ ★ そして `HeredZ2core`（核）と `RootZ2`（消費側の `hz0`）が**まるごと消えます**。** -/
def Row2RootOrph : Prop :=
  ∀ (Q : TrioSeq) (d e n k : ℕ), 0 < Q.length → k < n → 0 < entry Q 2 0 →
    ¬ hasParent (mTower Q d e n) (srow (mTower Q d e n) (k * Q.length)) (k * Q.length)

/-! ### 223.6 ⛔⛔ **私の訂正: `ZeroDOK` の消滅は間違いでした**

§223.3 で「`d = 0` ならブロック根は**必ず孤児** ⟹ `snoc_orphan_W` で無料 ⟹ `ZeroDOK` は要らない」
と書きました。**⟹ ⛔ 「孤児」は**塔の中だけ**の話でした。**

**⟹ ★ H12 が**反対向き**を緑にしています（`hasParent0_prefix_blockRoot_iff_d_zero`）:**

    `d = 0` なら**全ブロック根は `Q` の根と**同じ列**を親に持つ**（その列は接頭辞 `A` の中）
    ⟹ `A` に `entry Q 0 0` より狭義に浅い列があれば、**ブロック根は親を持ちます**

**⟹ ⟹ ⛔ ですから `OrphOK0`（塔の中で孤児 ⟹ `A` つきでも孤児）は `d = 0` で**偽**です。**

**⟹ ★ 直しました:**

    `OrphOK0` に **`0 < d`** を足した
    `ZeroDOK`（`d = 0` の塔）を**戻した**
    `towerClosed_of_hered` は `d = 0` を `ZeroDOK` に流す（`0 < d` の枝だけ自分で扱う）

⚠ **§223.3 `blockRoot_orphan_of_d_zero` 自体は正しく、いまも使っています**
（`0 < d` の導出ではなく、`d = 0` を切り分ける根拠として §223.6 の散文に）。
**⟹ ⟹ 誤っていたのは「だから `ZeroDOK` が消える」という**散文の推論**でした。**

⚠ **教訓（今日 7 件目）: 「塔の中で真」を「接頭辞を付けても真」と書いた。**
**⟹ ★ `hbase` を消したとき（§208）と**同じ境界**です。接頭辞は毎回ここで効きます。** -/

/-! ### 223.2 ★★★★ `j = 0` の枝の `0 < e` なし版（§216 の差し替え） -/

open Classical in
theorem hsnoc_zero_noE {u : ℕ} {A Q : TrioSeq} {d e k : ℕ}
    (horph0 : OrphOK0) (hQne : Q ≠ []) (hdpos : 0 < d)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hrow2 : Row2RootOrph) (hz1 : ∀ q, q < Q.length → entry Q 2 q ≤ 1)
    (hIH : ∀ V d0 d1, TowerP'' V d0 d1 → towerMeas V d0 d1 < towerMeas Q d e →
      ∀ A', A' ∈ W u → A' ++ V ∈ W u → ∀ m, A' ++ mTower V d0 d1 m ∈ W u)
    (hpre : ∀ p, p ≤ Q.length →
      A ++ mTower Q d e k
        ++ (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
            ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take p ∈ W u)
:
    A ++ mTower Q d e (k + 1)
      ++ (Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take 1 ∈ W u := by
  have hQ1 : 0 < Q.length := List.length_pos_iff.mpr hQne
  set B0 := Lift1 (shiftr01 (d * k) 0 Q) (e * k) with hB0
  set B1 := Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1)) with hB1
  set P := A ++ mTower Q d e k with hPdef
  set T := mTower Q d e (k + 1) ++ B1.take 1 with hTdef
  have hB0len : B0.length = Q.length := by rw [hB0, Lift1_length, shiftr01_length]
  have hB1len : B1.length = Q.length := by rw [hB1, Lift1_length, shiftr01_length]
  have hBlen : (B0 ++ B1).length = Q.length + Q.length := by
    rw [List.length_append, hB0len, hB1len]
  have hPlen : P.length = A.length + k * Q.length := by
    rw [hPdef, List.length_append, mTower_length]
  have hsucc : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
  have hre : A ++ mTower Q d e (k + 1) ++ B1.take 1
      = P ++ (B0 ++ B1).take (Q.length + 1) := by
    rw [hPdef, hB0, hB1, prefix_mTower_take_reassoc A Q d e k 1, List.append_assoc]
  have hassoc : A ++ mTower Q d e (k + 1) ++ B1.take 1 = A ++ T := by
    rw [hTdef, List.append_assoc]
  set S := P ++ (B0 ++ B1).take (Q.length + 1) with hS
  have hSlen : S.length = P.length + (Q.length + 1) := by
    rw [hS, List.length_append, List.length_take, hBlen, Nat.min_eq_left (by omega)]
  have hSAT : S = A ++ T := by rw [← hre]; exact hassoc
  have hTlen : T.length = (k + 1) * Q.length + 1 := by
    rw [hTdef, List.length_append, mTower_length, List.length_take, hB1len,
      Nat.min_eq_left (by omega)]
  have hlastAT : (A ++ T).length - 1 = A.length + (k + 1) * Q.length := by
    rw [List.length_append, hTlen]; omega
  have hTeq : T = (mTower Q d e (k + 2)).take ((k + 1) * Q.length + 1) := by
    rw [hTdef]; exact tower_snoc_root_eq_take Q d e k
  have hTlen2 : (mTower Q d e (k + 2)).length = (k + 2) * Q.length :=
    mTower_length Q d e (k + 2)
  have hsucc2 : (k + 2) * Q.length = (k + 1) * Q.length + Q.length :=
    Nat.succ_mul (k + 1) Q.length
  have hle : (k + 1) * Q.length + 1 ≤ (mTower Q d e (k + 2)).length := by omega
  have hsrowT : srow T ((k + 1) * Q.length)
      = srow (mTower Q d e (k + 2)) ((k + 1) * Q.length) := by
    rw [hTeq]; exact srow_take (by omega)
  by_cases hpM : hasParent (mTower Q d e (k + 2))
      (srow (mTower Q d e (k + 2)) ((k + 1) * Q.length)) ((k + 1) * Q.length)
  · -- ★ 親がある ⟹ `d = 0` ではありえない（§223.3）
    have hd : 0 < d := hdpos
    have hz0 : entry Q 2 0 = 0 := by
      by_contra hc
      exact hrow2 Q d e (k + 2) (k + 1) hQ1 (by omega) (by omega) hpM
    have hpT : hasParent T (srow T ((k + 1) * Q.length)) ((k + 1) * Q.length) := by
      rw [hsrowT, hTeq]
      exact (hasParent_take hle (by omega)).mpr hpM
    have hpTe : parent T (srow T ((k + 1) * Q.length)) ((k + 1) * Q.length)
        = parent (mTower Q d e (k + 2))
          (srow (mTower Q d e (k + 2)) ((k + 1) * Q.length)) ((k + 1) * Q.length) := by
      rw [hsrowT] at hpT ⊢
      rw [hTeq] at hpT ⊢
      exact parent_take hle (by omega) hpT
    have hparAT : hasParent (A ++ T) (srow T ((k + 1) * Q.length))
        (A.length + (k + 1) * Q.length) := hasParent_append_right_of _ _ hpT
    have hsrowAT : srow (A ++ T) (A.length + (k + 1) * Q.length)
        = srow T ((k + 1) * Q.length) := srow_append_right A T _
    have hpar : hasParent S (srow S (S.length - 1)) (S.length - 1) := by
      rw [hSAT, hlastAT, hsrowAT]; exact hparAT
    set par := parent S (srow S (S.length - 1)) (S.length - 1) with hpardef
    have hpareq : par = A.length
        + parent (mTower Q d e (k + 2))
          (srow (mTower Q d e (k + 2)) ((k + 1) * Q.length)) ((k + 1) * Q.length) := by
      rw [hpardef, hSAT, hlastAT, hsrowAT, parent_append_right_of A T hpT, hpTe]
    have hge := blockRoot_parent_ge_noE (Q := Q) (d := d) (e := e) (n := k + 2)
      (k := k) hQne hd (by omega) hr0 hz0 hpM
    have hltAT : par < A.length + (k + 1) * Q.length := by
      rw [hpardef]
      have := nextR_index_lt (parent_nextR hpar)
      rw [hSAT, hlastAT] at this ⊢
      exact this
    set p := par - P.length with hpdef
    have hplt : p < Q.length := by omega
    have hpe : par = P.length + p := by omega
    have hsle : srow S (S.length - 1) ≤ 1 := by
      rw [hSAT, hlastAT, hsrowAT, hsrowT]
      exact blockRoot_srow_le_one hQ1 (show k + 1 < k + 2 by omega) hz0
    refine hsnoc_zero_of_parent hd hIH hQ1 (hpre Q.length le_rfl) (hpre p (by omega))
      hplt hpar hpe hz1 ?_
    intro hp0
    rw [hp0]
    refine hrank_blockRoot_noE (A := A) hQne hd hz0 hpM ?_
    omega
  · -- ★ 孤児 ⟹ `snoc_orphan_W`
    have hnpT : ¬ hasParent T (srow T ((k + 1) * Q.length)) ((k + 1) * Q.length) := by
      rw [hsrowT, hTeq]
      intro hc
      exact hpM ((hasParent_take hle (by omega)).mp hc)
    have hnp := horph0 A Q d e k hdpos hnpT
    have hB1t : B1.take 1 = [B1.getD 0 (0, 0, 0)] := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, List.take_add_one, List.take_zero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    have hCmem : A ++ mTower Q d e (k + 1) ∈ W u := by
      have h := hpre Q.length le_rfl
      rw [show (B0 ++ B1).take Q.length = B0 from by
        rw [List.take_append, List.take_of_length_le (by omega), hB0len,
          Nat.sub_self, List.take_zero, List.append_nil]] at h
      rw [hPdef] at h
      rw [show mTower Q d e (k + 1) = mTower Q d e k ++ B0 from by
        rw [mTower_succ, ← hB0], ← List.append_assoc]
      exact h
    have hClen : (A ++ mTower Q d e (k + 1)).length = A.length + (k + 1) * Q.length := by
      rw [List.length_append, mTower_length]
    have hCne : A ++ mTower Q d e (k + 1) ≠ [] := by
      intro hc
      have : (A ++ mTower Q d e (k + 1)).length = 0 := by rw [hc]; rfl
      omega
    have hsp : A ++ mTower Q d e (k + 1) ++ B1.take 1
        = (A ++ mTower Q d e (k + 1)) ++ [B1.getD 0 (0, 0, 0)] := by rw [hB1t]
    rw [hsp]
    refine snoc_orphan_W _ hCmem hCne ?_
    rw [hClen, ← hsp, hassoc]
    exact hnp

/-! ### 220.2c ⛔⛔ `0 < d` / `0 < e` は**遺伝しません**（今日いちばん重い発見）

`oper` の作る新しいリフト量は（§198 の逐語）

    `srow = 2` … `wd0` も `wd1` も正になりうる
    **`srow = 1` … `wd1 = 0`**（`¬ 1 < 1`）
    **`srow = 0` … `wd0 = wd1 = 0`**

**⟹ ⛔ ★ つまり `0 < e` は `srow ≤ 1` の段で**必ず**破れます。「ときどき」ではありません。**
**⟹ ⟹ `0 < d` も `srow = 0` の段で必ず破れます。**

**⟹ ★ ですからこの 2 つは `TowerP''` から**外し**、**別ルートの仮定**にします:**

    `d = 0` … 行 0 のリフトが無い塔（`mTower Q 0 e n`）
    `e = 0` … 行 1 のリフトが無い塔（`mTower Q d 0 n`）
             ⟹ §112 `MTowerClosedS0 = ShiftTowerClosedS`（**プロジェクト既知の対象**）

⚠ **これは「穴が増えた」のではなく「穴の位置が正しくなった」ものです。**
**⟹ 私は `TowerP''` に `0 < d` / `0 < e` を入れたまま「遺伝は易しいはず」と書いていました。**
**⟹ ⟹ ⛔ **誤り**でした。⟹ 必ず破れます。** -/

/-! ### 220.3 測度の強帰納（底のブロックをもらう版） -/

theorem tower_of_measure_step2 {u : ℕ}
    (P : TrioSeq → ℕ → ℕ → Prop) (meas : TrioSeq → ℕ → ℕ → ℕ)
    (hstep : ∀ Q d e, P Q d e →
      (∀ V d0 d1, P V d0 d1 → meas V d0 d1 < meas Q d e →
        ∀ A, A ∈ W u → A ++ V ∈ W u → ∀ m, A ++ mTower V d0 d1 m ∈ W u) →
      ∀ A, A ∈ W u → A ++ Q ∈ W u → ∀ n, A ++ mTower Q d e n ∈ W u) :
    ∀ Q d e, P Q d e → ∀ A, A ∈ W u → A ++ Q ∈ W u →
      ∀ n, A ++ mTower Q d e n ∈ W u := by
  have key : ∀ s Q d e, meas Q d e ≤ s → P Q d e →
      ∀ A, A ∈ W u → A ++ Q ∈ W u → ∀ n, A ++ mTower Q d e n ∈ W u := by
    intro s
    induction s with
    | zero =>
      intro Q d e hle hP A hA hAQ n
      exact hstep Q d e hP
        (fun _ _ _ _ hlt _ _ _ _ => absurd hlt (by omega)) A hA hAQ n
    | succ s ih =>
      intro Q d e hle hP A hA hAQ n
      exact hstep Q d e hP
        (fun V d0 d1 hPV hlt A' hA' hAV m =>
          ih V d0 d1 (by omega) hPV A' hA' hAV m) A hA hAQ n
  intro Q d e hP A hA hAQ n
  exact key (meas Q d e) Q d e (le_refl _) hP A hA hAQ n

/-! ### 220.4 ★★★★★ **最終定理** -/

open Classical in
theorem towerClosed_of_hered {u : ℕ} (horph : OrphOK) (horph0 : OrphOK0)
    (hzd : ZeroDOK u) (hrow2 : Row2RootOrph) :
    ∀ Q d e, TowerP'' Q d e → ∀ A, A ∈ W u → A ++ Q ∈ W u →
      ∀ n, A ++ mTower Q d e n ∈ W u := by
  refine tower_of_measure_step2 (u := u) TowerP'' towerMeas ?_
  intro Q d e hP hIH A hA hAQ
  have hQne := ne_of_TowerP'' hP
  have hQ1 : 0 < Q.length := List.length_pos_iff.mpr hQne
  have hr0 := hr0_of_TowerP'' hP
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0; exact hzd A Q e hP hA hAQ
  refine prefixTowerClosed_of_snocStepStrong1 hA hAQ ?_
  intro n j hn hj hall
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · -- ★ `j = 0`: `n = k+1`
    subst hj0
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hpre : ∀ p, p ≤ Q.length →
        A ++ mTower Q d e k
          ++ (Lift1 (shiftr01 (d * k) 0 Q) (e * k)
              ++ Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))).take p ∈ W u := by
      intro p hp
      exact prefix_block_take_mem hp (by simpa using hall 0 (le_refl 0))
    exact hsnoc_zero_noE horph0 hQne hdpos hr0 hrow2 (hz1_of_TowerP'' hP) hIH hpre
  · -- ★ `j ≥ 1`
    set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
    have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
    by_cases hloc : hasParent (B.take (j + 1)) (srow (B.take (j + 1)) j) j
    · exact hsnoc_pos hP hIH hj hj1 hloc (parent_bound_pos hj hloc) hall
    · -- ⟹ ブロックの中で孤児 ⟹ `OrphOK` で全体でも孤児 ⟹ `snoc_orphan_W`
      have hnp := horph A Q d e n j hj1 hj hloc
      have hBt : B.take (j + 1) = B.take j ++ [B.getD j (0, 0, 0)] := by
        rw [List.take_add_one]
        congr 1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        rfl
      have hsplit : A ++ mTower Q d e n ++ B.take (j + 1)
          = (A ++ mTower Q d e n ++ B.take j) ++ [B.getD j (0, 0, 0)] := by
        rw [hBt, ← List.append_assoc]
      have hClen : (A ++ mTower Q d e n ++ B.take j).length
          = (A ++ mTower Q d e n).length + j := by
        rw [List.length_append, List.length_take, hBlen, Nat.min_eq_left (by omega)]
      have hCne : A ++ mTower Q d e n ++ B.take j ≠ [] := by
        intro hc
        have : (A ++ mTower Q d e n ++ B.take j).length = 0 := by rw [hc]; rfl
        omega
      rw [hsplit]
      refine snoc_orphan_W _ (hall j (le_refl j)) hCne ?_
      rw [hClen, ← hsplit]
      exact hnp

/-! ### 220.5 ⟹ ★★★★★★ **残る義務は 3 本**（`ZeroDOK` も消えました）

```lean
theorem towerClosed_of_hered {u : ℕ} (horph : OrphOK) (horph0 : OrphOK0) (hz2 : HeredZ2) :
    ∀ Q d e, TowerP'' Q d e → ∀ A, A ∈ W u → A ++ Q ∈ W u →
      ∀ n, A ++ mTower Q d e n ∈ W u
```

    **`OrphOK`**  … `j ≥ 1` でブロックの中で孤児 ⟹ 全体でも孤児（**R2 実測 100%、374043**）
    **`OrphOK0`** … `j = 0` で**塔の中**で孤児 ⟹ 接頭辞を付けても孤児
    **`HeredZ2`** … 窓の根の行 2 が 0（＝ (H2')。**R2 実測 98.4〜99.8%**）

**⟹ ★ `ZeroEOK` は H12 の (q3b) で、`ZeroDOK` は §223.3 で消えました。**
**⟹ ⟹ `0 < d` / `0 < e` は**仮定せず、必要なときだけ導出**します:**

    `0 < d` … 親があるブロック根から（§223.3 の対偶）
    `0 < e` … 親がブロック根のとき `nextrel1` から（§199）

### 220.6 ★★★ 遺伝の義務は **`hz0(V)` 1 本**

`TowerP''` は `0 < |Q|` / `hr0` / `hz0` の 3 本で、

    `0 < |V|` … §221 `wnd_pos`（**無料**）
    `hr0(V)`  … §221 `hr0_wnd`（**無料**）
    `hz0(V)`  … ⛔ **`HeredZ2`**（唯一の核）

⚠ **教訓 14**: **3 本のどれも証明していません。** -/

/-! ## 222. ★★★★★★★★★★ **消費側への接続** —— `MTowerClosedS` まで繋ぎます

`MTowerClosedS`（`L105Cap:5618`）は

    `∀ u d e n Q, Q ∈ W u → (∀ j, 1 ≤ j → j < |Q| → entry Q 0 0 < entry Q 0 j) → mTower Q d e n ∈ W u`

**⟹ ★ §220 を `A = []` で使うと、足りないのは `entry Q 2 0 = 0` **1 つだけ**です。**

    `[] ∈ W u` … `W_nil` ✅
    `[] ++ Q = Q ∈ W u` … **消費側の仮定そのもの** ✅
    `hr0` … **消費側の仮定そのもの** ✅
    `0 < |Q|` … `|Q| = 0` なら `mTower = []` ✅
    `entry Q 2 0 = 0` … ⛔ **供給されません**（team-lead: `z = 1` で破れる） -/

/-- ⛔ **消費側の `z < 2`**（行 2 ≤ 1）。プロジェクトの断片の前提そのもの。 -/
def RootZ1 : Prop :=
  ∀ (u : ℕ) (Q : TrioSeq), Q ∈ W u → ∀ q, q < Q.length → entry Q 2 q ≤ 1

/-- ⛔ **消費側の `hz0`**（`z = 0` に相当）。H12 の `hz0_of_zle1` が効くはずのところ。 -/
def RootZ2 : Prop :=
  ∀ (u : ℕ) (Q : TrioSeq), Q ∈ W u →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) → entry Q 2 0 = 0

theorem mTower_nil (d e n : ℕ) : mTower ([] : TrioSeq) d e n = [] :=
  List.eq_nil_of_length_eq_zero (by rw [mTower_length]; simp)

open Classical in
/-- ★★★★★ **`MTowerClosedS` は 5 本から出ます。** -/
theorem mTowerClosedS_of_residues (horph : OrphOK) (horph0 : OrphOK0)
    (hzd : ∀ u, ZeroDOK u) (hrow2 : Row2RootOrph) (hrz1 : RootZ1) :
    MTowerClosedS := by
  intro u d e n Q hQ hs
  rcases Nat.eq_zero_or_pos Q.length with h0 | hpos
  · have hnil : Q = [] := List.eq_nil_of_length_eq_zero h0
    subst hnil
    rw [mTower_nil]
    exact W_nil u
  · have hP : TowerP'' Q d e :=
      ⟨hpos, fun l hl0 hl1 => hs l hl0 hl1, hrz1 u Q hQ⟩
    have h := towerClosed_of_hered (u := u) horph horph0 (hzd u) hrow2 Q d e hP []
      (W_nil u) (by simpa using hQ) n
    simpa using h

/-! ### 222.1 ⟹ ★★★★★★ **`MTowerClosedS` は 5 本の式です**

```lean
theorem mTowerClosedS_of_residues (horph : OrphOK) (horph0 : OrphOK0)
    (hzd : ∀ u, ZeroDOK u) (hrow2 : Row2RootOrph) (hrz1 : RootZ1) : MTowerClosedS
```

    **(1) `OrphOK`**（`j ≥ 1`）… ブロックの中で孤児 ⟹ 全体でも孤児
         ⟹ ★ **R2 実測 100.0000%**（1,457,772、4 種の `A`、対照 7〜14%）
    **(2) `OrphOK0`**（`j = 0`、**`0 < d`**）… 塔の中で孤児 ⟹ 接頭辞つきでも孤児
         ⚠ **`0 < d` は必須**（§223.6。`d = 0` では H12 の定理が反例）
    **(3) `ZeroDOK`** … `d = 0` の塔 ⟹ `PrefixCopies`（`L53Subst:3599`）の領域
    **(4) `Row2RootOrph`** … 底の根の行 2 が正なら、塔のブロック根は**行 2 の孤児**
         ⟹ ★ **R2 実測 35,244 / 35,244（100%）**、対照 0.83% / 17.63% で鳴る
    **(5) `RootZ1`** … 消費側の底の行 2 が**全部 ≤ 1**（＝ `z < 2` の断片そのもの、`zle1` 承認ずみ）

### 222.2 ★★★ `HeredZ2`（核）と `RootZ2` が**消えました**

**`TowerP''` から `hz0`（`entry Q 2 0 = 0`）を落としたからです。⟹ 落とせた理由:**

    `hz0` を使っていたのは **`j = 0` の枝**（ブロック根の `srow ≤ 1`）だけ
    ⟹ ★ `Row2RootOrph` の**対偶**で「親があるなら `entry Q 2 0 = 0`」が**導出**できる
    ⟹ ⟹ **仮定にせず、使う場所で導く**（`0 < d` / `0 < e` と同じ手、今日 3 回目）

**⟹ ★★ `TowerP''` は **3 本**になりました: `0 < |Q|` ／ `hr0` ／ `hz1`（行 2 ≤ 1）。**
**⟹ ⟹ ★ そして **3 本とも窓に遺伝します**（`wnd_pos` / `hr0_wnd` / `entry2_wnd`、全部緑）。**
**⟹ ⟹ ⟹ ★★★ **遺伝の義務は 0 になりました**。**

### 222.3 ★ 消えたもの（今日）

    `hbase`（§208）／ `hd0e`・`hlp`（未使用）／ `h2out`・`h1out`（`OrphOK` が肩代わり）
    `0 < d`・`0 < e`（**導出に変えた**）／ `ZeroEOK`（H12 の (q3b)）
    `hr0(V)` の遺伝（§221）／ **`hz0`・`HeredZ2`・`RootZ2`**（§225 `Row2RootOrph`）

⚠ **`ZeroDOK` は §223.3 で消したつもりでしたが §223.6 で**戻しました**（私の誤り）。**

⚠ **教訓 14**: **5 本のどれも証明していません。**
**とくに `Row2RootOrph` は R2 の実測 100% ですが、Lean では 1 行も書いていません。** -/

/-! ### 225.1 ✅ `Row2RootOrph` の **`k = 0` は無条件で真**（下限の確認）

**索引を引く前に、まず自分で確かめられる部分を切り出します。**
**⟹ ★ ブロック 0 の根は添字 0 なので、`nextR` の始点（`< 0`）が存在しません。** -/

theorem no_hasParent_zero {M : TrioSeq} {i : ℕ} : ¬ hasParent M i 0 := by
  intro hp
  have := nextR_index_lt (parent_nextR hp)
  omega

/-- ★ `Row2RootOrph` の `k = 0` の場合。 -/
theorem row2RootOrph_zero {Q : TrioSeq} {d e n : ℕ} :
    ¬ hasParent (mTower Q d e n) (srow (mTower Q d e n) (0 * Q.length)) (0 * Q.length) := by
  rw [Nat.zero_mul]
  exact no_hasParent_zero

/-! ### 225.2 ⚠ `k ≥ 1` は**書けていません**。反例の形も作れませんでした

**必要なのは「`entry Q 2 0 > 0` なら `nextrel2 M a (k*|Q|)` が取れない」です。**

    `srow = 2` は無料（行 2 は `shiftr01` / `Lift1` で不変 ⟹ `entry M 2 (k*|Q|) = entry Q 2 0 > 0`）
    `nextrel2` は **`entry M 2 a < entry Q 2 0`** と **`le1 M a (k*|Q|)`** を要求
    ⟹ `zle1` の下では `entry Q 2 0 = 1` ⟹ `entry M 2 a = 0`
    ⟹ ⛔ **残るのは「行 2 が 0 の列が、ブロック根に `le1` で届かない」**

**⟹ ⚠ ★ ここは H12 の `not_nextrel2_blockRoots`（§198）では足りません。**
**§198 は「**ブロック根どうし**」だけで、`a` が**非根**の場合を潰していません。**

⚠ **反例の形も 15 分では作れませんでした**（教訓 45 の逆で、作れないことは証拠になりません）。
**⟹ ★ R2 の 35,244 / 35,244（対照 0.83% / 17.63% で鳴る）だけが根拠です。**
**⟹ ⟹ H12 に (A) として振りました。** -/

end L106
end TRIO
