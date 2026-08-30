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

/-! ## 236. ★★★★★★★★ (C1) を見て分かったこと: **`hhigh` は必要条件ではありません**

R2 の核（型 B）を、ブロックの中で 1 列ずつ追いました。

    `V = [(x0, a, 0), (x1, 0, 0), (x2, b, 0)]`、`b ≤ a`、`x0 < x1 < x2`
    ⟹ 第 1 列・第 2 列は**錐の外**（行 1 が根 `a` 以下）⟹ 持ち上がらない
    ⟹ ★ 第 `k` ブロック ＝ `[(x0+d0k, a+e0k, 0), (x1+d0k, 0, 0), (x2+d0k, b, 0)]`

## ★★★ そして **`hloc` は全列で成り立ちます**

    **第 1 列**（行 1 も行 2 も 0）… `srow = 0` ⟹ §154 `block_blockParent_row0`（`hr0` だけ）✅
    **第 2 列**（行 1 ＝ `b`）…
      `b = 0` ⟹ `srow = 0` ⟹ 同上 ✅
      **`b > 0`** ⟹ `srow = 1`、**錐の外** ⟹ §172 は `hhigh : a < b` を要求 ⟹ ⛔ **`b ≤ a` で偽**
      ⟹ ★★★ **ですが親は居ます**: **第 1 列**（行 1 ＝ `0 < b`、隣接なので `le0` ✓、
        最小性は間に列が無いので**空虚**）⟹ `Wset.hasParent_one_of` で **`hloc` ✅**

> **⟹ ★★★★ ですから §172 の `hhigh`（**根**より行 1 が上）は**十分条件であって必要条件ではありません**。**
> **⟹ ⟹ ★ 本当に要るのは「**`le0` の祖先のどれかが行 1 で小さい**」だけです。**

## ⟹ ★★ 設計への含意

**`OrphOK`（`hnbQ` が要る）が発火するのは **`hloc` が破れるとき**だけです。**
**⟹ ★ ですから **`hloc` が全列で立つなら `hnbQ` は要りません**。**
**⟹ ⟹ ★★ そして核の形（型 B）では **`hloc` が全列で立ちます**（上）。**
**⟹ ⟹ ⟹ ★★★ **`h1out` / `hnbQ` は、どちらも「`hloc` を出すための十分条件」に過ぎませんでした**。** -/

/-- ★★ **`le0` の祖先に行 1 が小さい列が 1 つでもあれば `hloc`**（`hasParent_one_of` の言い換え）。
⟹ §172 の `hhigh`（根と比較）より**ずっと弱い**。 -/
theorem block_hasParent_one_of_witness {Q : TrioSeq} {d e n j y : ℕ}
    (hj : j < Q.length) (hyj : y < j)
    (hle0 : le0 ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) y j)
    (hlt : entry ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 1 y
      < entry ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 1 j) :
    hasParent ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 1 j := by
  have hBlen : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length = Q.length := by
    rw [Lift1_length, shiftr01_length]
  have hlen : ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length = j + 1 := by
    rw [List.length_take, hBlen, Nat.min_eq_left (by omega)]
  exact hasParent_one_of (by omega) hyj hle0 hlt

/-! ### 236.1 ⟹ ★★★ **正しい条件は「`hloc` が立つ」そのものです**

**今日ずっと追ってきた条件の系列を並べます:**

    `hbase`（`entry Q 0 0 = 0`）… ⛔ 遺伝 **0%**（§207 で証明）
    `rsum` … ⛔ 遺伝 **0%**（§227 で証明）
    `h1out`（錐の外の列が**根**より行 1 で上）… ⛔ H12 `blocker_of_large_k` で **必ず壊れる**
    `hnbQ`（全列が根より行 1 で上）… ⛔ **核の形（型 B）で偽**（§235）
    ★★★ **`hloc`（ブロックの中に親がいる）** … ⟹ **核の形でも立ちます**（上）

**⟹ ★ **前の 4 つはどれも「`hloc` を出すための十分条件」**でした。**
**⟹ ⟹ ★★ ⟹ **`hloc` そのものを不変量にする**のが正しい設計だと思います。**

⚠ **教訓 14**: 上は**核の形について確かめただけ**です。
**「`hloc` が一般に遺伝する」は**測っても証明してもいません**。**
**⟹ ★ R2 に **(LOCHER)**「窓 `V` の全列で `hloc` が立つか」を測ってもらう必要があります。**

⚠ **そして H12 の実測（`hloc` は錐の外の列で 68.8% 破れる、15944/23188）と
矛盾するように見えます。⟹ ★ ですが H12 の母集団は**一様な箱の `Q`**で、
**核の形（型 B）とは別**です。⟹ ⟹ 母集団を揃えて測り直す必要があります。** -/

/-! ### 236.2 ★★★★ `hloc`（行 1）を **`Q` の言葉・`n` に依らない形**に落とします

§236 で「要るのは **`le0` の祖先のどれかが行 1 で小さい**」と分かりました。
**⟹ ★ それを `Q` の言葉に落とすと、`e*n` が消える条件が見えます。**

`entry (block) 1 x = entry Q 1 x + (if le1 Q 0 x then e*n else 0)` なので:

| 証人 `y` | 的 `j` | ブロックでの比較 | `n` |
|---|---|---|---|
| 錐の中 | 錐の中 | `entry Q 1 y < entry Q 1 j`（両辺 `+e*n`）| ★ **消える** |
| 錐の外 | 錐の外 | `entry Q 1 y < entry Q 1 j` | ★ **消える** |
| 錐の外 | 錐の中 | `entry Q 1 y < entry Q 1 j + e*n` | ★ **緩む**（`Q` の条件で十分） |
| **錐の中** | **錐の外** | `entry Q 1 y + e*n < entry Q 1 j` | ⛔ **`n` 依存** |

**⟹ ★★★ ですから **「証人が錐の中なら的も錐の中」**（`le1 Q 0 y → le1 Q 0 j`）を付ければ、
**`n` が完全に消えます**。**

**⟹ ⟹ ★ そして核の形（型 B）では、証人（第 1 列）も的（第 2 列）も**錐の外**なので
この条件を**満たします**。⟹ ⟹ **核の形が通ります**。** -/

open Classical in
theorem block_hasParent_one_of_Q_witness {Q : TrioSeq} {d e n j y : ℕ}
    (hj : j < Q.length) (hyj : y < j)
    (hle0Q : le0 Q y j)
    (hlt : entry Q 1 y < entry Q 1 j)
    (hcls : le1 Q 0 y → le1 Q 0 j) :
    hasParent ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 1 j := by
  set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
  have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
  have hE1 : ∀ x, x < Q.length →
      entry B 1 x = entry Q 1 x + (if le1 Q 0 x then e * n else 0) := by
    intro x hx
    show (B.getD x (0, 0, 0)).2.1 = _
    rw [hB, block_getD hx]
  have hle0B : le0 (B.take (j + 1)) y j := by
    refine (le0_take (by omega) (by omega)).mpr ?_
    rw [hB]
    exact Wset.le0_Lift1.mpr (le0_shiftr01.mpr hle0Q)
  refine block_hasParent_one_of_witness (d := d) (e := e) (n := n) hj hyj hle0B ?_
  rw [Wset.entry_take (X := B) (l := j + 1) (i := 1) (j := y) (by omega),
    Wset.entry_take (X := B) (l := j + 1) (i := 1) (j := j) (by omega),
    hE1 y (by omega), hE1 j hj]
  by_cases hy : le1 Q 0 y
  · rw [if_pos hy, if_pos (hcls hy)]; omega
  · rw [if_neg hy]
    split_ifs <;> omega

/-! ### 236.3 ⟹ ★★★ **`hlocQ`: `Q` だけの、`n` に依らない条件**

    **`hlocQ Q` … ∀ j ≥ 1, `srow` が 1 のとき
      ∃ y < j, `le0 Q y j` ∧ `entry Q 1 y < entry Q 1 j` ∧ (`le1 Q 0 y → le1 Q 0 j`)**

**⟹ ★ 行 0 は §154（`hr0` だけ）、行 2 は §173（`Q.take (j+1)` に落ちる）。**
**⟹ ⟹ ★★ ですから **`hloc` は `Q` の言葉で書けます**。⟹ **`d, e, n` が消えます**。**

**⟹ ⟹ ⟹ ★★★ そして核の形（型 B）は `y = 1`（第 1 列、行 1 ＝ 0、錐の外）で満たします:**

    `le0 V 1 2` … 隣接（行 0 が狭義増加）✅
    `entry V 1 1 = 0 < b = entry V 1 2` ✅（`b > 0` のとき）
    `le1 V 0 1 → le1 V 0 2` … 前件が偽（第 1 列は錐の外）⟹ **空虚に真** ✅

⚠ **教訓 14**: **`hlocQ` の遺伝は測っても証明してもいません**。
**⟹ ★ ですが `hbase` / `rsum` / `h1out` / `hnbQ` と違い、**核の形で偽になりません**。**
**⟹ ⟹ R2 に (LOCHER) として測ってもらう価値があります。** -/


/-! ## 237. ★★★★★★★★★★ **`hlocQ` を定義して、`hloc` を全列で出します**

§236.2 で `hloc`（行 1）が `Q` の言葉・`n` 非依存で書けると分かりました。
**⟹ ★ 行 0（§154）・行 2（§173）と合わせて、**3 行そろえます**。**

⚠ **1 つ確認しました**: ブロックの `srow` が 1 になるのは
**`entry Q 2 j = 0` かつ `entry Q 1 j > 0`** のとき**だけ**です（`n` に依りません）。

    `j` が**錐の中** ⟹ `le1_entry1_lt` で `entry Q 1 0 < entry Q 1 j` ⟹ **`entry Q 1 j > 0`**
    `j` が**錐の外** ⟹ 持ち上がらないので `entry (block) 1 j = entry Q 1 j`

**⟹ ★ ですから `srow` の判定は `Q` だけで決まります。** -/

/-- ★★★ **`hlocQ`**: 「ブロックの中に親がいる」を `Q` の言葉で書いたもの（`d, e, n` に依らない）。 -/
def hlocQ (Q : TrioSeq) : Prop :=
  ∀ j, 0 < j → j < Q.length →
    (0 < entry Q 2 j → hasParent (Q.take (j + 1)) 2 j) ∧
    (entry Q 2 j = 0 → 0 < entry Q 1 j →
      ∃ y, y < j ∧ le0 Q y j ∧ entry Q 1 y < entry Q 1 j ∧ (le1 Q 0 y → le1 Q 0 j))

open Classical in
/-- ★★★★★ **`hlocQ` ⟹ ブロックの全列に親がいる**（`hloc` が全列で立つ）。 -/
theorem block_hasParent_all_of_hlocQ {Q : TrioSeq} {d e n j : ℕ}
    (hj : j < Q.length) (hj1 : 0 < j)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (h : hlocQ Q) :
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
  obtain ⟨h2, h1⟩ := h j hj1 hj
  unfold srow
  by_cases h2p : 0 < entry (B.take (j + 1)) 2 j
  · rw [if_pos h2p]
    rw [hE2] at h2p
    exact block_blockParent_row2' hj (h2 h2p)
  · by_cases h1p : 0 < entry (B.take (j + 1)) 1 j
    · rw [if_neg h2p, if_pos h1p]
      rw [hE2] at h2p
      -- ★ `entry Q 1 j > 0` を出す（錐の中なら `le1_entry1_lt`、外なら直接）
      have hQ1j : 0 < entry Q 1 j := by
        by_cases hc : le1 Q 0 j
        · have := le1_entry1_lt hc (show (0 : ℕ) ≠ j from by omega)
          omega
        · rw [hE1, if_neg hc, Nat.add_zero] at h1p
          exact h1p
      obtain ⟨y, hyj, hle0, hlt, hcls⟩ := h1 (by omega) hQ1j
      exact block_hasParent_one_of_Q_witness (d := d) (e := e) (n := n)
        hj hyj hle0 hlt hcls
    · rw [if_neg h2p, if_neg h1p]
      exact block_blockParent_row0 hj hj1 hr0

/-! ### 237.1 ⟹ ★★★ **`OrphOK` の枝が発火しなくなります**

`towerClosed_of_hered` の `j ≥ 1` は `by_cases hloc` で 2 分岐していました。
**⟹ ★ `hlocQ` があれば **`hloc` は常に真** ⟹ **`¬hloc` の枝が空**になります。**
**⟹ ⟹ ★★ ですから **`OrphOK` も `orphOK_proved` も `hnbQ` も要りません**。**

⚠ **教訓 14**: `hlocQ` の**遺伝**は測っても証明してもいません。
**⟹ ★ ですが `hbase` / `rsum` / `h1out` / `hnbQ` と違い、**核の形（型 B）で偽になりません**。** -/

/-! ### 211.1 ⟹ ★★★ **`TowerP''`**: 遺伝させるべき条件が**これで全部**です

**⟹ ★ `hstep` に渡す親の位置の前提が**完全に消えました**。**
**⟹ ⟹ 残るのは「この 6 本が窓 `V` に遺伝するか」だけです。** -/

/-- ★★★ 遺伝させるべき条件の**最終形**（親の位置はもう前提に出てきません）。 -/
def TowerP'' (Q : TrioSeq) (d e : ℕ) : Prop :=
  0 < Q.length ∧
    (∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) ∧
    (∀ q, q < Q.length → entry Q 2 q ≤ 1) ∧
    entry Q 2 0 = 0 ∧
    hlocQ Q ∧
    (d = 0 → e = 0)

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
    ∀ q, q < Q.length → entry Q 2 q ≤ 1 := hP.2.2.1

/-- ★ 根の行 2 が 0（＝ `z = 0`）。 -/
theorem hz0_of_TowerP'' {Q : TrioSeq} {d e : ℕ} (hP : TowerP'' Q d e) :
    entry Q 2 0 = 0 := hP.2.2.2.1

/-- ★ ブロックの全列に親がいる（`Q` の言葉、§237）。⟹ `OrphOK` の枝を空にします。 -/
theorem hlocQ_of_TowerP'' {Q : TrioSeq} {d e : ℕ} (hP : TowerP'' Q d e) :
    hlocQ Q := hP.2.2.2.2.1

/-- ★ **`d = 0 ⟹ e = 0`**（H12 の `entry0_parent_lt_of_srow2` から遺伝、§233）。
⟹ `ZeroDOK` が **`d = e = 0`（同一コピー）だけ**になります。 -/
theorem hde_of_TowerP'' {Q : TrioSeq} {d e : ℕ} (hP : TowerP'' Q d e) :
    d = 0 → e = 0 := hP.2.2.2.2.2

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

/-- ⛔⛔ **`RsumHered`**（R2 が 2026-08-30 に見つけた**唯一の共通の核**）。

    `Wset.rsum A P : Prop := ∀ p ∈ A ++ P, entry P 0 0 ≤ p.1`
    ＝「**接頭辞にも `P` にも、`P` の根より浅い列が無い**」

**⟹ ★ R2 の実測: `rsum` があれば `OrphOK` / `OrphOK0` は **100%（612,045、違反 0）**。**
**⟹ ⟹ ⛔ 無ければ **19.3〜54.4% で破れます**。⟹ ですから `rsum` は**必須の前提**です。**

⚠ **消費側では無料**: `Q = Lift1 ((0,v,z) :: R.dropLast) t` は `entry Q 0 0 = 0`
⟹ `rsum A Q` が自明（行 0 は自然数）。⟹ ★ **`A = []` なら `hr0` からも出ます**。

⚠⚠ **遺伝は team-lead の見立てでは**しません****（窓は親の列から始まるので、
`A'` の中に「親の親」＝ より浅い列がある）。⟹ **そこが新しい核です**。

⚠⚠⚠ **正直に**: 私は最初 `∀ A V, A ∈ W u → A ++ V ∈ W u → rsum A V` と書きました。
**⟹ ⛔ それは**明らかに偽**です**（`A = [(0,0,0)]`、`V = [(5,0,0)]`）。
**⟹ ⟹ 偽の仮定を置くと定理が**空虚**になります。⟹ **窓の形に限定し直しました**。**
**⟹ ★ それでも team-lead は「遺伝しない」と見ています。⟹ **偽かもしれません**。**
**⟹ ⟹ ⟹ ですから `mTowerClosedS_of_residues` は**まだ空虚かもしれない**と明記します。** -/
def RsumHered : Prop :=
  ∀ (P B : TrioSeq) (j p : ℕ), p < j → j < B.length →
    rsum (P ++ B.take p) (wnd P B j p)

/-! ## 228. ★★★★★★★★ `rsum` の**代わり**: 「的が塔の根より**真に上**」

§227 で `rsum` が使えないと分かりました。**⟹ 代わりを探して、見つかったと思います。**

## 機構（`nextrel_i` の**最小性の節**を、塔の根で殴る）

`nextrel0 (A ++ T) y (|A| + j1)` の最小性は

    `∀ j, y < j ∧ j < |A| + j1 → entry (A ++ T) 0 (|A| + j1) ≤ entry (A ++ T) 0 j`

**⟹ ★ ここに `j := |A|`（＝ **`T` の根**）を入れると `entry T 0 j1 ≤ entry T 0 0`。**
**⟹ ⟹ ★★ ですから **`entry T 0 0 < entry T 0 j1`** なら、`A` の列は**行 0 の親になれません**。**

**行 1 も同じです**（`nextrel1` の最小性は `le0` 祖先の上なので、`le0 (|A|) (|A|+j1)` が要ります）。

> **⟹ ★★★ `hbase`（`entry T 0 0 = 0`）は「**0 は絶対的な壁**」でした。**
> **⟹ ⟹ ★ これは「**塔の根が的より低ければ壁になる**」——**平行移動で不変**です。** -/

theorem no_nextrel0_from_prefix {A T : TrioSeq} {y j1 : ℕ}
    (hy : y < A.length) (hj1 : 0 < j1)
    (hmin : entry T 0 0 < entry T 0 j1) :
    ¬ nextrel0 (A ++ T) y (A.length + j1) := by
  intro h
  have hval := h.2.2.2.2 A.length ⟨by omega, by omega⟩
  have h0 : entry (A ++ T) 0 (A.length + j1) = entry T 0 j1 := entry_append_right A T 0 j1
  have h1 : entry (A ++ T) 0 A.length = entry T 0 0 := by
    have := entry_append_right A T 0 0
    rw [Nat.add_zero] at this
    exact this
  rw [h0, h1] at hval
  omega

theorem no_nextrel1_from_prefix {A T : TrioSeq} {y j1 : ℕ}
    (hy : y < A.length)
    (hle0 : le0 (A ++ T) A.length (A.length + j1))
    (hmin : entry T 1 0 < entry T 1 j1) :
    ¬ nextrel1 (A ++ T) y (A.length + j1) := by
  intro h
  have hval := h.2.2.2.2.2 A.length ⟨by omega, hle0⟩
  have h0 : entry (A ++ T) 1 (A.length + j1) = entry T 1 j1 := entry_append_right A T 1 j1
  have h1 : entry (A ++ T) 1 A.length = entry T 1 0 := by
    have := entry_append_right A T 1 0
    rw [Nat.add_zero] at this
    exact this
  rw [h0, h1] at hval
  omega

theorem no_nextrel2_from_prefix {A T : TrioSeq} {y j1 : ℕ}
    (hy : y < A.length)
    (hle1 : le1 (A ++ T) A.length (A.length + j1))
    (hmin : entry T 2 0 < entry T 2 j1) :
    ¬ nextrel2 (A ++ T) y (A.length + j1) := by
  intro h
  have hval := h.2.2.2.2.2 A.length ⟨by omega, hle1⟩
  have h0 : entry (A ++ T) 2 (A.length + j1) = entry T 2 j1 := entry_append_right A T 2 j1
  have h1 : entry (A ++ T) 2 A.length = entry T 2 0 := by
    have := entry_append_right A T 2 0
    rw [Nat.add_zero] at this
    exact this
  rw [h0, h1] at hval
  omega

/-! ### 228.1 ⟹ ★★★ **これが `rsum` の代わりです。しかも `Q` だけの条件です**

**`OrphOK` が要るのは「`A` が親を供給しない」ことです。⟹ 上の 3 本で:**

    **行 0** … `entry T 0 0 < entry T 0 j1` … ★ **`hr0` から出ます**（塔の根 ＝ `Q` の根）
    **行 1** … `entry T 1 0 < entry T 1 j1` ＋ `le0` が塔の根を通る
             ⟹ ★ **「的が塔の根より行 1 で上」＝ 錐の中** ⟹ **ブロッカーでは破れる**
    **行 2** … `entry T 2 0 < entry T 2 j1` ＋ `le1` が塔の根を通る

**⟹ ★★★ ⟹ R2 の実測（`OrphOK` が `rsum` 無しで **45.6% 破れる**）と辻褄が合います:**
**⟹ ⟹ **破れるのはブロッカー**（行 1 が根以下の列）のはずです。**

⚠ **そして R2 の反例 `A = [(0,5,0)]`（行 0 = 0 で浅いが**孤児のまま**）も説明できます:**
**⟹ 行 0 では上の壁が効き、行 1 では `A` の列の行 1 が 5 で高すぎて `nextrel1` の狭義増加が取れない。**

⚠ **教訓 14**: 上の 3 本は緑ですが、**`OrphOK` を導いてはいません**。
**⟹ `le0` / `le1` が**塔の根を通る**ことを別に示す必要があります**（`nextrel_i` の候補が
`A` の中にあるとき、鎖が塔の根を経由するか）。⟹ ★ そこが次の仕事です。 -/

/-! ### 227.2 ⟹ ★ ですから `rsum` は**帰納の中では運べません**。外しました

**§226 で `OrphOK` / `OrphOK0` に `rsum A Q` を足しましたが、§227 で `RsumHered` が偽と分かりました。**
**⟹ ⛔ 偽の仮定を残すと定理が**空虚**になります。⟹ ★ **`rsum` を外しました**。**

**⟹ ⟹ ★ いまの `OrphOK` / `OrphOK0` は「証明されていない」であって「偽が証明された」ではありません。**

⚠ **R2 の実測（`rsum` 無し）:**

    `OrphOK`（`j ≥ 1`、`0 < d`）… **96.5% 上限**（`A` が空でも **3.5% 破れる**）
         ⟹ ★ 破れの正体は **「親が 1 ブロック手前」**（R2: 100%、そして `|V| ≤ |Q|` も 100%）
         ⟹ ⟹ **穴ではなく、`parent_bound_pos` の枠が狭い**（team-lead の読み）
    `OrphOK0`（`j = 0`）… `rsum` があれば 100%、無ければ浅い `A` で 19〜31%

**⟹ ★★ ですから次の一手は 2 つです:**

    **(1)** `parent_bound_pos` を **`|V| ≤ |Q|`**（＝「親は高々 `|Q|` 列手前」）に緩める
         ⚠ ★ ただし **`|V| = |Q|` になると測度の第 1 成分が減りません**。
           ⟹ そこは `rankDE` を減らす必要があり、**親がブロック根でないので §200 が使えません**。
           ⟹ ⟹ ★★ **R2 に「`j ≥ 1` で `|V| = |Q|` が起きるか」を聞く必要があります**。
             起きないなら（`|V| < |Q|` が 100% なら）そのまま通ります。
    **(2)** `OrphOK` を「**ブロック ＋ 1 つ前のブロック**の中で孤児」に書き換える

⚠ **教訓 14**: `rsum` を外したので、`mTowerClosedS_of_residues` は
**「偽の仮定による空虚」ではなくなりました**。⟹ ですが `OrphOK` は**実測で 3.5% 破れます**。
**⟹ ⟹ ★ ですから **いまも「証明できていない」状態**です。そこは変わりません。** -/

/-! ## 230. ★★★★★★★ §228 を `OrphOK` に繋ぎます —— **行 0 は完全に閉じます**

team-lead の読み（「穴は `j1 = 0`（塔の根）1 点かもしれない」）を受けて、
§228 を「孤児が孤児のまま」に繋ぎました。

**⟹ ★ まず「剥がす」を **`hroot` なしで**やる道具を作ります。**
**⟹ ⟹ `hasParent_append_right`（`Column:363`）は `hroot` を要求しますが、
**要るのは「接頭辞の列が `nextR` の始点になれない」だけ**です。** -/

theorem hasParent_peel_of_noCross {A T : TrioSeq} {i j1 : ℕ}
    (hnc : ∀ y, y < A.length → ¬ nextR (A ++ T) i y (A.length + j1))
    (hp : hasParent (A ++ T) i (A.length + j1)) : hasParent T i j1 := by
  obtain ⟨j0, hj0, huniq⟩ := hp
  have hge : A.length ≤ j0 := by
    by_contra hc
    exact hnc j0 (by omega) hj0
  obtain ⟨j0', rfl⟩ : ∃ j0', j0 = A.length + j0' := ⟨j0 - A.length, by omega⟩
  refine ⟨j0', (nextR_append_right A T i j0' j1).1 hj0, ?_⟩
  intro y hy
  have := huniq (A.length + y) ((nextR_append_right A T i y j1).2 hy)
  omega

/-- ★★★ **行 0 の `OrphOK` は無条件**（`entry T 0 0 < entry T 0 j1` だけ）。 -/
theorem orphOK_row0 {A T : TrioSeq} {j1 : ℕ} (hj1 : 0 < j1)
    (hmin : entry T 0 0 < entry T 0 j1)
    (hnp : ¬ hasParent T 0 j1) : ¬ hasParent (A ++ T) 0 (A.length + j1) := by
  intro hp
  refine hnp (hasParent_peel_of_noCross (fun y hy hc => ?_) hp)
  unfold nextR at hc
  rw [if_pos rfl] at hc
  exact no_nextrel0_from_prefix hy hj1 hmin hc

/-- ★★ **行 1 の `OrphOK`**（`le0` が塔の根を通ることと、行 1 の大小が要る）。 -/
theorem orphOK_row1 {A T : TrioSeq} {j1 : ℕ}
    (hle0 : le0 (A ++ T) A.length (A.length + j1))
    (hmin : entry T 1 0 < entry T 1 j1)
    (hnp : ¬ hasParent T 1 j1) : ¬ hasParent (A ++ T) 1 (A.length + j1) := by
  intro hp
  refine hnp (hasParent_peel_of_noCross (fun y hy hc => ?_) hp)
  unfold nextR at hc
  rw [if_neg (by omega), if_pos rfl] at hc
  exact no_nextrel1_from_prefix hy hle0 hmin hc

/-- ★★ **行 2 の `OrphOK`**（`le1` が塔の根を通ることと、行 2 の大小が要る）。 -/
theorem orphOK_row2 {A T : TrioSeq} {j1 : ℕ}
    (hle1 : le1 (A ++ T) A.length (A.length + j1))
    (hmin : entry T 2 0 < entry T 2 j1)
    (hnp : ¬ hasParent T 2 j1) : ¬ hasParent (A ++ T) 2 (A.length + j1) := by
  intro hp
  refine hnp (hasParent_peel_of_noCross (fun y hy hc => ?_) hp)
  unfold nextR at hc
  rw [if_neg (by omega), if_neg (by omega)] at hc
  exact no_nextrel2_from_prefix hy hle1 hmin hc

/-! ### 230.1 ⟹ ★★★ **`hbase` の正体が分かりました**

    `Column.hasParent_append_right`（`:363`）… `hroot : entry T 0 0 = 0` を要求
    ★ **本当に要るのは「接頭辞の列が `nextR` の始点になれない」だけ**（`hasParent_peel_of_noCross`）
    ⟹ ⟹ そして §228 の 3 本が、それを**行ごとに**与えます

**⟹ ★★ ですから H12 の「`hbase` の弱化は行 1/2 で止まる」は、**`hr0` で殴ろうとしたから**でした。**
**⟹ ⟹ ★ **行 1 には行 1 の条件、行 2 には行 2 の条件**を使えば、3 行とも同じ形で通ります。**

### 230.2 ⟹ ★ `OrphOK` に必要なもの（行ごと）

`OrphOK` の的は `T = mTower Q d e n ++ block.take (j+1)` の位置 `j1 = n*|Q| + j`（`j ≥ 1`）。

    **`srow = 0`** … ✅ **無条件**。`entry T 0 0 = entry Q 0 0`、`entry T 0 j1 = entry Q 0 j + d*n`
                  ⟹ **`hr0` と `j ≥ 1` で `<` が出ます** ⟹ **完全に閉じます**
    **`srow = 1`** … ⛔ `le0` が塔の根を通ること ＋ **`entry Q 1 0 < entry T 1 j1`**
                  ⟹ ★ 後者は「**的が錐の中**」＝ **ブロッカーでない** ⟹ H12 の `h1out` と同じもの
    **`srow = 2`** … ⛔ `le1` が塔の根を通ること ＋ `entry Q 2 0 < entry T 2 j1`

**⟹ ★★★ ⟹ R2 の実測（`OrphOK` が 3.5% 破れる）は、**`srow ≥ 1` の側**のはずです。**
**⟹ ⟹ R2 に「破れを `srow` で切ってほしい」と伝えます。⟹ `srow = 0` が 1 件でも出たら
私の証明か計器のどちらかが誤りです。**

⚠ **教訓 14**: 上の 3 本は緑ですが、**`OrphOK` を導いてはいません**。
**`le0` / `le1` が塔の根を通ることと、行 1・行 2 の大小が残っています。** -/

theorem entry0_block_take {Q : TrioSeq} {d e n j x : ℕ} (hx : x < j + 1)
    (hxQ : x < Q.length) :
    entry ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 0 x
      = entry Q 0 x + d * n := by
  rw [Wset.entry_take hx, entry0_Lift1, entry0_shiftr01 hxQ]

/-- ★ ブロックの接頭辞の根は、行 0 で狭義最浅（`hr0` から）。 -/
theorem hmin_block {Q : TrioSeq} {d e n j : ℕ} (hj : j < Q.length)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) :
    ∀ l, 0 < l → l < ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length →
      entry ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 0 0
        < entry ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 0 l := by
  have hBlen : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length = Q.length := by
    rw [Lift1_length, shiftr01_length]
  intro l hl0 hlt
  rw [List.length_take, hBlen, Nat.min_eq_left (by omega)] at hlt
  rw [entry0_block_take (d := d) (e := e) (n := n) (by omega) (by omega),
    entry0_block_take (d := d) (e := e) (n := n) hlt (by omega)]
  have := hr0 l hl0 (by omega)
  omega


/-! ## 234. ★★★★★★★★★★ **配線**: `OrphOK` を `TowerP''` の中に取り込みます

team-lead の最優先依頼です。**⟹ ★ 鍵は「1 回で剥がす」ことでした。**

⚠ §232.2 で「2 段は難度が違う」と書きました。**⟹ ★ ですが**2 段に分けなければ**よいのです。**

    **`A' := A ++ mTower Q d e n`**、**`T' := ブロックの接頭辞 `B.take (j+1)`**
    ⟹ `S = A' ++ T'`、的は `A'.length + j`
    ⟹ ★ 要る入力は **`¬ hasParent T' (srow T' j) j`** ＝ **`hloc` そのもの** ✅

**⟹ ★★ そして H12 の `no_nextR_srow_cross` の 3 前提を `T' = B.take (j+1)` で見ると:**

    `hmin` … `hmin_block`（§232、**`hr0` だけ**）✅
    `hz0`  … `entry (B.take (j+1)) 2 0 = entry Q 2 0 = 0` ✅（`TowerP''`）
    `hnb`  … `entry (block) 1 0 < entry (block) 1 l` ⟹ ⛔ **`n` に依存して見える**

## ★★★ ⟹ ですが **`hnbQ`（`Q` にブロッカーが無い）があれば `n` が消えます**

**`hnbQ` ⟹ `L105.not_le1_zero_iff` の右辺が偽 ⟹ **`Q` の全列が錐の中****
**⟹ ⟹ ★ `block_getD` の `if le1 Q 0 x` が**常に真** ⟹ `entry (block) 1 x = entry Q 1 x + e*n`**
**⟹ ⟹ ⟹ ★★ 両辺の `e*n` が消えて **`hnbQ` そのもの**になります。** -/

/-- ★ `hnbQ`（ブロッカー無し）⟹ `Q` の全列が根の錐の中。 -/
theorem le1_zero_all_of_noBlocker {Q : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hnbQ : ∀ i, 0 < i → i < Q.length → entry Q 1 0 < entry Q 1 i)
    {q : ℕ} (hq : q < Q.length) : le1 Q 0 q := by
  by_contra hc
  obtain ⟨y, hy, hy0, hy1⟩ := (not_le1_zero_iff hr0 hq).mp hc
  have hyq : y ≤ q := nextrel0_rtrancl_index_le hy
  have := hnbQ y (by omega) (by omega)
  omega

/-- ★★ `hnbQ` ⟹ ブロックの接頭辞にもブロッカーが無い（**`n` に依らない**）。 -/
theorem hnb_block {Q : TrioSeq} {d e n j : ℕ} (hj : j < Q.length)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hnbQ : ∀ i, 0 < i → i < Q.length → entry Q 1 0 < entry Q 1 i) :
    ∀ l, 0 < l → l < ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length →
      entry ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 1 0
        < entry ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 1 l := by
  have hBlen : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length = Q.length := by
    rw [Lift1_length, shiftr01_length]
  have hE : ∀ x, x < j + 1 → x < Q.length →
      entry ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 1 x
        = entry Q 1 x + e * n := by
    intro x hx hxQ
    rw [Wset.entry_take hx]
    show ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).getD x (0, 0, 0)).2.1 = _
    rw [block_getD hxQ, if_pos (le1_zero_all_of_noBlocker hr0 hnbQ hxQ)]
  intro l hl0 hlt
  rw [List.length_take, hBlen, Nat.min_eq_left (by omega)] at hlt
  rw [hE 0 (by omega) (by omega), hE l hlt (by omega)]
  have := hnbQ l hl0 (by omega)
  omega

/-- ★ ブロックの接頭辞の根の行 2 は `Q` の根の行 2。 -/
theorem hz0_block {Q : TrioSeq} {d e n j : ℕ} (hQ1 : 0 < Q.length)
    (hz0 : entry Q 2 0 = 0) :
    entry ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 2 0 = 0 := by
  rw [Wset.entry_take (show (0 : ℕ) < j + 1 by omega)]
  show ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).getD 0 (0, 0, 0)).2.2 = 0
  rw [block_getD (d := d) (e := e) (n := n) hQ1]
  exact hz0

/-- ★★★★★ **`OrphOK` が定理になりました**（`hnbQ` を前提に）。 -/
theorem orphOK_proved {A Q : TrioSeq} {d e n j : ℕ}
    (hQ1 : 0 < Q.length) (hj : j < Q.length) (hj1 : 0 < j)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hz0 : entry Q 2 0 = 0)
    (hnbQ : ∀ i, 0 < i → i < Q.length → entry Q 1 0 < entry Q 1 i)
    (hloc : ¬ hasParent ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (srow ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) j) j) :
    ¬ hasParent (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (srow (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        ((A ++ mTower Q d e n).length + j))
      ((A ++ mTower Q d e n).length + j) := by
  have hBlen : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length = Q.length := by
    rw [Lift1_length, shiftr01_length]
  have hlen : ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length = j + 1 := by
    rw [List.length_take, hBlen, Nat.min_eq_left (by omega)]
  intro hp
  have hsr : srow (A ++ mTower Q d e n
      ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      ((A ++ mTower Q d e n).length + j)
      = srow ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) j :=
    srow_append_right _ _ j
  rw [hsr] at hp
  -- ★ 1 回で剥がす: `A' := A ++ mTower Q d e n`、`T' := ブロックの接頭辞`
  refine hloc (hasParent_peel_of_noCross (A := A ++ mTower Q d e n)
    (T := (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
    (i := srow ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) j)
    (fun y hy hc => ?_) hp)
  rw [← hsr] at hc
  exact no_nextR_srow_cross (hmin_block (d := d) (e := e) (n := n) hj hr0)
    (hnb_block (d := d) (e := e) (n := n) hj hr0 hnbQ)
    (hz0_block (d := d) (e := e) (n := n) (j := j) hQ1 hz0) hy (by omega) hj1 hc

/-- ⛔ **遺伝 (1)**: 窓の根の行 2 が 0（＝ 旧 `HeredZ2`）。**R2 実測 98.4〜99.8%**。 -/
def HeredZ0 : Prop :=
  ∀ (P B : TrioSeq) (j p : ℕ), p < j → j < B.length →
    hasParent (P ++ B.take (j + 1))
      (srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1))
      ((P ++ B.take (j + 1)).length - 1) →
    parent (P ++ B.take (j + 1))
      (srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1))
      ((P ++ B.take (j + 1)).length - 1) = P.length + p →
    entry (wnd P B j p) 2 0 = 0

/-- ⛔ **遺伝 (2)**: 窓が `hlocQ` を満たす（＝ ブロックの全列に親がいる）。
★ **`hbase` / `rsum` / `h1out` / `hnbQ` と違い、核の形（型 B）で偽になりません**（§236）。
⚠ **遺伝は未測定**（R2 の (LOCHER) 待ち）。 -/
def HeredNB : Prop :=
  ∀ (P B : TrioSeq) (j p : ℕ), p < j → j < B.length → hlocQ (wnd P B j p)


/-! ## 233. ★★★ H12 の「`d = 0 ⟹ e = 0`」を窓の言葉で（`wd0 = 0 ⟹ wd1 = 0`）

H12 の `entry0_parent_lt_of_srow2`（緑）を、私の `wd0` / `wd1` に当てます。

    `wd1 > 0` ⟹ `1 < srow(末尾)` ⟹ `srow = 2` ⟹ 親は `nextrel2` の始点
    ⟹ H12 `entry0_parent_lt_of_srow2` … **行 0 が狭義に小さい**
    ⟹ `wd0 = entry 0 (末尾) − entry 0 (親) > 0`

**⟹ ★ 対偶で **`wd0 = 0 ⟹ wd1 = 0`**。⟹ ⟹ **`d = 0` の塔は `d = e = 0` にしかならない**。** -/

open Classical in
theorem wd1_zero_of_wd0_zero {P B : TrioSeq} {j p : ℕ}
    (hpar : hasParent (P ++ B.take (j + 1))
      (srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1))
      ((P ++ B.take (j + 1)).length - 1))
    (hpe : parent (P ++ B.take (j + 1))
      (srow (P ++ B.take (j + 1)) ((P ++ B.take (j + 1)).length - 1))
      ((P ++ B.take (j + 1)).length - 1) = P.length + p)
    (h0 : wd0 P B j p = 0) : wd1 P B j p = 0 := by
  set T := P ++ B.take (j + 1) with hT
  set s := srow T (T.length - 1) with hs
  unfold wd1
  rw [← hT, ← hs]
  by_cases h2 : 1 < s
  · exfalso
    -- `srow = 2` ⟹ 親は `nextrel2` の始点 ⟹ 行 0 が狭義に小さい
    have hnr := parent_nextR hpar
    rw [hpe] at hnr
    have hs2 : s = 2 := by
      have hss : s = srow T (T.length - 1) := hs
      unfold srow at hss
      split_ifs at hss <;> omega
    rw [hs2] at hnr
    have hlt := entry0_parent_lt_of_srow2 hnr
    have h0' := h0
    unfold wd0 at h0'
    rw [← hT, ← hs, if_pos (by omega)] at h0'
    omega
  · rw [if_neg h2]

/-! ## 213. ★★★★★★★★★ **`hsnoc` の `j ≥ 1` の枝が緑になりました**

材料が全部そろったので組みます。**残る前提は「窓に `TowerP''` が遺伝する」1 本だけです。** -/

open Classical in
theorem hsnoc_pos {u : ℕ} {A Q : TrioSeq} {d e n j : ℕ}
    (hP : TowerP'' Q d e)
    (hIH : ∀ V d0 d1, TowerP'' V d0 d1 → towerMeas V d0 d1 < towerMeas Q d e →
      ∀ A', A' ∈ W u → A' ++ V ∈ W u → ∀ m, A' ++ mTower V d0 d1 m ∈ W u)
    (hz0h : HeredZ0) (hnbh : HeredNB)
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
      (fun q hq => by
        rw [hlenV] at hq
        rw [entry2_wnd hpj hq]
        exact hz1 (p + q) (by omega)),
      hz0h P B j p hpj (by omega) hpar (by rw [← hpardef]; exact hpe),
      hnbh P B j p hpj (by omega),
      fun h0 => wd1_zero_of_wd0_zero hpar (by rw [← hpardef]; exact hpe) h0⟩ ?_
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
    (hz0h : HeredZ0) (hnbh : HeredNB)
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
      exact hz1 (p + q) (by omega),
    hz0h P (B0 ++ B1) Q.length p hplt (by omega) hpar hpe,
    hnbh P (B0 ++ B1) Q.length p hplt (by omega),
    fun h0 => wd1_zero_of_wd0_zero hpar hpe h0⟩
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
  ∀ (A Q : TrioSeq), TowerP'' Q 0 0 → A ∈ W u → A ++ Q ∈ W u →
    ∀ n, A ++ mTower Q 0 0 n ∈ W u

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
    (hz0 : entry Q 2 0 = 0) (hz1 : ∀ q, q < Q.length → entry Q 2 q ≤ 1)
    (hz0h : HeredZ0) (hnbh : HeredNB)
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
      hplt hpar hpe hz1 hz0h hnbh ?_
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
theorem towerClosed_of_hered {u : ℕ} (horph0 : OrphOK0)
    (hzd : ZeroDOK u) (hz0h : HeredZ0) (hnbh : HeredNB) :
    ∀ Q d e, TowerP'' Q d e → ∀ A, A ∈ W u → A ++ Q ∈ W u →
      ∀ n, A ++ mTower Q d e n ∈ W u := by
  refine tower_of_measure_step2 (u := u) TowerP'' towerMeas ?_
  intro Q d e hP hIH A hA hAQ
  have hQne := ne_of_TowerP'' hP
  have hQ1 : 0 < Q.length := List.length_pos_iff.mpr hQne
  have hr0 := hr0_of_TowerP'' hP
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    have he0 : e = 0 := hde_of_TowerP'' hP rfl
    subst he0
    exact hzd A Q hP hA hAQ
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
    exact hsnoc_zero_noE horph0 hQne hdpos hr0 (hz0_of_TowerP'' hP)
      (hz1_of_TowerP'' hP) hz0h hnbh hIH hpre
  · -- ★ `j ≥ 1` … `hlocQ` で `hloc` が**常に**立つので、孤児の枝は空です（§237）
    exact hsnoc_pos hP hIH hz0h hnbh hj hj1
      (block_hasParent_all_of_hlocQ hj hj1 hr0 (hlocQ_of_TowerP'' hP))
      (parent_bound_pos hj (block_hasParent_all_of_hlocQ hj hj1 hr0
        (hlocQ_of_TowerP'' hP))) hall

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

/-- ⛔ **消費側の `hlocQ`**（ブロックの全列に親がいる）。 -/
def RootNB : Prop :=
  ∀ (u : ℕ) (Q : TrioSeq), Q ∈ W u → hlocQ Q

/-- ⛔ **消費側の `hz0`**（`z = 0` に相当）。H12 の `hz0_of_zle1` が効くはずのところ。 -/
def RootZ2 : Prop :=
  ∀ (u : ℕ) (Q : TrioSeq), Q ∈ W u →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) → entry Q 2 0 = 0

theorem mTower_nil (d e n : ℕ) : mTower ([] : TrioSeq) d e n = [] :=
  List.eq_nil_of_length_eq_zero (by rw [mTower_length]; simp)

open Classical in
/-- ★★★★★ **`MTowerClosedS` は 5 本から出ます。** -/
theorem mTowerClosedS_of_residues (horph0 : OrphOK0)
    (hzd : ∀ u, ZeroDOK u) (hz0h : HeredZ0) (hnbh : HeredNB)
    (hrz1 : RootZ1) (hroot : RootZ2) (hrnb : RootNB)
    (hde : ∀ (u : ℕ) (Q : TrioSeq) (d e : ℕ), Q ∈ W u → d = 0 → e = 0) :
    MTowerClosedS := by
  intro u d e n Q hQ hs
  rcases Nat.eq_zero_or_pos Q.length with h0 | hpos
  · have hnil : Q = [] := List.eq_nil_of_length_eq_zero h0
    subst hnil
    rw [mTower_nil]
    exact W_nil u
  · have hP : TowerP'' Q d e :=
      ⟨hpos, fun l hl0 hl1 => hs l hl0 hl1, hrz1 u Q hQ, hroot u Q hQ hs,
        hrnb u Q hQ, hde u Q d e hQ⟩
    have h := towerClosed_of_hered (u := u) horph0 (hzd u) hz0h hnbh
      Q d e hP [] (W_nil u) (by simpa using hQ) n
    simpa using h

/-! ### 222.1 ⟹ ★★★★★★★★ **`MTowerClosedS` は 6 本**（`OrphOK` は**消えました**）

```lean
theorem mTowerClosedS_of_residues (horph0 : OrphOK0)
    (hzd : ∀ u, ZeroDOK u) (hz0h : HeredZ0) (hnbh : HeredNB)
    (hrz1 : RootZ1) (hroot : RootZ2) (hrnb : RootNB) : MTowerClosedS
```

    **(1) `OrphOK0`**（`j = 0`、`0 < d`）… 塔の中で孤児 ⟹ 接頭辞つきでも孤児
    **(2) `ZeroDOK`** … `d = 0` の塔 ⟹ H12 が `PrefixCopiesOpen` に合流させた
    **(3) `HeredZ0`** … 窓の根の行 2 が 0 ⟹ **R2 実測 98.4〜99.8%**
    **(4) `HeredNB`** … ★ **窓が `hlocQ` を満たす**（§237）⟹ **R2 の (LOCHER) 待ち**
    **(5) `RootZ1` / (6) `RootZ2` / `RootNB`** … 消費側の 3 本

**⟹ ★★★ `OrphOK`（`j ≥ 1`）は **枝ごと消えました**。⟹ §237 で `hloc` が**常に**立つので。**

### 222.2 ★★★★★ **条件の系譜**（今日たどった 5 段）

| 条件 | 意味 | 状態 |
|---|---|---|
| `hbase` | 塔の根の深さが **0** | ⛔ 遺伝 **0%**（§207 で**証明**） |
| `rsum` | 接頭辞に根より浅い列が無い | ⛔ 遺伝 **0%**（§227 で**証明**） |
| `h1out` | 錐の外の列が**根**より行 1 で上 | ⛔ H12 `blocker_of_large_k` で**必ず壊れる** |
| `hnbQ` | **全列**が根より行 1 で上 | ⛔ **核の形（型 B）で偽**（§235、緑） |
| ★★★ **`hlocQ`** | **`le0` の祖先に行 1 が小さい列がある** | ⟹ **核の形でも立つ**（§236、緑） |

**⟹ ★ 毎回「壁を立てる**十分条件**」を弱めてきました。**
**⟹ ⟹ ★★ `hlocQ` は「ブロックの中に親がいる」の**言い換え**なので、**必要十分に近い**形です。**

### 222.3 ★ 消えたもの（今日）

    `hbase`（§208）／ `hd0e`・`hlp`（未使用）／ `h2out`・`h1out`（`hlocQ` に吸収）
    `0 < d`・`0 < e`（**導出に変えた**）／ `ZeroEOK`（H12 の (q3b)）
    `hr0(V)` の遺伝（§221）／ **`OrphOK`（§237 で枝ごと消滅）**

⚠ **教訓 14**: **6 本のどれも証明していません。**
**とくに `HeredNB`（＝ `hlocQ` の遺伝）は**測ってもいません**。** -/

/-! ## 238. ★★★★★★★ `hlocQ` の遺伝の下ごしらえ: **`le0` は窓に移ります**

team-lead の (ADJ)（証人が隣で取れるか）待ちですが、**どの証人でも要る道具**を先に作ります。

**⟹ ★ 窓は**連続した区間**なので、`nextrel0` はそのまま移るはずです。**
**⟹ ⟹ `nextrel0` の最小性は「間の列」についてで、**間の列は窓の中に全部ある**からです。** -/

theorem window_length {T : TrioSeq} {s L : ℕ} (hL : s + L ≤ T.length) :
    ((T.drop s).take L).length = L := by
  rw [List.length_take, List.length_drop]
  omega

theorem nextrel0_window {T : TrioSeq} {s L a b : ℕ} (hL : s + L ≤ T.length)
    (ha : a < L) (hb : b < L) :
    nextrel0 ((T.drop s).take L) a b ↔ nextrel0 T (s + a) (s + b) := by
  have hlen := window_length hL
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    rw [entry_window T (i := 0) hb, entry_window T (i := 0) ha] at h4
    refine ⟨by omega, by omega, by omega, h4, ?_⟩
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = s + j' := ⟨j - s, by omega⟩
    have hj'L : j' < L := by omega
    have := h5 j' ⟨by omega, by omega⟩
    rw [entry_window T (i := 0) hb, entry_window T (i := 0) hj'L] at this
    exact this
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩
    · rw [entry_window T (i := 0) hb, entry_window T (i := 0) ha]; omega
    · intro j hj
      have := h5 (s + j) ⟨by omega, by omega⟩
      rw [entry_window T (i := 0) hb, entry_window T (i := 0) (show j < L by omega)]
      exact this

/-- ★★ **`le0` は窓に移ります**（`nextrel0` の鎖は前へ進むので、窓から出ません）。 -/
theorem le0_window {T : TrioSeq} {s L a b : ℕ} (hL : s + L ≤ T.length)
    (ha : a < L) (hb : b < L) (h : le0 T (s + a) (s + b)) :
    le0 ((T.drop s).take L) a b := by
  have hlen := window_length hL
  obtain ⟨-, -, hrtg⟩ := h
  refine ⟨by omega, by omega, ?_⟩
  -- 鎖の各ノードは `[s+a, s+b]` の中（`nextrel0` は添字を増やすので）
  have key : ∀ c, Relation.ReflTransGen (nextrel0 T) (s + a) c → c ≤ s + b →
      ∃ c', c = s + c' ∧ c' < L ∧
        Relation.ReflTransGen (nextrel0 ((T.drop s).take L)) a c' := by
    intro c hc
    induction hc with
    | refl => intro _; exact ⟨a, rfl, ha, Relation.ReflTransGen.refl⟩
    | @tail x y hx hxy ih =>
        intro hyb
        have hxy' := hxy
        have hxle : x < y := hxy.2.2.1
        obtain ⟨x', rfl, hx'L, hch⟩ := ih (by omega)
        obtain ⟨y', rfl⟩ : ∃ y', y = s + y' := ⟨y - s, by omega⟩
        have hy'L : y' < L := by omega
        exact ⟨y', rfl, hy'L,
          hch.tail ((nextrel0_window hL hx'L hy'L).mpr hxy')⟩
  obtain ⟨b', hb'eq, -, hres⟩ := key (s + b) hrtg (le_refl _)
  have : b' = b := by omega
  subst this
  exact hres

/-! ### 238.1 ⟹ ★ これで `hlocQ` の遺伝の**行 0 の部分**は移ります

**残るのは 2 つです:**

    **(a)** 証人 `y` が**窓の中**にあるか（＝ `p ≤ y`）… ★ **team-lead の (ADJ)**
    **(b)** 錐のクラス条件 `le1 V 0 y' → le1 V 0 t` が、`Q` のものから出るか
         ⚠ ★ **`V` の錐は `V` の根（＝ `Q` の列 `p`）についてなので、`Q` の錐とは別物です**
         ⟹ ⟹ ★ **そこが残ります**

**⟹ ★ (a) は測定待ち、(b) は私が見ます。** -/

/-! ### 238.2 ★★ 錐のクラス条件は、**的が錐の外なら自動で満たせます**

`hlocQ` の `hcls : le1 Q 0 y → le1 Q 0 j` は、**証人 `y` が錐の外なら前件が偽**で
**空虚に真**です。**⟹ ★ そして的 `j` が錐の外なら、`not_le1_zero_iff` が
**錐の外の候補**（ブロッカー）を必ず 1 つ供給します。** -/

/-- ★ ブロッカーは必ず錐の外（H12 の `blocker_not_le1` と同じもの、こちらで再証明）。 -/
theorem blocker_out_of_cone {Q : TrioSeq} {y : ℕ} (hy0 : y ≠ 0)
    (hy1 : entry Q 1 y ≤ entry Q 1 0) : ¬ le1 Q 0 y := by
  intro hc
  have := le1_entry1_lt hc (show (0 : ℕ) ≠ y from fun h => hy0 h.symm)
  omega

/-- ★★ **的が錐の外なら、錐の外の候補が必ず取れます**（`not_le1_zero_iff` から）。
⟹ ★ その候補で `entry Q 1 y < entry Q 1 j` さえ言えれば、`hlocQ` の 3 条件が全部そろいます
（`hcls` は**空虚に真**）。 -/
theorem outOfCone_witness_candidate {Q : TrioSeq}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    {j : ℕ} (hj : j < Q.length) (hout : ¬ le1 Q 0 j) :
    ∃ y, y ≤ j ∧ y ≠ 0 ∧ le0 Q y j ∧ entry Q 1 y ≤ entry Q 1 0 ∧ ¬ le1 Q 0 y := by
  obtain ⟨y, hy, hy0, hy1⟩ := (not_le1_zero_iff hr0 hj).mp hout
  have hyj : y ≤ j := nextrel0_rtrancl_index_le hy
  exact ⟨y, hyj, hy0, ⟨by omega, hj, hy⟩, hy1, blocker_out_of_cone hy0 hy1⟩

/-! ### 238.3 ⟹ ★★★ **`hlocQ` の残りは「行 1 の 1 つの比較」だけ**

**的 `j` の錐の内外で分けると:**

    **`j` が錐の中** … `hcls` の後件が真 ⟹ **`hcls` は自動**
         ⟹ 残るのは「`le0` の祖先に行 1 が小さい列がある」だけ
    **`j` が錐の外** … §238.2 が**錐の外の候補 `y`** を供給 ⟹ `hcls` は**空虚に真**
         ⟹ 残るのは **`entry Q 1 y < entry Q 1 j`** だけ
         ⚠ ★ 候補は `entry Q 1 y ≤ entry Q 1 0` なので、
           **`entry Q 1 0 < entry Q 1 j` なら足ります** ⟹ ★ それは **`h1out` そのもの**
         ⟹ ⟹ ⛔ ですが `h1out` は `blocker_of_large_k` で壊れます
         ⟹ ⟹ ⟹ ★★ **候補を「行 1 が最小のブロッカー」に取り直せば、より弱くなります**

**⟹ ★ ですから `hlocQ` の本体は「**ブロッカーのうち行 1 が最小のものが、的より小さいか**」です。**
**⟹ ⟹ ★★ 核の形（型 B）では: ブロッカーは第 1 列（行 1 ＝ 0）、的は第 2 列（行 1 ＝ `b > 0`）**
**⟹ ⟹ ⟹ **`0 < b`** ✅ ⟹ **通ります**。**

⚠ **教訓 14**: 上の分解は緑ですが、**`hlocQ` の遺伝は証明していません**。
**⟹ ★ team-lead の (ADJ)（証人が隣で取れるか）と合わせて決まります。** -/

/-! ## 239. ★★★★★★ (P1) の骨: **窓の中の証人はそのまま移ります**

R2 の (ADJ): **証人の距離は最大 2**、`hlocQ(V)` の遺伝は **95.5〜96.9%**、**`n` 依存なし**。
**⟹ ★ ですから「証人が窓の中にある」なら、§238 の `le0_window` でそのまま移ります。**

**⟹ ★★ 下は「証人が窓の中にある」を**前提**にした遺伝の骨です。**
**⟹ ⟹ 残るのは **錐のクラス条件**（`V` の錐は `V` の根についてなので `B` のものと別）だけです。** -/

open Classical in
/-- ★★ **窓の中の証人は、行 0（`le0`）も行 1（`entry`）もそのまま移ります**。 -/
theorem wnd_witness_transfer {P B : TrioSeq} {j p t y : ℕ}
    (hjB : j < B.length) (hpj : p < j) (htL : t < j - p)
    (hy1 : p ≤ y) (hy2 : y < p + t)
    (hle0 : le0 (P ++ B.take (j + 1)) (P.length + y) (P.length + (p + t)))
    (hlt : entry (P ++ B.take (j + 1)) 1 (P.length + y)
      < entry (P ++ B.take (j + 1)) 1 (P.length + (p + t))) :
    (y - p) < t ∧ le0 (wnd P B j p) (y - p) t ∧
      entry (wnd P B j p) 1 (y - p) < entry (wnd P B j p) 1 t := by
  have hTl : (P ++ B.take (j + 1)).length = P.length + (j + 1) := by
    rw [List.length_append, List.length_take, Nat.min_eq_left (by omega)]
  have hle : P.length + p + (j - p) ≤ (P ++ B.take (j + 1)).length := by omega
  refine ⟨by omega, ?_, ?_⟩
  · unfold wnd
    have h := le0_window (T := P ++ B.take (j + 1)) (s := P.length + p) (L := j - p)
      (a := y - p) (b := t) (by omega) (by omega) htL ?_
    · exact h
    · have e1 : P.length + p + (y - p) = P.length + y := by omega
      have e2 : P.length + p + t = P.length + (p + t) := by omega
      rw [e1, e2]; exact hle0
  · unfold wnd
    rw [entry_window _ (show y - p < j - p by omega), entry_window _ htL]
    have e1 : P.length + p + (y - p) = P.length + y := by omega
    have e2 : P.length + p + t = P.length + (p + t) := by omega
    rw [e1, e2]
    exact hlt

/-! ### 239.1 ⟹ ★ **(P1) に残るのは錐のクラス条件だけ**

    ✅ **`le0`** … §238 `le0_window`（窓は連続区間）
    ✅ **行 1 の大小** … `entry_window`（§224.5）
    ✅ **証人が窓の中** … R2 の (ADJ)（距離 ≤ 2）＋ `|V| ≥ 3`
    ⛔ **錐のクラス** … `le1 V 0 (y−p) → le1 V 0 t`
         ⚠ ★ **`V` の錐は `V` の根（＝ `B` の列 `p`）についてなので、`B` の錐とは別物**

**⟹ ★★ §238.2 の分解が効きます:**

    `t` が **`V` の錐の外** ⟹ `outOfCone_witness_candidate` が **`V` の中で錐の外の候補**を供給
         ⟹ ★ クラス条件は**空虚に真** ⟹ **`B` から移す必要すらありません**
    `t` が **`V` の錐の中** ⟹ 後件が真 ⟹ ★ **クラス条件は自動**

**⟹ ★★★ ⟹ **どちらの場合もクラス条件は自動**です。⟹ ⟹ 残るのは
「錐の外の候補が `entry V 1 y* < entry V 1 t` を満たすか」だけ。**

**⟹ ★ そしてそれは §238.3 の「**行 1 が最小のブロッカーが的より小さいか**」そのものです。**

⚠ **教訓 14**: 上は**分解**です。**(P1) はまだ組んでいません。**
**⟹ ★ 組むには「`V` の中で候補を取り直す」ところを書く必要があります。** -/

/-! ### 239.2 ★★★★ (P1) の**受け皿**: 証人が窓の中にあれば `hlocQ` が移ります

team-lead の依頼 1 です。**「証人の距離 ≤ 2」（R2 の (ADJ)）は H12 が定理にしています。**
**⟹ ★ こちらは「**証人が窓の中にある**」を前提にした**受け皿**を先に置きます。** -/

open Classical in
theorem hlocQ_wnd_of_witnesses {P B : TrioSeq} {j p : ℕ}
    (hjB : j < B.length) (hpj : p < j)
    (h2 : ∀ t, 0 < t → t < j - p → 0 < entry (wnd P B j p) 2 t →
      hasParent ((wnd P B j p).take (t + 1)) 2 t)
    (h1 : ∀ t, 0 < t → t < j - p →
      entry (wnd P B j p) 2 t = 0 → 0 < entry (wnd P B j p) 1 t →
      ∃ y, p ≤ y ∧ y < p + t ∧
        le0 (P ++ B.take (j + 1)) (P.length + y) (P.length + (p + t)) ∧
        entry (P ++ B.take (j + 1)) 1 (P.length + y)
          < entry (P ++ B.take (j + 1)) 1 (P.length + (p + t)) ∧
        (le1 (wnd P B j p) 0 (y - p) → le1 (wnd P B j p) 0 t)) :
    hlocQ (wnd P B j p) := by
  have hlen : (wnd P B j p).length = j - p := wnd_length hjB hpj
  intro t ht0 htL
  rw [hlen] at htL
  refine ⟨h2 t ht0 htL, ?_⟩
  intro hz hpos
  obtain ⟨y, hy1, hy2, hle0, hlt, hcls⟩ := h1 t ht0 htL hz hpos
  obtain ⟨hylt, hle0V, hltV⟩ :=
    wnd_witness_transfer (P := P) (B := B) (j := j) (p := p) (t := t) (y := y)
      hjB hpj htL hy1 hy2 hle0 hlt
  exact ⟨y - p, hylt, hle0V, hltV, hcls⟩

/-! ### 239.3 ⟹ ★ **(P1) の残りは「証人が `p` 以上に取れるか」1 つ**

    ✅ **`le0` の移送** … §238 `le0_window`
    ✅ **行 1 の移送** … `entry_window`
    ✅ **受け皿** … §239.2（上）
    ⛔ **証人が `p` 以上** … ★ **R2 の (ADJ)：距離 ≤ 2 ⟹ `t ≥ 2` なら自動**
         ⚠ **`t = 1` のときだけ、証人が `p − 1`（窓の外）になりえます**
         ⟹ ★ ですが **`t = 1` の証人が「窓の根 `p`」なら距離 1 で窓の中** ✅
         ⟹ ⟹ ★★ ですから **「`t = 1` の証人が根に取れるか」**が最後の 1 点です

**⟹ ★ team-lead の補足（「窓の根 `p` は候補になるはず」）と**同じ場所**に来ました。**
**⟹ ⟹ ★★ R2 に **(ADJ'-d)**「窓の**第 1 列**（`t = 1`）の証人が**窓の根**に取れるか」を
出してもらってください。⟹ ★ **100% なら (P1) が閉じます**。**

⚠ **教訓 14**: §239.2 は**受け皿**です。**証人の存在は仮定しています。** -/

/-! ### 239.4 ★★★★★ **`t = 1` は「1 つの不等式」と同値**です（証人は根しかありません）

§239.3 で「`t = 1` の証人が窓の根に取れるか」が最後の 1 点だと書きました。
**⟹ ★ 実は **`t = 1` では証人の候補が根しかありません**（`y < 1` ⟹ `y = 0`）。**
**⟹ ⟹ ★★ ですから **同値**です。⟹ 測る前に**形が決まります**。** -/

open Classical in
theorem hlocQ_first_column_iff {V : TrioSeq} (hV : 1 < V.length)
    (hr0V : ∀ l, 0 < l → l < V.length → entry V 0 0 < entry V 0 l) :
    (∃ y, y < 1 ∧ le0 V y 1 ∧ entry V 1 y < entry V 1 1 ∧ (le1 V 0 y → le1 V 0 1))
      ↔ entry V 1 0 < entry V 1 1 := by
  constructor
  · rintro ⟨y, hy, -, hlt, -⟩
    have : y = 0 := by omega
    subst this
    exact hlt
  · intro hlt
    have hn0 : nextrel0 V 0 1 := by
      refine ⟨by omega, by omega, by omega, hr0V 1 (by omega) hV, ?_⟩
      intro j hj
      omega
    have hle0 : le0 V 0 1 := ⟨by omega, by omega, Relation.ReflTransGen.single hn0⟩
    have hn1 : nextrel1 V 0 1 := by
      refine ⟨by omega, by omega, by omega, hlt, hle0, ?_⟩
      intro j hj
      have hjle : j ≤ 1 := rtg0_le hj.2.2.2
      have : j = 1 := by omega
      subst this
      omega
    exact ⟨0, by omega, hle0, hlt,
      fun _ => ⟨by omega, by omega, Relation.ReflTransGen.single hn1⟩⟩

/-! ### 239.5 ⟹ ★★★★ **`hlocQ` の遺伝が「2 つの不等式」に決まりました**

    **`t = 1`** … ★ **`entry V 1 0 < entry V 1 1`**（同値、上）
         ⟹ ★ 証人は**根しかない**ので、これが**必要十分**です
    **`t ≥ 2`** … ★ R2 の (ADJ)（距離 ≤ 2）で**証人は窓の中** ⟹ §239.2 の受け皿で移ります

**⟹ ★★★ ですから **(P1) の残りは `entry V 1 0 < entry V 1 1` 1 本**です。**

⚠ **そして `V` の第 1 列は「バッドルートの**次**の列」です。**
**⟹ ★ 核の形（型 B）では `V = [(x0,a,0),(x1,0,0),(x2,b,0)]` ⟹ `entry V 1 0 = a`、`entry V 1 1 = 0`**
**⟹ ⟹ ⛔ **`a < 0` は偽** ⟹ **型 B は `t = 1` で `hlocQ` を破ります**。**

**⟹ ★★ ですが `t = 1` の列は `srow` が 0（行 1 も行 2 も 0）なので、
`hlocQ` の行 1 の条件は **前件が偽**（`0 < entry V 1 1` が偽）⟹ **空虚に真** ✅**

**⟹ ⟹ ★★★ ですから **型 B は `hlocQ` を破りません**。⟹ §236 の読みと一致します。**

⚠ **教訓 14**: 上は**同値**の証明です。**遺伝そのものは、`t = 1` の不等式が
窓ごとに成り立つかにかかっています。⟹ R2 の (ADJ'-d) が**それ**です。** -/

/-! ### 239.6 ★★★ `t = 1` の条件を **ブロックの言葉**に落とします（team-lead の確認依頼）

team-lead:「`t = 1` の比較は**同じブロックの中の 2 列**なので `e*k` が両辺で同じ ⟹ `k` が消える」

**⟹ ★ 前半は正しいです（下で緑）。⟹ ⛔ ですが**後半は自動ではありません**。** -/

theorem wnd_first_two_entry1 {P B : TrioSeq} {j p : ℕ} (hpj : p < j)
    (hlen2 : 1 < j - p) :
    (entry (wnd P B j p) 1 0 < entry (wnd P B j p) 1 1)
      ↔ entry B 1 p < entry B 1 (p + 1) := by
  have hE : ∀ t, t < j - p →
      entry (wnd P B j p) 1 t = entry B 1 (p + t) := by
    intro t ht
    unfold wnd
    rw [entry_window _ ht,
      show P.length + p + t = P.length + (p + t) from by omega, entry_append_right,
      Wset.entry_take (show p + t < j + 1 by omega)]
  rw [hE 0 (by omega), hE 1 (by omega), Nat.add_zero]

/-! ### 239.7 ⚠⚠ **`k` が消えるのは「錐のクラスが同じとき」だけ**です

`entry B 1 x = entry Q 1 x + (if le1 Q 0 x then e*n else 0)` なので、`t = 1` の条件は

    `entry Q 1 p + (if le1 Q 0 p then e*n else 0)
      < entry Q 1 (p+1) + (if le1 Q 0 (p+1) then e*n else 0)`

| `p`（窓の根） | `p+1` | `e*n` |
|---|---|---|
| 錐の中 | 錐の中 | ★ **消える** |
| 錐の外 | 錐の外 | ★ **消える** |
| 錐の外 | 錐の中 | ★ **緩む** |
| **錐の中** | **錐の外** | ⛔ **`n` 依存** ← ★ **`blocker_of_large_k` の射程**（`hinp` ∧ `houtj`） |

**⟹ ★ ですから team-lead の「`k` が消える」は **3/4 のマスでは正しく、1 マスで偽**です。**
**⟹ ⟹ ★★ そして残る 1 マスは **`hcls` を `(p, p+1)` に当てたもの**そのものです。**

**⟹ ⟹ ⟹ ★★★ ですから (FIN) の分母は「**窓の根が錐の中 ∧ 第 1 列が錐の外**」に絞れます。**
**⟹ ★ そこが 0 件なら、`t = 1` の条件は `n` に依らず、`blocker_of_large_k` の射程外です。**

⚠ **教訓 14**: 上の表は **H12 の 4 通りの表と同じもの**です。
**⟹ ★ 「同じブロックの中だから消える」は**十分ではありません**。⟹ ⟹ 錐のクラスが要ります。** -/

/-! ## 240. ★★★★★ `hlocQ` の**行 2 の成分**を「祖先の存在」に書き換えます

team-lead の (COMP-a): 行 2 の成分は **66.8% / 64.7%**、行 1 より **25 ポイント悪い**。
**⟹ ★ そして team-lead の観察「行 2 の破れも定義から孤児」は**正しい**——それを定理にします。**

`z < 2` の断片では `entry M 2 j ≤ 1` なので、`0 < entry M 2 j` は `entry M 2 j = 1`。
**⟹ ★ すると `nextrel2` の始点は `entry M 2 y = 0` に限られ、最小性は
「`y` と `j` の間の `le1` 祖先はすべて行 2 = 1」に化けます。**
**⟹ ⟹ ★★★ ですから **親 = 「行 2 が 0 である最大の `le1` 祖先」**——一意性まで込みで同値です。** -/

/-- **最大の証人**を取り出す道具（下向きの整列）。 -/
theorem exists_max_below {j : ℕ} (P : ℕ → Prop) [DecidablePred P] (h : ∃ y, y < j ∧ P y) :
    ∃ y, y < j ∧ P y ∧ ∀ z, y < z → z < j → ¬ P z := by
  obtain ⟨y0, hy0, hPy0⟩ := h
  have hex : ∃ k, k < j ∧ P (j - 1 - k) := by
    refine ⟨j - 1 - y0, by omega, ?_⟩
    rw [show j - 1 - (j - 1 - y0) = y0 from by omega]; exact hPy0
  classical
  set k0 := Nat.find hex with hk0
  obtain ⟨hk0j, hk0P⟩ := Nat.find_spec hex
  refine ⟨j - 1 - k0, by omega, hk0P, ?_⟩
  intro z hz hzj hPz
  have hlt : j - 1 - z < k0 := by omega
  exact (Nat.find_min hex hlt) ⟨by omega, by rw [show j - 1 - (j - 1 - z) = z from by omega]; exact hPz⟩

open Classical in
/-- ★★★★★ **`z < 2` では「行 2 の親を持つ」＝「行 2 が 0 の `le1` 祖先がある」**。

**⟹ ★ 一意性まで込みの**同値**です。⟹ ⟹ `hasParent` の存在＋一意性を、
`le1` 祖先の**存在だけ**に落とします。** -/
theorem hasParent_two_iff_of_z1 {M : TrioSeq} {j : ℕ} (hj : j < M.length)
    (hz1 : ∀ q, q < M.length → entry M 2 q ≤ 1) (hpos : 0 < entry M 2 j) :
    hasParent M 2 j ↔ ∃ y, y < j ∧ le1 M y j ∧ entry M 2 y = 0 := by
  have hj1 : entry M 2 j = 1 := by have := hz1 j hj; omega
  constructor
  · rintro ⟨y, hy, -⟩
    unfold nextR at hy
    rw [if_neg (by omega), if_neg (by omega)] at hy
    exact ⟨y, hy.2.2.1, hy.2.2.2.2.1, by have := hy.2.2.2.1; omega⟩
  · intro hex
    obtain ⟨y, hyj, ⟨hle1, hz⟩, hmax⟩ :=
      exists_max_below (j := j) (fun y => le1 M y j ∧ entry M 2 y = 0)
        (by obtain ⟨y, h1, h2, h3⟩ := hex; exact ⟨y, h1, h2, h3⟩)
    have hnry : nextrel2 M y j := by
      refine ⟨hle1.1, hj, hyj, by omega, hle1, ?_⟩
      intro q ⟨hq1, hq2⟩
      rcases Nat.lt_or_ge q j with hqj | hqj
      · have hne := hmax q hq1 hqj
        have hq0 : entry M 2 q ≠ 0 := fun h => hne ⟨hq2, h⟩
        have := hz1 q hq2.1
        omega
      · have hle := le1_le' hq2
        rw [show q = j from by omega]
    -- `y` が最大なので最小性が立つ
    refine ⟨y, hnry, ?_⟩
    intro y' hy'
    unfold nextR at hy'
    rw [if_neg (by omega), if_neg (by omega)] at hy'
    by_contra hne
    have hy'z : entry M 2 y' = 0 := by have := hy'.2.2.2.1; omega
    have hy'j : y' < j := hy'.2.2.1
    rcases Nat.lt_or_ge y' y with hlt | hge
    · -- `y'` の最小性を `y` に当てる ⟹ `entry M 2 j ≤ entry M 2 y = 0`
      have := hy'.2.2.2.2.2 y ⟨hlt, hle1⟩
      omega
    · exact hmax y' (by omega) hy'j ⟨hy'.2.2.2.2.1, hy'z⟩

/-! ### 240.1 ★★★★★ ⟹ **行 2 の成分は「錐の中」では無料**です

§240 で「親を持つ ＝ 行 2 が 0 の `le1` 祖先がある」に落ちました。
**⟹ ★★★ そして `hz0`（`entry Q 2 0 = 0`）は **根の行 2 が 0** と言っています。**
**⟹ ⟹ ★★★★★ ですから **`j` が錐の中（`le1 Q 0 j`）なら、根そのものが証人**です。**

**⟹ ⟹ ⟹ ★★ つまり **`hlocQ` の行 2 の成分は「錐の外の列」でしか中身がありません**。** -/

theorem hlocQ_row2_of_cone {M : TrioSeq} {j : ℕ} (hj : j < M.length) (hj0 : 0 < j)
    (hz1 : ∀ q, q < M.length → entry M 2 q ≤ 1) (hz0 : entry M 2 0 = 0)
    (hcone : le1 M 0 j) (hpos : 0 < entry M 2 j) : hasParent M 2 j :=
  (hasParent_two_iff_of_z1 hj hz1 hpos).mpr ⟨0, hj0, hcone, hz0⟩

/-- ⟹ ★ 対偶: **行 2 の成分が破れる列は必ず錐の外**（`hz0` ＋ `hz1` の下で）。 -/
theorem not_le1_zero_of_row2_break {M : TrioSeq} {j : ℕ} (hj : j < M.length) (hj0 : 0 < j)
    (hz1 : ∀ q, q < M.length → entry M 2 q ≤ 1) (hz0 : entry M 2 0 = 0)
    (hpos : 0 < entry M 2 j) (hnp : ¬ hasParent M 2 j) : ¬ le1 M 0 j :=
  fun hc => hnp (hlocQ_row2_of_cone hj hj0 hz1 hz0 hc hpos)

/-! ### 240.2 ⟹ ★★★★ **`Q.take (j+1)` 版**（`hlocQ` が要求する形そのもの）

`hlocQ` の行 2 の成分は `hasParent (Q.take (j+1)) 2 j` です。
**⟹ ★ `Q.take (j+1)` の根は `Q` の根なので `hz0` がそのまま効きます。** -/

theorem hlocQ_row2_take_of_cone {Q : TrioSeq} {j : ℕ} (hj : j < Q.length) (hj0 : 0 < j)
    (hz1 : ∀ q, q < Q.length → entry Q 2 q ≤ 1) (hz0 : entry Q 2 0 = 0)
    (hcone : le1 (Q.take (j + 1)) 0 j) (hpos : 0 < entry Q 2 j) :
    hasParent (Q.take (j + 1)) 2 j := by
  have hlen : (Q.take (j + 1)).length = j + 1 := by
    rw [List.length_take]; omega
  refine hlocQ_row2_of_cone (by omega) hj0 ?_ ?_ hcone ?_
  · intro q hq
    rw [hlen] at hq
    rw [Wset.entry_take (show q < j + 1 by omega)]
    exact hz1 q (by omega)
  · rw [Wset.entry_take (show 0 < j + 1 by omega)]; exact hz0
  · rw [Wset.entry_take (show j < j + 1 by omega)]; exact hpos

/-! ### 240.3 ⟹ ★★ **残差の形**（(ROW2) への注文）

**⟹ ★ ですから (COMP-a) の 66.8% の破れは、**すべて次の形**のはずです:**

    `entry Q 2 j = 1` ∧ **`¬ le1 (Q.take (j+1)) 0 j`（錐の外）**
      ∧ `j` の `le1` 祖先が**すべて行 2 = 1**

**⟹ ⚠ **教訓 27**: R2 には**分母**（`entry Q 2 j = 1` かつ錐の外である列の数）も
一緒に測ってもらってください。⟹ **「0 件」なら分母が 0 かもしれません**。**

⚠ そして **これは `hz0` を使っています**。`hz0` は `TowerP''` の中にあり、
**遺伝は §213 で緑**なので、循環はありません。 -/

/-! ### 240.4 ★★★★★ (R1) を**定理**にします —— **`hlocQ` があれば接頭辞は親を供給しない**

team-lead の (R1)。⚠ そして R2 の (W15)「接頭辞は `hbase` が無いと 12.58% で親を供給する」
との**整合**をここで取ります。

**⟹ ★★★ 答え: `L105.parent_ge_of_inner`（`L105Cap.lean:7480`、前提なし）が
「**後ろが自分の中に親を持てば**、接頭辞は親を供給できない」と言っています。**
**⟹ ⟹ ★★★★ そして `hlocQ` は**まさにその前提**です。⟹ `hnbQ` の代役は要りません。**

⚠ **R2 の 12.58% と矛盾しません**: あちらは**孤児の列**（塔の根が 89.2%）を数えています。
**⟹ ★ `hlocQ` は「孤児でない」を言うので、12.58% の側には入りません。** -/

theorem prefix_no_cross_of_inner {A T : TrioSeq} {i j : ℕ}
    (hj : j + 1 = T.length) (hp : hasParent T i j) :
    ∀ y, y < A.length → ¬ nextR (A ++ T) i y (A.length + j) := by
  intro y hy hnr
  have hTne : T ≠ [] := by intro h; rw [h] at hj; simp at hj
  have hidx : (A ++ T).length - 1 = A.length + j := by
    rw [List.length_append]; omega
  have hT1 : T.length - 1 = j := by omega
  have hge : A.length ≤ y :=
    L105.parent_ge_of_inner (A := A) (T := T) (i := i) hTne
      (by rw [hT1]; exact hp) (by rw [hidx]; exact hnr)
  omega

/-! ### 240.5 ⟹ ★★★ ですから **`hloc` があれば剥がせます**（§230 との合流）

§230 の `hasParent_peel_of_noCross` は「接頭辞が `nextR` の始点でない」を受け取ります。
**⟹ ★ §240.4 がそれを **`hasParent T` だけ**から出します。⟹ ⟹ 循環しません
（前提は `T` の中の話、結論は `A ++ T` の話）。** -/

/-- ★★ 実用形: `A ++ T` の親は必ず `T` の中にある。 -/
theorem parent_in_suffix_of_inner {A T : TrioSeq} {i j y : ℕ}
    (hj : j + 1 = T.length) (hp : hasParent T i j)
    (hnr : nextR (A ++ T) i y (A.length + j)) : A.length ≤ y := by
  by_contra hcon
  exact prefix_no_cross_of_inner hj hp y (by omega) hnr

/-! ### 240.6 ★★★★ 行 2 の成分の**窓への遺伝**（`hlocQ_wnd_of_witnesses` の `h2` を埋めます）

§240.2 を窓に当てるだけです。**⟹ ★ 要るのは 2 つ:**

    (a) **窓の根の行 2 が 0** …… ★ §224（`heredZ2_of_srow2` / `heredZ2_of_p_zero`）
    (b) **その列が窓の錐の中** …… ★ §240.1 で「錐の外でしか破れない」と分かったもの

**⟹ ★★ ですから **行 2 の成分の残差は (b) だけ**です（(a) は §224 でほぼ済み）。** -/

theorem hlocQ_row2_wnd {P B : TrioSeq} {j p : ℕ} (hjB : j < B.length) (hpj : p < j)
    (hz0V : entry (wnd P B j p) 2 0 = 0)
    (hz1V : ∀ q, q < j - p → entry (wnd P B j p) 2 q ≤ 1)
    (hcone : ∀ t, 0 < t → t < j - p → 0 < entry (wnd P B j p) 2 t →
      le1 (wnd P B j p) 0 t) :
    ∀ t, 0 < t → t < j - p → 0 < entry (wnd P B j p) 2 t →
      hasParent ((wnd P B j p).take (t + 1)) 2 t := by
  have hlen : (wnd P B j p).length = j - p := wnd_length hjB hpj
  intro t ht0 htL hpos
  refine hlocQ_row2_take_of_cone (Q := wnd P B j p) (by omega) ht0
    (fun q hq => hz1V q (by omega)) hz0V ?_ hpos
  exact (Wset.le1_take (X := wnd P B j p) (l := t + 1) (by omega) (by omega)).mpr
    (hcone t ht0 htL hpos)

/-! ### 240.7 ⟹ ★★ **行 2 の残差は「窓の錐」だけ**になりました

    ✅ **`hasParent` ⟹ 祖先の存在** …… §240 `hasParent_two_iff_of_z1`
    ✅ **錐の中なら無料** …………… §240.1 `hlocQ_row2_of_cone`
    ✅ **窓への受け皿** ……………… §240.6（上）
    ✅ **窓の根の行 2 = 0** ………… §224（`srow = 2` の段 ／ `p = 0` の段）
    ⛔ **窓の錐** …………………… ★ **`le1 (wnd P B j p) 0 t` が残る 1 点**

**⟹ ⚠ そして (COMP-a) の 66.8% の破れは、**窓の錐の外の列**に限られます。**
**⟹ ★ R2 への注文はそこの分母です。⟹ **教訓 27**。** -/

/-! ## 241. ★★★★★★ **`hlocQ` は「錐の中」では丸ごと無料**です

§240.1 で**行 2 の成分**が錐の中で無料と分かりました。
**⟹ ★★★ 実は**行 1 の成分も**そうです。⟹ ⟹ 2 つの理由が合わさります:**

    (1) クラス条件 `(le1 Q 0 y → le1 Q 0 j)` は、**`le1 Q 0 j` が既にあれば空虚**
    (2) `le1 Q 0 j` の**最後の 1 歩**（`nextrel1 Q y j`）が、証人 `y` をそのまま与える
        ⟹ ★ `nextrel1` は定義に `le0 Q y j` と `entry Q 1 y < entry Q 1 j` を含む

**⟹ ⟹ ⟹ ★★★★★★ ですから **`hlocQ` の中身は「錐の外の列」だけ**です。**
**⟹ ★ (COMP-a) の破れ（行 1 90.9%、行 2 66.8%）は、**すべて錐の外**で起きています。** -/

theorem hlocQ_row1_of_cone {Q : TrioSeq} {j : ℕ} (hj0 : 0 < j) (hcone : le1 Q 0 j) :
    ∃ y, y < j ∧ le0 Q y j ∧ entry Q 1 y < entry Q 1 j ∧ (le1 Q 0 y → le1 Q 0 j) := by
  rcases Relation.ReflTransGen.cases_tail hcone.2.2 with h | ⟨y, -, hstep⟩
  · exact absurd h.symm (by omega)
  · exact ⟨y, hstep.2.2.1, hstep.2.2.2.2.1, hstep.2.2.2.1, fun _ => hcone⟩

open Classical in
/-- ★★★★★★ **`hlocQ` は錐の外の列だけの条件**（`hz0` ＋ `hz1` のもとで）。 -/
theorem hlocQ_iff_outOfCone {Q : TrioSeq}
    (hz1 : ∀ q, q < Q.length → entry Q 2 q ≤ 1) (hz0 : entry Q 2 0 = 0) :
    hlocQ Q ↔ ∀ j, 0 < j → j < Q.length → ¬ le1 Q 0 j →
      ((0 < entry Q 2 j → hasParent (Q.take (j + 1)) 2 j) ∧
       (entry Q 2 j = 0 → 0 < entry Q 1 j →
         ∃ y, y < j ∧ le0 Q y j ∧ entry Q 1 y < entry Q 1 j ∧ (le1 Q 0 y → le1 Q 0 j))) := by
  constructor
  · intro h j hj0 hj _; exact h j hj0 hj
  · intro h j hj0 hj
    by_cases hc : le1 Q 0 j
    · exact ⟨fun hpos => hlocQ_row2_take_of_cone hj hj0 hz1 hz0
        ((Wset.le1_take (X := Q) (l := j + 1) (by omega) (by omega)).mpr hc) hpos,
        fun _ _ => hlocQ_row1_of_cone hj0 hc⟩
    · exact h j hj0 hj hc

/-! ### 241.1 ⟹ ★★★ 「錐の外」の列は**行 1 も行 0 も低い**

**⟹ ★ ですから残差は**ブロッカーの部分木**に閉じ込められました。**
**⟹ ⟹ ★ `L105.not_le1_zero_iff`（`L105Cap.lean:7149`）が「錐の外」を閉じた形にします:**

    `¬ le1 Q 0 q ↔ ∃ y, ReflTransGen (nextrel0 Q) y q ∧ y ≠ 0 ∧ entry Q 1 y ≤ entry Q 1 0`

**⟹ ★★ つまり **`q` の行 0 祖先のどこかにブロッカー `y` がいる**。**
**⟹ ⟹ ★★★ そして R2 の (ADJ'-e) の破れの形（`[(0,0,0), (3,-2,0)]` など 28 種）は
**すべて「行 0 は上がるが行 1 が根より下がる隣接列」＝ ブロッカー**でした。⟹ **一致します**。**

⚠ **教訓 14**: 一致しただけです。**残差はまだ証明されていません。** -/

/-! ### 241.2 ★★★★★ ⟹ **`t = 1` の条件の正体は「第 1 列が錐の中」**

§239.4 は `t = 1` の証人の存在 ⟺ `entry V 1 0 < entry V 1 1` と言いました。
§241 は `hlocQ` が錐の中で無料と言いました。
**⟹ ★★★ 2 つを繋ぐと、**`t = 1` の条件はちょうど「第 1 列が錐の中」**になります。** -/

theorem le1_zero_one_iff {V : TrioSeq} (hV : 1 < V.length)
    (hr0V : ∀ l, 0 < l → l < V.length → entry V 0 0 < entry V 0 l) :
    le1 V 0 1 ↔ entry V 1 0 < entry V 1 1 := by
  constructor
  · intro hc
    obtain ⟨y, hy1, hy2, hy3, hy4⟩ := hlocQ_row1_of_cone (Q := V) (j := 1) (by omega) hc
    exact (hlocQ_first_column_iff hV hr0V).mp ⟨y, hy1, hy2, hy3, hy4⟩
  · intro h
    obtain ⟨y, hy1, -, -, hy4⟩ := (hlocQ_first_column_iff hV hr0V).mpr h
    exact hy4 (by rw [show y = 0 from by omega]; exact le1_self (by omega))

/-! ⟹ ★★ ですから **R2 の (ADJ'-e) と (COMP) は同じものを測っています**:

    `t = 1` の証人がある ⟺ `entry V 1 0 < entry V 1 1` ⟺ **`le1 V 0 1`（錐の中）**

**⟹ ★ そして (ADJ'-e) の破れの形が全部ブロッカーだったのは、**定義そのもの**です。**
**⟹ ⟹ ⚠ ですから (ADJ'-e) の 90.3% は **`hlocQ` の残差そのもの**で、
**新しい情報ではありません**。⟹ **教訓 45**: 同じ量を 2 度測っても検算になりません。** -/

/-! ## 242. ★★★★★ **窓の錐は「大きい列の中で窓の根の子孫」から出ます**（前提なし）

§241 で `hlocQ` の残差が「錐の外の列」だけになりました。
**⟹ ★ 窓の側で必要なのは `le1 V 0 t`（窓の根の子孫）です。**
**⟹ ⟹ ★★★ これは **`le1 T (s+0) (s+t)` から前提なしで出ます**。⟹ 以下で緑にします。**

**⚠ 逆向き（窓 ⟹ 大きい列）は「根を飛び越えない」が要ります**——そちらは使いません。 -/

/-- ★★ `le0` の**逆向き**（窓 ⟹ 元の列）。`nextrel0_window` の鎖を持ち上げるだけ。 -/
theorem le0_window' {T : TrioSeq} {s L a b : ℕ} (hL : s + L ≤ T.length)
    (ha : a < L) (hb : b < L) (h : le0 ((T.drop s).take L) a b) :
    le0 T (s + a) (s + b) := by
  have hlen := window_length hL
  obtain ⟨-, -, hrtg⟩ := h
  refine ⟨by omega, by omega, ?_⟩
  have key : ∀ c, Relation.ReflTransGen (nextrel0 ((T.drop s).take L)) a c →
      c < L ∧ Relation.ReflTransGen (nextrel0 T) (s + a) (s + c) := by
    intro c hc
    induction hc with
    | refl => exact ⟨ha, Relation.ReflTransGen.refl⟩
    | @tail x y hx hxy ih =>
        have hyL : y < L := by
          have := hxy.2.1; rw [hlen] at this; exact this
        exact ⟨hyL, ih.2.tail ((nextrel0_window hL ih.1 hyL).mp hxy)⟩
  exact (key b hrtg).2

/-- ★★★★ **`nextrel1` は元の列から窓へ移ります**（前提なし）。

最小性は `le0` の**逆向き**（`le0_window'`）で元の列の最小性に帰着します。 -/
theorem nextrel1_window_of {T : TrioSeq} {s L a b : ℕ} (hL : s + L ≤ T.length)
    (ha : a < L) (hb : b < L) (h : nextrel1 T (s + a) (s + b)) :
    nextrel1 ((T.drop s).take L) a b := by
  have hlen := window_length hL
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨by omega, by omega, by omega, ?_, le0_window hL ha hb h5, ?_⟩
  · rw [entry_window T (i := 1) hb, entry_window T (i := 1) ha]; omega
  · intro q ⟨hq1, hq2⟩
    have hqL : q < L := by
      have := hq2.1; rw [hlen] at this; omega
    have := h6 (s + q) ⟨by omega, le0_window' hL hqL hb hq2⟩
    rw [entry_window T (i := 1) hb, entry_window T (i := 1) hqL]
    exact this

/-- ★★★★★ ⟹ **`le1` も元の列から窓へ移ります**（前提なし）。 -/
theorem le1_window {T : TrioSeq} {s L a b : ℕ} (hL : s + L ≤ T.length)
    (ha : a < L) (hb : b < L) (h : le1 T (s + a) (s + b)) :
    le1 ((T.drop s).take L) a b := by
  have hlen := window_length hL
  obtain ⟨-, -, hrtg⟩ := h
  refine ⟨by omega, by omega, ?_⟩
  have key : ∀ c, Relation.ReflTransGen (nextrel1 T) (s + a) c → c ≤ s + b →
      ∃ c', c = s + c' ∧ c' < L ∧
        Relation.ReflTransGen (nextrel1 ((T.drop s).take L)) a c' := by
    intro c hc
    induction hc with
    | refl => intro _; exact ⟨a, rfl, ha, Relation.ReflTransGen.refl⟩
    | @tail x y hx hxy ih =>
        intro hyb
        have hxle : x < y := hxy.2.2.1
        obtain ⟨x', rfl, hx'L, hch⟩ := ih (by omega)
        obtain ⟨y', rfl⟩ : ∃ y', y = s + y' := ⟨y - s, by omega⟩
        exact ⟨y', rfl, by omega, hch.tail (nextrel1_window_of hL hx'L (by omega) hxy)⟩
  obtain ⟨b', hb'eq, -, hres⟩ := key (s + b) hrtg (le_refl _)
  rw [show b' = b from by omega] at hres
  exact hres

/-! ### 242.1 ⟹ ★★★ **`hlocQ_row2_wnd` の `hcone` が「大きい列の錐」に化けました**

    `le1 (P ++ B.take (j+1)) (P.length + p) (P.length + p + t)`  ⟹  `le1 (wnd P B j p) 0 t`

**⟹ ★★ ですから (CONE) の測るべき量は「**窓の根の行 1 の子孫か**」に確定しました。**
**⟹ ⟹ ★ そして **前提が要りません**（「根を飛び越えない」は逆向きにしか要りません）。** -/

theorem le1_wnd_of {P B : TrioSeq} {j p t : ℕ} (hjB : j < B.length) (hpj : p < j)
    (ht : t < j - p)
    (h : le1 (P ++ B.take (j + 1)) (P.length + p) (P.length + p + t)) :
    le1 (wnd P B j p) 0 t := by
  have hTl : (P ++ B.take (j + 1)).length = P.length + (j + 1) := by
    rw [List.length_append, List.length_take, Nat.min_eq_left (by omega)]
  unfold wnd
  refine le1_window (T := P ++ B.take (j + 1)) (s := P.length + p) (L := j - p)
    (by omega) (by omega) ht ?_
  rw [Nat.add_zero]
  exact h

/-! ### 242.2 ★★★★★ **窓の `hlocQ` の受け皿**（§241 を窓に当てた形）

§241 は「`hlocQ` は錐の中では丸ごと無料」と言いました。⟹ ★ 窓にもそのまま当たります。
**⟹ ⟹ ★★★ ですから **窓の `hlocQ` に要るのは「窓の錐の外の列」だけ**です。** -/

open Classical in
theorem hlocQ_wnd_of_outOfCone {P B : TrioSeq} {j p : ℕ} (hjB : j < B.length) (hpj : p < j)
    (hz0V : entry (wnd P B j p) 2 0 = 0)
    (hz1V : ∀ q, q < j - p → entry (wnd P B j p) 2 q ≤ 1)
    (hout : ∀ t, 0 < t → t < j - p → ¬ le1 (wnd P B j p) 0 t →
      ((0 < entry (wnd P B j p) 2 t →
          hasParent ((wnd P B j p).take (t + 1)) 2 t) ∧
       (entry (wnd P B j p) 2 t = 0 → 0 < entry (wnd P B j p) 1 t →
         ∃ y, y < t ∧ le0 (wnd P B j p) y t ∧
           entry (wnd P B j p) 1 y < entry (wnd P B j p) 1 t ∧
           (le1 (wnd P B j p) 0 y → le1 (wnd P B j p) 0 t)))) :
    hlocQ (wnd P B j p) := by
  have hlen : (wnd P B j p).length = j - p := wnd_length hjB hpj
  refine (hlocQ_iff_outOfCone (Q := wnd P B j p) (fun q hq => hz1V q (by omega)) hz0V).mpr ?_
  intro t ht0 htL hnc
  exact hout t ht0 (by omega) hnc

/-! ### 242.3 ⟹ ★★★ **(P1) の残りは 1 行で書けます**

    ✅ **窓の根の行 2 = 0** ……… §224
    ✅ **窓の行 2 ≤ 1** ………… `entry2_wnd` ＋ `hz1(Q)`
    ✅ **錐の中は丸ごと無料** …… §241 ＋ §242.2（上）
    ✅ **大きい列の錐 ⟹ 窓の錐** … §242 `le1_wnd_of`（**前提なし**）
    ⛔ **窓の錐の外の列** ……… ★ **これだけ**

**⟹ ★★ そして「窓の錐の外」は `L105.not_le1_zero_iff` で
**「窓の根より行 1 が低い行 0 祖先がいる」**——**ブロッカーの部分木**です。**

**⟹ ⟹ ★★★ ですから残差は **「ブロッカーの部分木の中で `hlocQ` が立つか」** 1 点です。**

⚠ **教訓 14**: これは**形の確定**です。**まだ証明されていません。** -/

/-! ## 243. ★★★★★★ **`hlocQ` の行 1 の成分は「行 1 の孤児でない」だけ**

§241 で「錐の中なら無料」と分かりましたが、**もっと弱い十分条件**があります。

**⟹ ★★★ `nextrel1 Q y j` が **1 本でもあれば** 行 1 の成分は立ちます。⟹ 理由:**

    `nextrel1` の定義に `y < j`・`le0 Q y j`・`entry Q 1 y < entry Q 1 j` が**全部入っている**
    ⟹ ★★ クラス条件 `le1 Q 0 y → le1 Q 0 j` も、**その 1 歩を継ぎ足すだけ**で出る

**⟹ ⟹ ★★★★★ ですから **行 1 の成分が破れるのは「行 1 の孤児」だけ**です。**
**⟹ ⟹ ⟹ ★ これは team-lead の (Q1)「破れる列は 100% 孤児」の**証明**です。** -/

theorem hlocQ_row1_of_nextrel1 {Q : TrioSeq} {j y : ℕ} (h : nextrel1 Q y j) :
    ∃ y, y < j ∧ le0 Q y j ∧ entry Q 1 y < entry Q 1 j ∧ (le1 Q 0 y → le1 Q 0 j) :=
  ⟨y, h.2.2.1, h.2.2.2.2.1, h.2.2.2.1,
    fun hc => ⟨hc.1, h.2.1, hc.2.2.tail h⟩⟩

/-- ⟹ ★ 対偶: **行 1 の成分が破れる列は行 1 の孤児**（`nextrel1` の始点が 1 つも無い）。 -/
theorem no_nextrel1_of_row1_break {Q : TrioSeq} {j : ℕ}
    (hbr : ¬ ∃ y, y < j ∧ le0 Q y j ∧ entry Q 1 y < entry Q 1 j ∧
      (le1 Q 0 y → le1 Q 0 j)) :
    ∀ y, ¬ nextrel1 Q y j :=
  fun _ h => hbr (hlocQ_row1_of_nextrel1 h)

/-! ### 243.1 ⟹ ★★ **孤児 ⟹ 錐の外**（§241 との入れ子）

`le1 Q 0 j` は `0 < j` なら **1 歩以上の鎖**なので、最後の 1 歩が `nextrel1` の始点を与えます。
**⟹ ★ ですから **錐の中 ⟹ 孤児でない**。⟹ ⟹ **孤児 ⟹ 錐の外**（§241 の逆は言えません）。**
**⟹ ⟹ ★★ つまり **「行 1 の孤児」は「錐の外」より真に強い条件**です。⟹ 残差がさらに縮みました。** -/

theorem not_orphan_of_cone {Q : TrioSeq} {j : ℕ} (hj0 : 0 < j) (hc : le1 Q 0 j) :
    ∃ y, nextrel1 Q y j := by
  rcases Relation.ReflTransGen.cases_tail hc.2.2 with h | ⟨y, -, hstep⟩
  · exact absurd h.symm (by omega)
  · exact ⟨y, hstep⟩

/-! ### 243.2 ★★★ **行 2 の成分も同じ形**にできます

§240 は「行 2 の親を持つ ⟺ 行 2 が 0 の `le1` 祖先がある」でした。
**⟹ ★ ですから **行 1 の親が行 2 = 0 なら、それがそのまま証人**です。** -/

theorem hlocQ_row2_of_nextrel1 {Q : TrioSeq} {j y : ℕ} (hj : j < Q.length)
    (hz1 : ∀ q, q < Q.length → entry Q 2 q ≤ 1) (hpos : 0 < entry Q 2 j)
    (h : nextrel1 Q y j) (hy2 : entry Q 2 y = 0) : hasParent Q 2 j :=
  (hasParent_two_iff_of_z1 hj hz1 hpos).mpr
    ⟨y, h.2.2.1, ⟨h.1, h.2.1, Relation.ReflTransGen.single h⟩, hy2⟩

/-! ### 243.3 ⟹ ★★★★ **残差の最終形**

    **行 1** … 破れるのは **`j` が行 1 の孤児**のときだけ（§243）
    **行 2** … 破れるのは **`j` の `le1` 祖先が全部行 2 = 1** のときだけ（§240）
              ⟹ ★ そして **`j` が行 1 の孤児なら `le1` 祖先は `j` 自身だけ** ⟹ 破れる
              ⟹ ⟹ ★★ **行 2 も「行 1 の孤児」に帰着**します

**⟹ ★★★★★ ですから **`hlocQ` の残差は「行 1 の孤児が出るか」1 点**です。**
**⟹ ⟹ ★ team-lead の (Q1)「破れる列は 100% 孤児」は、**測るまでもなく定理**でした。**

⚠ **教訓 45**: (Q1) は `hlocQ` の言い換えを測っていました。**独立な情報ではありません。**

**⟹ ⚠ そして **孤児が出ないこと**は測定では出ません（H12 の `blocker_of_large_k` の教訓）。**
**⟹ ★ ですから次に要るのは「**窓の中で行 1 の孤児は窓の根だけ**」の証明です。** -/

/-! ## 244. ★★★★★★ **クラス条件は無料**でした —— (COMP-b) の証明

§243 で「`nextrel1` の始点が 1 本あれば行 1 の成分は立つ」と分かりました。
**⟹ ★★★ そして **`nextrel1` の始点は「行 1 が小さい `le0` 祖先」から作れます**:**

    候補のうち**最大のもの**を取れば、最小性 `∀ q, y < q ∧ le0 M q t → entry M 1 t ≤ entry M 1 q`
    は**自動**（`q < t` なら最大性、`q = t` なら自明、`q > t` は `le0` の単調性で不可能）

**⟹ ⟹ ★★★★★★ ですから **`hlocQ` の行 1 の成分は 3 つの連言に縮みます**:**

    `∃ y, y < j ∧ le0 Q y j ∧ entry Q 1 y < entry Q 1 j`     ← ★ **クラス条件が消える**

**⟹ ★ これは R2 の (COMP-b)「クラス条件だけが合わない例は 0.0000%」の**証明**です。**
**⟹ ⟹ ★★ そして **窓への移送が楽になります**（`le0_window` ＋ `entry_window` だけ）。** -/

open Classical in
theorem exists_nextrel1_of_le0_lt {M : TrioSeq} {t : ℕ} (ht : t < M.length)
    (h : ∃ y, y < t ∧ le0 M y t ∧ entry M 1 y < entry M 1 t) :
    ∃ y, nextrel1 M y t := by
  obtain ⟨y, hyt, ⟨hle0, hlt⟩, hmax⟩ :=
    exists_max_below (j := t) (fun y => le0 M y t ∧ entry M 1 y < entry M 1 t)
      (by obtain ⟨y, h1, h2, h3⟩ := h; exact ⟨y, h1, h2, h3⟩)
  refine ⟨y, hle0.1, ht, hyt, hlt, hle0, ?_⟩
  intro q ⟨hq1, hq2⟩
  rcases Nat.lt_or_ge q t with hqt | hqt
  · by_contra hcon
    exact hmax q hq1 hqt ⟨hq2, by omega⟩
  · have := le0_le' hq2
    rw [show q = t from by omega]

/-- ★★★★★★ ⟹ **`hlocQ` の行 1 の成分は 3 連言と同値**（クラス条件は無料）。 -/
theorem hlocQ_row1_iff {Q : TrioSeq} {j : ℕ} (hj : j < Q.length) :
    (∃ y, y < j ∧ le0 Q y j ∧ entry Q 1 y < entry Q 1 j ∧ (le1 Q 0 y → le1 Q 0 j))
      ↔ (∃ y, y < j ∧ le0 Q y j ∧ entry Q 1 y < entry Q 1 j) := by
  constructor
  · rintro ⟨y, h1, h2, h3, -⟩; exact ⟨y, h1, h2, h3⟩
  · intro h
    obtain ⟨y, hy⟩ := exists_nextrel1_of_le0_lt hj h
    exact hlocQ_row1_of_nextrel1 hy

/-! ### 244.1 ⟹ ★★★★ **`hlocQ` の書き換え形**

**⟹ ★ `hlocQ` は次と同値です（`hz1` ＋ `hz0` は要りません）:** -/

theorem hlocQ_iff_simple {Q : TrioSeq} :
    hlocQ Q ↔ ∀ j, 0 < j → j < Q.length →
      (0 < entry Q 2 j → hasParent (Q.take (j + 1)) 2 j) ∧
      (entry Q 2 j = 0 → 0 < entry Q 1 j →
        ∃ y, y < j ∧ le0 Q y j ∧ entry Q 1 y < entry Q 1 j) := by
  constructor
  · intro h j hj0 hj
    exact ⟨(h j hj0 hj).1, fun hz hp => (hlocQ_row1_iff hj).mp ((h j hj0 hj).2 hz hp)⟩
  · intro h j hj0 hj
    exact ⟨(h j hj0 hj).1, fun hz hp => (hlocQ_row1_iff hj).mpr ((h j hj0 hj).2 hz hp)⟩

/-! ### 244.2 ⟹ ★★★ **窓への移送が 2 本で済みます**

    `le0` …… ✅ §238 `le0_window`（前提なし）
    行 1 … ✅ `entry_window`（前提なし）

**⟹ ★★ ですから残るのは **「証人 `y` を `p` 以上に取れるか」**だけ。⟹ (ADJ) そのものです。**
**⟹ ⟹ ★ そして §239.4 で **`t = 1` なら候補は根しかない**と分かっています。**

⚠ **教訓 45**: (COMP-b) は測る必要がありませんでした。**定義から出ます。** -/

/-! ## 245. ★★★★★★ **「根が行 0 でも行 1 でも最小」なら錐は全体**

§244 の `exists_nextrel1_of_le0_lt` を**繰り返し適用**するだけです。

    `t > 0` なら根が候補（`le0 V 0 t` ＋ `entry V 1 0 < entry V 1 t`）⟹ `nextrel1` の始点 `y < t` が居る
    ⟹ ★ 強い帰納法で `le1 V 0 y` ⟹ 1 歩継いで `le1 V 0 t`

**⟹ ★★★★★ ですから **`hr0` ＋「根が行 1 で最小」⟹ 全列が錐の中**。**
**⟹ ⟹ ★★ そして §241 が「錐の中なら `hlocQ` は無料」と言うので、**`hlocQ` が丸ごと出ます**。** -/

theorem le1_root_of_root_lt {V : TrioSeq}
    (hr0V : ∀ l, 0 < l → l < V.length → entry V 0 0 < entry V 0 l)
    (h1 : ∀ l, 0 < l → l < V.length → entry V 1 0 < entry V 1 l) :
    ∀ t, t < V.length → le1 V 0 t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · exact le1_self (by omega)
    · obtain ⟨y, hy⟩ := exists_nextrel1_of_le0_lt (M := V) ht
        ⟨0, ht0, L105.le0_zero_of_shallow (fun l hl1 hl => hr0V l (by omega) hl) ht,
          h1 t ht0 ht⟩
      have hyt : y < t := hy.2.2.1
      exact ⟨by omega, ht, (ih y hyt (by omega)).2.2.tail hy⟩

/-- ★★★★★★ ⟹ **`hlocQ` の十分条件**: `hr0` ＋ 根が行 1 で最小 ＋ `hz0` ＋ `hz1`。 -/
theorem hlocQ_of_root_lt {V : TrioSeq}
    (hr0V : ∀ l, 0 < l → l < V.length → entry V 0 0 < entry V 0 l)
    (h1 : ∀ l, 0 < l → l < V.length → entry V 1 0 < entry V 1 l)
    (hz0V : entry V 2 0 = 0) (hz1V : ∀ q, q < V.length → entry V 2 q ≤ 1) :
    hlocQ V := by
  refine (hlocQ_iff_outOfCone hz1V hz0V).mpr ?_
  intro j hj0 hj hnc
  exact absurd (le1_root_of_root_lt hr0V h1 j hj) hnc

/-! ### 245.1 ⟹ ★★★★ **窓版**（残差が 1 本になりました）

    ✅ `hr0(V)` …… §221 `hr0_wnd`（**前提なし**）
    ✅ `hz0(V)` …… §224（`srow = 2` の段 ／ `p = 0` の段）
    ✅ `hz1(V)` …… `entry2_wnd` ＋ `hz1(Q)`
    ⛔ **根が行 1 で最小** … ★ **これだけ**（＝ **窓の根がブロッカーでない**） -/

theorem hlocQ_wnd_of_root_lt {P B : TrioSeq} {j p : ℕ} (hjB : j < B.length) (hpj : p < j)
    (hr0V : ∀ l, 0 < l → l < j - p →
      entry (wnd P B j p) 0 0 < entry (wnd P B j p) 0 l)
    (hz0V : entry (wnd P B j p) 2 0 = 0)
    (hz1V : ∀ q, q < j - p → entry (wnd P B j p) 2 q ≤ 1)
    (hroot1 : ∀ t, 0 < t → t < j - p →
      entry (wnd P B j p) 1 0 < entry (wnd P B j p) 1 t) :
    hlocQ (wnd P B j p) := by
  have hlen : (wnd P B j p).length = j - p := wnd_length hjB hpj
  exact hlocQ_of_root_lt
    (fun l hl0 hl => hr0V l hl0 (by omega)) (fun l hl0 hl => hroot1 l hl0 (by omega))
    hz0V (fun q hq => hz1V q (by omega))

/-! ### 245.2 ⚠⚠ **残差 `hroot1` は `h1out` と同じもの**です —— **正直に書きます**

**⟹ ⛔ `hroot1`（窓の根が行 1 で最小）は、私が §184 で潰し、H12 が `blocker_of_large_k` で
「塔が伸びれば**必ず**壊れる」と証明した **`h1out` そのもの**です。**

**⟹ ★ ただし §239.6/§239.7 で分かったとおり、`e*n` が効くのは**次の 1 マスだけ**です:**

    **窓の根 `p` が錐の中** ∧ **`p+t` が錐の外**

**⟹ ★★ そして §243 が「`p+t` が錐の外なら `nextrel1` の始点も錐の外」と言っています。**
**⟹ ⟹ ⚠ ですが `hroot1` は**根を証人に固定**しているので、その逃げ道を使えません。**

**⟹ ⟹ ⟹ ★★★ ですから **`hroot1` は強すぎます**。⟹ **§244 の 3 連言に戻すべき**です:**

    `∃ y, y < t ∧ le0 V y t ∧ entry V 1 y < entry V 1 t`   ← ★ **証人は根でなくてよい**

**⟹ ★ §245 は「一番強い十分条件」を緑にしたものです。⟹ **本命はこの弱い形**です。**

⚠ **教訓 14**: `hlocQ_of_root_lt` は緑ですが、**前提が満たされる保証はありません**。 -/

/-! ## 246. ★★★★★ **窓の `hlocQ` の行 1 の成分＝「証人が窓の中」** —— **同値**にします

§244 で行 1 の成分は 3 連言になりました。⟹ ★ 窓と元の列で **`le0` は両方向に移ります**
（§238 `le0_window` ／ §242 `le0_window'`、**どちらも前提なし**）。
**⟹ ⟹ ★★★ ですから **残差はちょうど「証人が `p` 以上に取れるか」**——**同値**です。**

⚠ **教訓 45**: **反例の形を先に書きます**。証人が `p` 未満なら**窓では本当に破れます**。 -/

theorem wnd_row1_witness_iff {P B : TrioSeq} {j p t : ℕ} (hjB : j < B.length) (hpj : p < j)
    (ht : t < j - p) :
    (∃ y', y' < t ∧ le0 (wnd P B j p) y' t ∧
       entry (wnd P B j p) 1 y' < entry (wnd P B j p) 1 t)
      ↔ (∃ y, p ≤ y ∧ y < p + t ∧
           le0 (P ++ B.take (j + 1)) (P.length + y) (P.length + (p + t)) ∧
           entry (P ++ B.take (j + 1)) 1 (P.length + y)
             < entry (P ++ B.take (j + 1)) 1 (P.length + (p + t))) := by
  set T := P ++ B.take (j + 1) with hT
  have hTl : T.length = P.length + (j + 1) := by
    rw [hT, List.length_append, List.length_take, Nat.min_eq_left (by omega)]
  have hL : P.length + p + (j - p) ≤ T.length := by omega
  have hE : ∀ q, q < j - p →
      entry (wnd P B j p) 1 q = entry T 1 (P.length + p + q) := by
    intro q hq; unfold wnd; rw [← hT, entry_window T (i := 1) hq]
  constructor
  · rintro ⟨y', hy't, hle0, hlt⟩
    refine ⟨p + y', by omega, by omega, ?_, ?_⟩
    · have := le0_window' (T := T) (s := P.length + p) (L := j - p)
        hL (show y' < j - p by omega) ht (by unfold wnd at hle0; rw [← hT] at hle0; exact hle0)
      rw [show P.length + p + y' = P.length + (p + y') from by omega,
        show P.length + p + t = P.length + (p + t) from by omega] at this
      exact this
    · rw [hE y' (by omega), hE t ht] at hlt
      rw [show P.length + (p + y') = P.length + p + y' from by omega,
        show P.length + (p + t) = P.length + p + t from by omega]
      exact hlt
  · rintro ⟨y, hpy, hyt, hle0, hlt⟩
    refine ⟨y - p, by omega, ?_, ?_⟩
    · unfold wnd; rw [← hT]
      refine le0_window (T := T) (s := P.length + p) (L := j - p)
        hL (show y - p < j - p by omega) ht ?_
      rw [show P.length + p + (y - p) = P.length + y from by omega,
        show P.length + p + t = P.length + (p + t) from by omega]
      exact hle0
    · rw [hE (y - p) (by omega), hE t ht,
        show P.length + p + (y - p) = P.length + y from by omega,
        show P.length + p + t = P.length + (p + t) from by omega]
      exact hlt

/-! ### 246.1 ⟹ ★★★ **残差の最終形**（`hlocQ` の行 1 の成分）

    窓で `hlocQ` の行 1 が立つ ⟺ **`p+t` の証人を `[p, p+t)` の中に取れる**

**⟹ ★ そして §244 の `exists_nextrel1_of_le0_lt` は**最大の証人**を作ります。**
**⟹ ⟹ ★★ ですから **「最大の証人 `y*` が `p` 以上か」**が正確な残差です。**
**⟹ ⟹ ⟹ ⛔ `y* < p` なら、`nextrel1` の最小性により
**`[p, p+t)` の `le0` 祖先はすべて行 1 が `p+t` 以上**——⟹ **窓では本当に破れます**。**

**⟹ ★ R2 の 90.3% / 95.5〜96.9% は、この量そのものです。⟹ **100% ではありません**。**
**⟹ ⟹ ⚠ ですから **`hlocQ` の遺伝はこのままでは偽**です。⟹ 追加の前提が要ります。** -/

/-! ## 247. ★★★★★★ **窓の根が錐の外なら、窓は丸ごと錐の外** ⟹ `e*n` が完全に消えます

§246 で残差が「証人が窓の中か」に確定しました。**⟹ ★ ここで**二分法**が効きます。**

    **窓の根 `p` が錐の外** ⟹ ★★★ 窓の全列が錐の外 ⟹ **持ち上げが一切無い**
                          ⟹ ⟹ **`e*n` が完全に消える** ⟹ **`Q` の話に還元**
    **窓の根 `p` が錐の中** ⟹ ⚠ 混ざりうる（`blocker_of_large_k` の射程）

**⟹ ★ 前半を緑にします。⟹ ⟹ `L105.not_le1_zero_iff`（`L105Cap.lean:7149`）だけで出ます。** -/

theorem not_le1_of_not_le1_le0 {Q : TrioSeq}
    (hr : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    {p q : ℕ} (hq : q < Q.length) (hnp : ¬ le1 Q 0 p) (hle0 : le0 Q p q) :
    ¬ le1 Q 0 q := by
  have hp : p < Q.length := hle0.1
  obtain ⟨y, hy1, hy2, hy3⟩ := (L105.not_le1_zero_iff hr hp).mp hnp
  exact (L105.not_le1_zero_iff hr hq).mpr ⟨y, hy1.trans hle0.2.2, hy2, hy3⟩

/-- ★★★★★ ⟹ **窓の根が錐の外なら、窓の全列が錐の外**。 -/
theorem wnd_all_out_of_cone {Q : TrioSeq}
    (hr : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    {p : ℕ} (hnp : ¬ le1 Q 0 p)
    (hsub : ∀ q, p ≤ q → q < Q.length → le0 Q p q) :
    ∀ q, p ≤ q → q < Q.length → ¬ le1 Q 0 q :=
  fun q hpq hq => not_le1_of_not_le1_le0 hr hq hnp (hsub q hpq hq)

/-! ### 247.1 ⟹ ★★★ **これが `hcls` の正体**です

§236.2 で置いた `hcls`（証人と的が同じ錐のクラス）は、
**「窓の根が錐の外」の場合には自動**です（両方とも錐の外なので）。

**⟹ ★ ですから残るのは **「窓の根が錐の中」の場合**だけ。**
**⟹ ⟹ ★★ そしてそのとき、`p` は錐の中なので `entry Q 1 0 < entry Q 1 p`。**
**⟹ ⟹ ⟹ ★★★ `p+t` が錐の外なら、そのブロッカー `y`（`entry Q 1 y ≤ entry Q 1 0`）は
**`p` より後ろ**にいます。⟹ ⟹ **`y < p` なら `p` 自身も錐の外**になってしまうからです。**

**⟹ ★★★★ つまり **「窓の根が錐の中」の場合、ブロッカーは必ず窓の中**にいます。**
**⟹ ⟹ ★ そして **窓の中のブロッカーは持ち上げられません** ⟹ `e*n` はそこでも消えます。**

⚠ **これは §246 の残差（証人が窓の中）を**直接は**閉じません**。
ブロッカー `y` が「行 1 が `p+t` より小さい」とは限らないからです。
**⟹ ★ ですが **`e*n` の問題は完全に消えました**。⟹ 残るのは `Q` だけの話です。** -/

theorem blocker_in_window {Q : TrioSeq}
    (hr : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    {p q : ℕ} (hq : q < Q.length) (hpc : le1 Q 0 p) (hqc : ¬ le1 Q 0 q) :
    ∃ y, Relation.ReflTransGen (nextrel0 Q) y q ∧ y ≠ 0 ∧
      entry Q 1 y ≤ entry Q 1 0 ∧ ¬ (y < p ∧ le0 Q y p) := by
  obtain ⟨y, hy1, hy2, hy3⟩ := (L105.not_le1_zero_iff hr hq).mp hqc
  refine ⟨y, hy1, hy2, hy3, ?_⟩
  rintro ⟨hyp, hyle⟩
  exact absurd ((L105.not_le1_zero_iff hr hpc.2.1).mpr ⟨y, hyle.2.2, hy2, hy3⟩) (by
    intro h; exact h hpc)

/-! ## 248. ⛔⛔ **`HeredNB` は偽です** —— 反例を貼ります（教訓 45）

§246 で「窓の `hlocQ` ⟺ 証人が窓の中」と**同値**にしました。
**⟹ ★ ですから **証人が窓の外にある例**を 1 つ作れば `HeredNB` は落ちます。**
**⟹ ⟹ ★★ R2 が §R227 で貼った形（`[(1,2,0), (2,1,0)]`）が**そのまま**使えます。**

    `B = [(0,0,0), (1,2,0), (2,1,0), (3,9,0)]`,  `j = 3`,  `p = 1`,  `P = []`
    ⟹ `wnd [] B 3 1 = [(1,2,0), (2,1,0)]`
    ⟹ ★ 列 1 は `srow = 1`（行 2 = 0、行 1 = 1 > 0）だが、
         候補は `y = 0` しかなく `entry V 1 0 = 2 < 1` は**偽**

⚠ **`Q` のほうでは証人があります**（根 `(0,0,0)` の行 1 = 0 < 1、`le0` も `0 → 1 → 2` で通る）。
**⟹ ★★★ ですから **「窓で切ると証人が外に落ちる」**——これが破れの正体です。** -/

theorem heredNB_false : ¬ HeredNB := by
  intro h
  have hw : wnd [] [(0, 0, 0), (1, 2, 0), (2, 1, 0), (3, 9, 0)] 3 1
      = [(1, 2, 0), (2, 1, 0)] := by unfold wnd; rfl
  have hloc := h [] [(0, 0, 0), (1, 2, 0), (2, 1, 0), (3, 9, 0)] 3 1
    (by omega) (by decide)
  rw [hw] at hloc
  obtain ⟨-, hrow1⟩ := hloc 1 (by omega) (by decide)
  obtain ⟨y, hy1, -, hylt, -⟩ := hrow1 (by decide) (by decide)
  rw [show y = 0 from by omega] at hylt
  exact absurd hylt (by decide)

/-! ### 248.1 ⟹ ★★★ **これで 5 番目の不変量が落ちました**

| 条件 | 運命 |
|---|---|
| `hbase` | 遺伝 0%（§207 で**証明**） |
| `rsum` | 遺伝 0%（§227 で**証明**） |
| `h1out` | H12 `blocker_of_large_k`（**必ず壊れる**） |
| `hnbQ` | 核の形で偽（§235 で**証明**） |
| **`HeredNB`（＝ `hlocQ` の窓遺伝）** | ⛔ **偽**（§248、**証明**） |

**⟹ ⚠ `HeredNB` は**前提なしで全ての `P B j p`** を量化していました。**
**⟹ ★★ ですから **`B ∈ W u` などの前提を足す**しかありません。⟹ ⟹ そこが次の設計です。**

**⟹ ★★★ そして §247 が示したとおり、**`e*n` はもう問題ではありません**。**
**⟹ ⟹ ★ 残るのは純粋に **`Q` の中で証人が窓に入るか**——`W` の構造が要ります。**

### ⛔⛔⛔ 248.2 **`mTowerClosedS_of_residues` は空虚になりました**

`mTowerClosedS_of_residues` は `hnbh : HeredNB` を前提に取っています。
**⟹ ⛔⛔ §248 で `HeredNB` が**偽**と分かったので、この定理は **前提が満たせません**。**
**⟹ ⟹ ⚠ **緑であること・`sorry` が無いことは、何も保証しません**（教訓 14）。**

**⟹ ★ 直し方は 1 つ: `HeredNB` に **`B ∈ W u`（またはブロックが `W` 由来）**を足すこと。**
**⟹ ⟹ ★★ すると `HeredNB` は `RootNB`（`∀ Q ∈ W u, hlocQ Q`）の**系**になります——
**窓が `W` の元だと言えれば**。⟹ ⟹ ⚠ `Lind.graft_take_drop` は `graft` の**向き**が逆で、
`y ∈ W u` から窓 `y.drop p` が `W m` に入ることは**まだ言えていません**。**

**⟹ ⟹ ⟹ ★★★ ですから次の設計課題は **「窓は `W` の元か」**です。** -/

/-! ## 249. ⛔⛔⛔ **`hpar` / `hpe` を足しても `HeredNB` は偽**です

§248 の反例は `p = 1` を勝手に取っていました。⚠ ですが**使用箇所（`hsnoc_pos`）は
`hpar`（親が居る）と `hpe`（親 ＝ `P.length + p`）を持っています**。
**⟹ ★ 実際 §248 の `B` では **親は 2** なので、窓は長さ 1 になり `hlocQ` は空虚です。**
**⟹ ⟹ ★★ ですから **`HeredNB` を締めれば直る**——と期待するのが自然です。**

**⟹ ⛔⛔ ですが **締めても偽**です。⟹ ⟹ 別の反例を貼ります:**

    `B = [(0,0,0), (1,5,0), (2,1,0), (2,9,0)]`
    ⟹ 行 0 = [0,1,2,2]、行 1 = [0,5,1,9]、行 2 ≡ 0
    ⟹ ★ 列 3 の `srow` は 1、**親は 1**（列 2 は `le0` 祖先でない: 行 0 が 2 = 2 で上がらない）
    ⟹ ⟹ 窓 = `[(1,5,0), (2,1,0)]` ⟹ ⛔ `t = 1` で `entry V 1 0 = 5 < 1` は**偽**

**⟹ ★★★ **列 2 は `j` の `le0` 祖先ではない**ので、`nextrel1` の最小性が効きません。**
**⟹ ⟹ ★ これが「締めても直らない」理由です。⟹ **窓は `le0` の部分木で、親の道より広い**。** -/

/-- 締めた `HeredNB`（使用箇所が実際に持っている前提つき）。 -/
def HeredNB' : Prop :=
  ∀ (P B : TrioSeq) (j p : ℕ), p < j → j < B.length →
    hasParent (P ++ B.take (j + 1))
      (srow (P ++ B.take (j + 1)) (P.length + j)) (P.length + j) →
    parent (P ++ B.take (j + 1))
      (srow (P ++ B.take (j + 1)) (P.length + j)) (P.length + j) = P.length + p →
    hlocQ (wnd P B j p)

section CE249
private def Bce : TrioSeq := [(0, 0, 0), (1, 5, 0), (2, 1, 0), (2, 9, 0)]

private theorem Bce_take : ([] : TrioSeq) ++ Bce.take (3 + 1) = Bce := by
  unfold Bce; rfl

private theorem Bce_nr0_13 : nextrel0 Bce 1 3 := by
  refine ⟨by decide, by decide, by omega, by decide, ?_⟩
  intro q hq
  rw [show q = 2 from by omega]; decide

private theorem Bce_no_le0_23 : ¬ le0 Bce 2 3 := by
  rintro ⟨-, -, hrt⟩
  rcases Relation.ReflTransGen.cases_tail hrt with h | ⟨c, hc, hcs⟩
  · omega
  · have h1 : 2 ≤ c := le0_le' ⟨by decide, by simpa using hcs.1, hc⟩
    have h2 : c < 3 := hcs.2.2.1
    rw [show c = 2 from by omega] at hcs
    exact absurd hcs.2.2.2.1 (by decide)

private theorem Bce_le0_q3 {q : ℕ} (h : le0 Bce q 3) (hq : 1 < q) : q = 3 := by
  have hle := le0_le' h
  rcases Nat.lt_or_ge q 3 with hlt | hge
  · rw [show q = 2 from by omega] at h; exact absurd h Bce_no_le0_23
  · omega

private theorem Bce_nr1_13 : nextrel1 Bce 1 3 := by
  refine ⟨by decide, by decide, by omega, by decide,
    ⟨by decide, by decide, Relation.ReflTransGen.single Bce_nr0_13⟩, ?_⟩
  intro q ⟨hq1, hq2⟩
  rw [Bce_le0_q3 hq2 hq1]

private theorem nextR_one_iff {M : TrioSeq} {a b : ℕ} : nextR M 1 a b ↔ nextrel1 M a b := by
  unfold nextR; simp

private theorem Bce_uniq {y : ℕ} (h : nextrel1 Bce y 3) : y = 1 := by
  have hy3 : y < 3 := h.2.2.1
  rcases Nat.lt_or_ge y 1 with h0 | h1
  · rw [show y = 0 from by omega] at h
    exact absurd (h.2.2.2.2.2 1 ⟨by omega,
      ⟨by decide, by decide, Relation.ReflTransGen.single Bce_nr0_13⟩⟩) (by decide)
  · rcases Nat.lt_or_ge y 2 with h1' | h2
    · omega
    · rw [show y = 2 from by omega] at h
      exact absurd h.2.2.2.2.1 Bce_no_le0_23

private theorem Bce_srow : srow Bce 3 = 1 := by decide

private theorem Bce_hasParent : hasParent Bce 1 3 := by
  refine ⟨1, nextR_one_iff.mpr Bce_nr1_13, fun y hy => Bce_uniq (nextR_one_iff.mp hy)⟩

/-- ⛔⛔⛔ **締めた `HeredNB'` も偽**。 -/
theorem heredNB'_false : ¬ HeredNB' := by
  intro h
  have hw : wnd ([] : TrioSeq) Bce 3 1 = [(1, 5, 0), (2, 1, 0)] := by
    unfold wnd Bce; rfl
  have hloc := h [] Bce 3 1 (by omega) (by decide) ?_ ?_
  · rw [hw] at hloc
    obtain ⟨-, hrow1⟩ := hloc 1 (by omega) (by decide)
    obtain ⟨y, hy1, -, hylt, -⟩ := hrow1 (by decide) (by decide)
    rw [show y = 0 from by omega] at hylt
    exact absurd hylt (by decide)
  · rw [Bce_take]
    show hasParent Bce (srow Bce (0 + 3)) (0 + 3)
    rw [show (0 : ℕ) + 3 = 3 from rfl, Bce_srow]
    exact Bce_hasParent
  · rw [Bce_take]
    show parent Bce (srow Bce (0 + 3)) (0 + 3) = 0 + 1
    rw [show (0 : ℕ) + 3 = 3 from rfl, Bce_srow, show (0 : ℕ) + 1 = 1 from rfl]
    exact Bce_uniq (nextR_one_iff.mp (parent_nextR Bce_hasParent))

end CE249

/-! ### 249.1 ⟹ ★★★ **何が悪いのかが分かりました**

    **窓 `[p, j)` は `p` の行 0 の部分木**（`j` への道だけではない）
    ⟹ ★ `nextrel1 B p j` の最小性は **`j` の `le0` 祖先**にしか効かない
    ⟹ ⟹ ⛔ **道から外れた列**（上の例の列 2）は**何の制約も受けない**
    ⟹ ⟹ ⟹ ★★★ そこが `hlocQ` を破ります

**⟹ ★ 逆に **`j` の `le0` 祖先の上では `hlocQ` は無料**です（次で緑にします）。** -/

theorem hlocQ_row1_of_le0_path {B : TrioSeq} {p q j : ℕ}
    (hnr : nextrel1 B p j) (hpq : p < q) (hq : le0 B q j) :
    entry B 1 p < entry B 1 q :=
  lt_of_lt_of_le hnr.2.2.2.1 (hnr.2.2.2.2.2 q ⟨hpq, hq⟩)

/-! ## 250. ⛔⛔⛔⛔ **`hlocQ B` を足しても駄目**です —— `hlocQ` は「遺伝しない」が確定

§249 の `Bce` について、⚠ **`hlocQ Bce` は成り立ちます**。⟹ ★ 下で緑にします。
**⟹ ⟹ ⛔⛔⛔ ですから **親が `hlocQ` を満たしていても、窓は満たしません**。**
**⟹ ⟹ ⟹ ★★★ これで **`hlocQ` は不変量として使えない**ことが**確定**しました。** -/

section CE250
open Classical in
private theorem Bce_nr0_01 : nextrel0 Bce 0 1 :=
  ⟨by decide, by decide, by omega, by decide, by intro q hq; omega⟩

private theorem Bce_nr0_12 : nextrel0 Bce 1 2 :=
  ⟨by decide, by decide, by omega, by decide, by intro q hq; omega⟩

private theorem Bce_nr1_01 : nextrel1 Bce 0 1 := by
  refine ⟨by decide, by decide, by omega, by decide,
    ⟨by decide, by decide, Relation.ReflTransGen.single Bce_nr0_01⟩, ?_⟩
  intro q ⟨hq1, hq2⟩
  rw [show q = 1 from by have := le0_le' hq2; omega]

private theorem Bce_le0_02 : le0 Bce 0 2 :=
  ⟨by decide, by decide, (Relation.ReflTransGen.single Bce_nr0_01).tail Bce_nr0_12⟩

private theorem Bce_nr1_02 : nextrel1 Bce 0 2 := by
  refine ⟨by decide, by decide, by omega, by decide, Bce_le0_02, ?_⟩
  intro q ⟨hq1, hq2⟩
  have := le0_le' hq2
  rcases Nat.lt_or_ge q 2 with h | h
  · rw [show q = 1 from by omega]; decide
  · rw [show q = 2 from by omega]

/-- ★ **`hlocQ Bce` は成り立ちます**（親の側は健全）。 -/
theorem Bce_hlocQ : hlocQ Bce := by
  intro j hj0 hj
  have hjlen : j < 4 := by simpa [Bce] using hj
  refine ⟨fun hpos => absurd hpos ?_, fun _ _ => ?_⟩
  · rcases Nat.lt_or_ge j 2 with h | h
    · rw [show j = 1 from by omega]; decide
    · rcases Nat.lt_or_ge j 3 with h' | h'
      · rw [show j = 2 from by omega]; decide
      · rw [show j = 3 from by omega]; decide
  · rcases Nat.lt_or_ge j 2 with h | h
    · rw [show j = 1 from by omega]; exact hlocQ_row1_of_nextrel1 Bce_nr1_01
    · rcases Nat.lt_or_ge j 3 with h' | h'
      · rw [show j = 2 from by omega]; exact hlocQ_row1_of_nextrel1 Bce_nr1_02
      · rw [show j = 3 from by omega]; exact hlocQ_row1_of_nextrel1 Bce_nr1_13

end CE250

/-! ### 250.1 ⛔⛔⛔⛔ **結論: `hlocQ` は不変量として使えません**

| 足した前提 | 結果 |
|---|---|
| 何も足さない（`HeredNB`） | ⛔ 偽（§248） |
| ＋ `hpar` / `hpe`（使用箇所が持つもの） | ⛔ 偽（§249） |
| ＋ **`hlocQ B`（親の側の健全性）** | ⛔ **偽**（§250、同じ `Bce`） |

**⟹ ★★★ **原因は 1 つ**です（§249.1）:**

    窓 `[p, j)` は **`p` の行 0 の部分木**であって「`j` への道」ではない
    ⟹ `nextrel1 B p j` の最小性は **`j` の `le0` 祖先**にしか効かない
    ⟹ ⛔ **道から外れた列は何の制約も受けない**

**⟹ ⟹ ★★ ですから **`hlocQ` に何を足しても、道の外の列は救えません**。**
### ⛔⛔⛔⛔⛔ 250.2 **シート（ground truth）で確認しました** —— **(い) も死にました**

`tools/dbms/psiI.json`（BM4-Analysis シートの DBMS 列、**重複を除いて 1637 個**）で、
各接頭辞 `B = M.take (j+1)` の最終列の親 `p` を計算し、窓 `[p, j)` の `hlocQ` を測りました。

    **分母 6792**（`srow ≥ 1` ∧ 親が一意 ∧ 窓の長さ ≥ 2 の窓）
    ⛔ **破れ 348（5.1237%）**
    ⛔ **そのうち `hlocQ B` も成り立つもの: 348（＝ 100%）**
    ⛔ **破れを出すシート行列: 197 / 1637**

**最短の例（シート由来）:**

    B = [(0,0,0), (1,0,0), (2,1,0), (3,2,0), (4,1,0), (3,2,0)]   （列 5 の親 = 2）
    窓 = [(2,1,0), (3,2,0), (4,1,0)]
    ⟹ ⛔ `t = 2` の列 `(4,1,0)` は行 1 = 1。窓の中の候補は行 1 = 1, 2 で**どちらも小さくない**
    ⟹ ★ `B` の中でなら証人は **`(1,0,0)`（添字 1）** ——**窓の根 2 より手前**

**⟹ ⛔⛔ ですから **`B ∈ W u` を足しても駄目**です。⟹ ⟹ **(い) は死にました**。**
**⟹ ★ そして **`hlocQ B` は 348 件すべてで成立**——親の側はいつも健全です。**

⚠ **教訓 27**: 分母 6792 と「100% で親側は健全」を併記しました。

**⟹ ⟹ ⟹ ★★★★ 直すなら **窓の取り方を変える**しかありません:**

    **(あ)** 窓を **`j` への `le0` の道**に沿って切る（`hlocQ_row1_of_le0_path` が無料になる）
    **(い)** **`B ∈ W u`** を足して、`W` の構造から「道の外の列」を排除する
    **(う)** `hlocQ` を捨て、**孤児の枝**（`snoc_orphan_W`）に戻す

**⚠ (あ) は展開規則が窓を `[p, j)` と決めているので、私には変えられません。**

### ⛔⛔⛔⛔⛔⛔ 250.3 **(う) も死にました** —— 窓の孤児は **100% 全体では孤児でない**

`tools/dbms/l3_sheet_hlocq.py` の第 2 の測定です。
**窓で `hlocQ` を破る列（＝ 窓の中の孤児）の親が `B` のどこにいるか:**

    **分母 353**（窓で破れた列）
    ⛔ **親が窓の根 `p` より手前: 353（100.0000%）**
    ★ **`B` の中でも孤児: 0 件**

**⟹ ⛔⛔ ですから **`snoc_orphan_W` は 1 件も使えません**。⟹ ⟹ **(う) は死にました**。**

**⟹ ★★★★ そして **親は必ず接頭辞（次の段の `A'`）の中**にいます。**
**⟹ ⟹ ★★★★★ ＝ これは **`OrphOK0` そのもの**です。**

### ⟹ ★★★★★★ 250.4 **結論: `hlocQ` の計画は `OrphOK0` に還元されました**

    (あ) 窓を道に沿って切る … ⛔ 展開規則が決めているので不可
    (い) `B ∈ W u` を足す …… ⛔ シートで 5.12% 破れる（§250.2）
    (う) 孤児の枝に戻す ……… ⛔ 窓の孤児は 100% 全体では孤児でない（§250.3）

**⟹ ★★ ですから **`hlocQ` は `OrphOK0` を消せません**。⟹ ⟹ **`OrphOK0` を証明するしかない**。**
**⟹ ★ 材料: §240.4（親があれば接頭辞は無関係）、§247（錐の伝播）、
H12 の `no_nextrel2_cross_of_anc`（行 2 の壁が「的の `le1` 祖先」に縮んだ）。**

⚠ **教訓 14**: ここまでの §239〜§250 は**すべて形の確定**です。**残差は 1 本も落ちていません。** -/

end L106
end TRIO
