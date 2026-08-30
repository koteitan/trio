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
import H12Export

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

/-- ★ **`d = 0 ⟹ e = 0`**（H12 の `entry0_parent_lt_of_srow2` から遺伝、§233）。
⟹ `ZeroDOK` が **`d = e = 0`（同一コピー）だけ**になります。 -/
theorem hde_of_TowerP'' {Q : TrioSeq} {d e : ℕ} (hP : TowerP'' Q d e) :
    d = 0 → e = 0 := hP.2.2.2.2

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
    (hz0h : HeredZ0)
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
    (hz0h : HeredZ0)
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
    (hz0h : HeredZ0)
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
      hplt hpar hpe hz1 hz0h ?_
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
/-- ⛔⛔ **使ってはいけません**: `OrphOK` / `OrphOK0` / `HeredZ0` は
**すべて偽**です（§261-263）。⟹ **前提が満たせないので空虚**です。 -/
theorem towerClosed_of_hered {u : ℕ} (horph : OrphOK) (horph0 : OrphOK0)
    (hzd : ZeroDOK u) (hz0h : HeredZ0) :
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
      (hz1_of_TowerP'' hP) hz0h hIH hpre
  · -- ★ `j ≥ 1` … ⛔ `hlocQ` は遺伝しない（§248-250）ので、**孤児の枝を戻します**
    set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
    have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
    by_cases hloc : hasParent (B.take (j + 1)) (srow (B.take (j + 1)) j) j
    · exact hsnoc_pos hP hIH hz0h hj hj1 hloc (parent_bound_pos hj hloc) hall
    · -- ⛔ 孤児 ⟹ `OrphOK` ＋ `snoc_orphan_W`
      have hnp := horph A Q d e n j hj1 hj hloc
      have hBt : B.take (j + 1) = B.take j ++ [B.getD j (0, 0, 0)] := by
        rw [List.take_add_one]
        congr 1
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        rfl
      have hsp : A ++ mTower Q d e n ++ B.take (j + 1)
          = (A ++ mTower Q d e n ++ B.take j) ++ [B.getD j (0, 0, 0)] := by
        rw [hBt, ← List.append_assoc]
      have hClen : (A ++ mTower Q d e n ++ B.take j).length
          = (A ++ mTower Q d e n).length + j := by
        rw [List.length_append, List.length_take, Nat.min_eq_left (by omega)]
      have hCne : A ++ mTower Q d e n ++ B.take j ≠ [] := by
        intro hc
        have : (A ++ mTower Q d e n ++ B.take j).length = 0 := by rw [hc]; rfl
        omega
      rw [hsp]
      refine snoc_orphan_W _ (hall j (le_refl j)) hCne ?_
      rw [hClen, ← hsp]
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
/-- ⛔⛔ **使ってはいけません**（§260 で `RootZ1` / `RootZ2` が偽、§261-263 で残りも偽）。 -/
theorem mTowerClosedS_of_residues (horph : OrphOK) (horph0 : OrphOK0)
    (hzd : ∀ u, ZeroDOK u) (hz0h : HeredZ0)
    (hrz1 : RootZ1) (hroot : RootZ2)
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
        hde u Q d e hQ⟩
    have h := towerClosed_of_hered (u := u) horph horph0 (hzd u) hz0h
      Q d e hP [] (W_nil u) (by simpa using hQ) n
    simpa using h

/-! ### 222.1 ⟹ ★★★★★★★★ **`MTowerClosedS` は 6 本**（`OrphOK` は**消えました**）

```lean
theorem mTowerClosedS_of_residues (horph0 : OrphOK0)
    (hzd : ∀ u, ZeroDOK u) (hz0h : HeredZ0)
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

### ✅ 248.2 **修理しました**（§251）: `HeredNB` と `RootNB` を外し、孤児の枝を戻しました

`mTowerClosedS_of_residues` は `hnbh : HeredNB` を前提に取っていました。
**⟹ ⛔ §248-250 で `HeredNB` が**偽**と分かったので、そのままでは**空虚**でした。**
**⟹ ⟹ ⚠ **緑であること・`sorry` が無いことは、何も保証しません**（教訓 14）。**

**⟹ ✅ §251 で修理済みです:**

    ⛔ `TowerP''` から **`hlocQ Q` の連言を削除**（遺伝しないので運べない）
    ⛔ ⟹ `RootNB`（`∀ Q ∈ W u, hlocQ Q`）も**不要**になり、**残差が 1 本減りました**
    ★ ⟹ 代わりに `towerClosed_of_hered` の `j ≥ 1` の枝に **`by_cases hloc` を戻し**、
         孤児の側は **`OrphOK` ＋ `snoc_orphan_W`** で処理します

**⟹ ⟹ ★ **`HeredNB` / `RootNB`（偽・不要）が消え、`OrphOK`（未証明）が戻りました**。** -/

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

/-! ## 251. ✅ **修理しました** —— `HeredNB` / `RootNB` を外し、孤児の枝を戻しました

§248-250 で `hlocQ` の遺伝が偽と確定したので、**設計を戻しました**。

    ⛔ `TowerP''` から **`hlocQ Q` の連言を削除**（遺伝しないので窓に運べない）
    ⛔ ⟹ `HeredNB`（**偽**）と `RootNB`（**不要になった**）が**両方消えました**
    ★ ⟹ `towerClosed_of_hered` の `j ≥ 1` の枝に **`by_cases hloc` を戻し**、
         孤児の側は **`OrphOK` ＋ `snoc_orphan_W`** で処理します

**⟹ ★★ 残差の一覧（現在）:**

| 残差 | 内容 | 状態 |
|---|---|---|
| **`OrphOK`** | ブロックの中で孤児 ⟹ 全体でも孤児（`j ≥ 1`） | ⛔ 未証明（R2 実測 100%、374043） |
| **`OrphOK0`** | 塔の中で孤児 ⟹ 接頭辞つきでも孤児（`j = 0`、`0 < d`） | ⛔ 未証明 |
| **`ZeroDOK`** | `d = e = 0` の塔（＝ `L53.PrefixCopies`） | ⛔ 未証明 |
| **`HeredZ0`** | 窓の根の行 2 が 0 | ⛔ 未証明（§224 で大半） |
| **`RootZ1`** | `Q ∈ W u` ⟹ 行 2 ≤ 1 | ⛔ 未証明 |
| **`RootZ2`** | `Q ∈ W u` ⟹ 根の行 2 = 0 | ⛔ 未証明 |
| `d = 0 → e = 0` | `Q ∈ W u` の性質 | ⛔ 未証明 |

**⟹ ⛔ **7 本**です。⟹ ⟹ ★ ただし **偽と分かっているものは 1 本もありません**
（`HeredNB` は外しました）。⟹ ⟹ ⟹ **前の 6 本のうち 1 本が偽だった**ので、実質は改善です。**

**⟹ ★★★ そして今日の §239-247 の道具は **`OrphOK` / `OrphOK0` にそのまま効きます**:**

    §240.4 `prefix_no_cross_of_inner` … **親が中にあれば接頭辞は無関係**（前提なし）
    §247   `wnd_all_out_of_cone` …… **窓の根が錐の外 ⟹ 窓は丸ごと錐の外** ⟹ `e*n` が消える
    §241   `hlocQ_iff_outOfCone` …… **錐の中は丸ごと無料**
    §243   `hlocQ_row1_of_nextrel1` … 行 1 の親が 1 本あれば十分
    §240   `hasParent_two_iff_of_z1` … 行 2 の親 ＝ 行 2 = 0 の `le1` 祖先（**同値**）

**⟹ ★ H12 の `nextR_src_ge_of_cone`（3 行そろいの壁）と `hanc_of_cone` が
**`OrphOK` の錐の中の部分**を閉じます。⟹ ⟹ **残るのは錐の外の列だけ**。** -/

/-! ## 252. ★ H12 の**壁**の補題を写します（`H12Export.lean:2713〜3008` 逐語）

**⟹ ★★★★★★ `nextR_src_ge_of_cone` が「的が錐の中なら 3 行とも壁が立つ」と言います。**
**⟹ ⟹ ★ これで `OrphOK` の**錐の中の部分**が閉じます。** -/

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



/-! ## 253. ★★★★★ **`OrphOK` の行 1 の `hle0` が無料になりました**

§228/§230 の `orphOK_row0/1/2` は既に**列 1 本の条件**で書けています:

    `orphOK_row0` … `entry T 0 0 < entry T 0 j1`                       ⟹ ★ **これだけ**
    `orphOK_row1` … ＋ **`le0 (A ++ T) A.length (A.length + j1)`**
    `orphOK_row2` … ＋ **`le1 (A ++ T) A.length (A.length + j1)`**

**⟹ ★★★★ §252 で写した H12 の `le0_root_of_shallow` が、**行 1 の `le0` を無料にします**。**
**⟹ ⟹ ★ 「窓の根は窓の全内部列の `le0` 祖先」——`hr0(T)` だけから出ます。** -/

theorem shallow_append_right {A T : TrioSeq}
    (hs : ∀ x, 0 < x → x < T.length → entry T 0 0 < entry T 0 x) :
    ∀ x, A.length < x → x < (A ++ T).length →
      entry (A ++ T) 0 A.length < entry (A ++ T) 0 x := by
  intro x hx1 hx2
  rw [List.length_append] at hx2
  obtain ⟨x', rfl⟩ : ∃ x', x = A.length + x' := ⟨x - A.length, by omega⟩
  rw [show A.length = A.length + 0 from by omega, entry_append_right,
    show A.length + 0 + x' = A.length + x' from by omega, entry_append_right]
  exact hs x' (by omega) (by omega)

/-- ★★★★★ **`orphOK_row1` の `hle0` は `hr0(T)` から無料**。 -/
theorem le0_root_append_right {A T : TrioSeq} {j1 : ℕ} (hj1 : 0 < j1)
    (hjT : j1 < T.length)
    (hs : ∀ x, 0 < x → x < T.length → entry T 0 0 < entry T 0 x) :
    le0 (A ++ T) A.length (A.length + j1) :=
  le0_root_of_shallow (M := A ++ T) (p := A.length)
    (by rw [List.length_append]; omega) (shallow_append_right (A := A) hs)
    (A.length + j1) (by omega) (by rw [List.length_append]; omega)

/-- ★★★★★ ⟹ **行 1 の `OrphOK` は「的が非ブロッカー」＋ `hr0(T)` だけ**。 -/
theorem orphOK_row1_free {A T : TrioSeq} {j1 : ℕ} (hj1 : 0 < j1) (hjT : j1 < T.length)
    (hs : ∀ x, 0 < x → x < T.length → entry T 0 0 < entry T 0 x)
    (hmin : entry T 1 0 < entry T 1 j1)
    (hnp : ¬ hasParent T 1 j1) : ¬ hasParent (A ++ T) 1 (A.length + j1) :=
  orphOK_row1 (le0_root_append_right hj1 hjT hs) hmin hnp

/-! ### 253.1 ⟹ ★★★ **`OrphOK` の残差は 2 つだけ**になりました

    ✅ **行 0** ………… `orphOK_row0`（`entry T 0 0 < entry T 0 j1` だけ、**無料**）
    ✅ **行 1（非ブロッカー）** … `orphOK_row1_free`（**`hr0(T)` ＋ 1 本の不等式**）
    ⛔ **行 1（的がブロッカー）** … `entry T 1 j1 ≤ entry T 1 0` のとき
    ⛔ **行 2** ………… `le1 (A ++ T) A.length (A.length + j1)` が要る

**⟹ ★★ ですから **`hnbQ` の ∀ が「的 1 列」に縮みました**（H12 の (W13) の方向）。**
**⟹ ⟹ ★ そして **行 2 の残差は「大きい列の中で的が塔の根の錐にいるか」**だけです。**

⚠ **教訓 14**: `OrphOK` はまだ証明されていません。**2 つの穴が残っています。** -/

/-! ## 254. ★★★★★★ **(W16) は無料でした** —— 私の §242 がそのまま効きます

H12 の `no_nextrel2_cross_of_anc` は **`nextrel1 (A ++ T)` の鎖**で `hanc` を要求し、
`hanc_of_cone` は **`nextrel1 T` の鎖**で与えます。⟹ ⚠ 私は「繋がっていない」と書きました。

**⟹ ★★★ ですが **繋がります**。⟹ ⟹ 鍵は 2 つ:**

    (1) `nextrel1` は添字を**増やす**ので、`A.length + m'` から始まる鎖は
        **すべて `A.length` 以上**にとどまる ⟹ ★ `A` に落ちない
    (2) そして `T = ((A ++ T).drop A.length).take T.length` は**まさに窓**
        ⟹ ★★ §242 `le1_window`（**前提なし**）がそのまま使える

**⟹ ⟹ ★★★★★ ですから **(W16) は無料**です。H12 に渡せます。** -/

/-! ★ H12 の越境の補題（`H12Export.lean:2870〜2920` 逐語）。 -/

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



/-! ★ H12 の鎖の補題（`H12Export.lean:2923〜3007` 逐語）を先に写します。 -/

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



theorem drop_take_append_right (A T : TrioSeq) :
    ((A ++ T).drop A.length).take T.length = T := by
  rw [List.drop_left, List.take_of_length_le (le_refl _)]

/-- ★★★★★★ **(W16)**: `A ++ T` の `le1` の鎖は `T` の `le1` の鎖に落ちる（**前提なし**）。 -/
theorem le1_peel_append_right {A T : TrioSeq} {a b : ℕ}
    (ha : a < T.length) (hb : b < T.length)
    (h : le1 (A ++ T) (A.length + a) (A.length + b)) : le1 T a b := by
  have hL : A.length + T.length ≤ (A ++ T).length := by
    rw [List.length_append]
  have := le1_window (T := A ++ T) (s := A.length) (L := T.length) hL ha hb h
  rwa [drop_take_append_right] at this

/-- ★★★★★ ⟹ **`rtg1` 版**（`hanc` の形に合わせたもの）。 -/
theorem rtg1_peel_append_right {A T : TrioSeq} {a b : ℕ}
    (ha : a < T.length) (hb : b < T.length)
    (h : Relation.ReflTransGen (nextrel1 (A ++ T)) (A.length + a) (A.length + b)) :
    Relation.ReflTransGen (nextrel1 T) a b :=
  (le1_peel_append_right ha hb
    ⟨by rw [List.length_append]; omega, by rw [List.length_append]; omega, h⟩).2.2

/-! ### 254.1 ⟹ ★★★★ **`hanc` が `T` の中の話に落ちました**

    H12 `no_nextrel2_cross_of_anc` の `hanc`（`A ++ T` の鎖）
      ⟸ §254 `rtg1_peel_append_right`
      ⟸ H12 `hanc_of_cone`（`T` の鎖）

**⟹ ★★ ですから **行 2 の壁は「的が `T` の錐の中」だけ**で立ちます。**
**⟹ ⟹ ★ そして §241/§243 が「錐の中なら祖先は全部非ブロッカー」を言います。**

**⟹ ⟹ ⟹ ★★★★★ ですから **(O2) は消え、残差は (O1) だけ**になります:**

    ⛔ **(O1) 行 1 で的がブロッカー**（`entry T 1 j1 ≤ entry T 1 0`）のとき、
        接頭辞が親を供給しうる

⚠ **教訓 14**: `hanc` の橋は緑ですが、**`OrphOK` はまだ証明されていません**。
行 2 について「的が `T` の錐の中」を**誰が供給するか**は未解決です。 -/

theorem hanc_bridge {A T : TrioSeq} {m : ℕ} (hm : m < T.length)
    (hcone : Relation.ReflTransGen (nextrel1 T) 0 m) :
    ∀ m', 0 < m' → m' < T.length →
      Relation.ReflTransGen (nextrel1 (A ++ T)) (A.length + m') (A.length + m) →
      entry T 1 0 < entry T 1 m' := by
  intro m' hm'0 hm'T hrt
  exact hanc_of_cone hcone m' hm'0 (rtg1_peel_append_right hm'T hm hrt)

/-! ## 255. ★★★★★★★ **`OrphOK` は「的が錐の中」なら 3 行とも成立**します

§253（行 0・行 1）と §254（行 2 の橋）を合わせます。

    **行 0** … `orphOK_row0` ………… `hr0(T)`
    **行 1** … `orphOK_row1_free` … `hr0(T)` ＋ **`entry T 1 0 < entry T 1 j1`**
    **行 2** … H12 `no_nextrel2_cross_of_anc` ＋ §254 `hanc_bridge` ＋ `hz0(T)`

**⟹ ★★★ そして **錐の中なら `entry T 1 0 < entry T 1 j1` は自動**です
（`hanc_of_cone` を的そのものに当てるだけ）。**
**⟹ ⟹ ★★★★★ ですから **前提は `hr0(T)` ＋ `hz0(T)` ＋「的が `T` の錐の中」だけ**です。** -/

open Classical in
theorem orphOK_of_cone {A T : TrioSeq} {j1 : ℕ} (hj1 : 0 < j1) (hjT : j1 < T.length)
    (hs : ∀ x, 0 < x → x < T.length → entry T 0 0 < entry T 0 x)
    (hz0 : entry T 2 0 = 0)
    (hcone : Relation.ReflTransGen (nextrel1 T) 0 j1)
    (hnp : ¬ hasParent T (srow T j1) j1) :
    ¬ hasParent (A ++ T) (srow T j1) (A.length + j1) := by
  have hnb1 : entry T 1 0 < entry T 1 j1 :=
    hanc_of_cone hcone j1 hj1 Relation.ReflTransGen.refl
  by_cases h2 : 0 < entry T 2 j1
  · -- ★ `srow = 2`
    have hsr : srow T j1 = 2 := by unfold srow; rw [if_pos h2]
    rw [hsr] at hnp ⊢
    intro hp
    refine hnp (hasParent_peel_of_noCross (fun y hy hc => ?_) hp)
    unfold nextR at hc
    rw [if_neg (by omega), if_neg (by omega)] at hc
    exact no_nextrel2_cross_of_anc (A := A) (T := T) (m := j1) hs
      (fun m' hm'0 hm'T hrt => hanc_bridge hjT hcone m' hm'0 hm'T hrt)
      (by omega) hy hjT hj1 hc
  · -- ★ `srow ≤ 1`。錐の中なので行 1 は正 ⟹ `srow = 1`
    have hsr : srow T j1 = 1 := by
      unfold srow; rw [if_neg h2, if_pos (by omega)]
    rw [hsr] at hnp ⊢
    exact orphOK_row1_free hj1 hjT hs hnb1 hnp

/-! ### 255.1 ⟹ ★★★★★ **`OrphOK` の残差は「的が錐の外」1 本**

    ✅ **的が `T` の錐の中** … §255（**3 行とも緑**）
    ⛔ **的が `T` の錐の外**（＝ ブロッカー） … **残差**

**⟹ ★ そして §247 が「**窓の根が錐の外 ⟹ 窓は丸ごと錐の外**」と言うので、
錐の外の場合は **持ち上げが一切なく、`e*n` が消えます**。⟹ ⟹ **`Q` だけの話**です。**

⚠ **教訓 14**: §255 は緑ですが、**`hcone` を誰が供給するかは未解決**です。
**⟹ ⛔ `OrphOK` はまだ証明されていません。** -/

/-! ## 256. ★★★★★★ **接頭辞の唯一の入口は「行 0 の越境」**です

§255 で「的が錐の中」は閉じました。⟹ ★ 残るのは**錐の外**。⟹ そこを別の角度から見ます。

**⟹ ★★★ `nextrel0` / `nextrel1` / `nextrel2` は**どれも `le0` を含みます**:**

    `nextrel0 M c b` ⟹ 1 歩なので `le0 M c b`
    `nextrel1 M c b` ⟹ 定義に `le0 M c b` が入っている
    `nextrel2 M c b` ⟹ 定義に `le1 M c b`、そして `Gamma.le0_of_le1` で `le0 M c b`

**⟹ ⟹ ★★★★★ ですから **接頭辞の列が親になるには、行 0 で越境するしかありません**。**
**⟹ ⟹ ⟹ ★ 行の区別なしに、**1 本で**言えます。** -/

/-- `le1` は `le0` を含む（`Gamma.lean:1119` と同じ証明。`Gamma` は `import` していない）。 -/
theorem le0_of_le1' {X : TrioSeq} {a b : ℕ} (h : le1 X a b) : le0 X a b := by
  obtain ⟨ha, hb, hch⟩ := h
  refine ⟨ha, hb, ?_⟩
  induction hch with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y w hay hyw ih => exact (ih hyw.1).trans hyw.2.2.2.2.1.2.2

theorem no_nextR_of_no_le0_cross {A T : TrioSeq} {i j1 c : ℕ}
    (hnc : ¬ le0 (A ++ T) c (A.length + j1)) :
    ¬ nextR (A ++ T) i c (A.length + j1) := by
  intro h
  unfold nextR at h
  by_cases h0 : i = 0
  · rw [if_pos h0] at h
    exact hnc ⟨h.1, h.2.1, Relation.ReflTransGen.single h⟩
  · rw [if_neg h0] at h
    by_cases h1 : i = 1
    · rw [if_pos h1] at h; exact hnc h.2.2.2.2.1
    · rw [if_neg h1] at h; exact hnc (le0_of_le1' h.2.2.2.2.1)

/-- ★★★★★★ ⟹ **行 0 で越境できなければ `OrphOK` は 3 行とも無料**。 -/
theorem orphOK_of_no_le0_cross {A T : TrioSeq} {i j1 : ℕ}
    (hnc : ∀ c, c < A.length → ¬ le0 (A ++ T) c (A.length + j1))
    (hnp : ¬ hasParent T i j1) : ¬ hasParent (A ++ T) i (A.length + j1) := by
  intro hp
  exact hnp (hasParent_peel_of_noCross
    (fun y hy => no_nextR_of_no_le0_cross (hnc y hy)) hp)

/-! ### 256.1 ⟹ ★★★★ **`OrphOK` の残差の最終形**

**⟹ ★ 2 つの十分条件が緑になりました（どちらか一方で足ります）:**

    **(S1)** 的が **`T` の錐の中** ……………… §255 `orphOK_of_cone`
    **(S2)** 接頭辞から **行 0 で越境できない** … §256 `orphOK_of_no_le0_cross`

**⟹ ★★ そして (S2) は **`entry T 0 0 ≤ entry A 0 c`（＝ `rsum` の形）**から出ます:**
**⟹ ⟹ ⛔ ですが `rsum` は遺伝しません（§227 で**証明**）。⟹ ⟹ そのままでは使えません。**

**⟹ ★★★ ですから残差は **「的が錐の外 ∧ 接頭辞が行 0 で越境できる」**という
**2 つの条件が同時に成り立つ場合**だけです。**

**⟹ ⚠ R2 への注文はこの**積**です:**

    **(BLK2) 「的がブロッカー」かつ「接頭辞の列が的の `le0` 祖先」——
             この 2 つが同時に起きる割合。⟹ 分母は**ブロッカーの列の数**。**

⚠ **教訓 27**: (W15) の分母は**全列**でした。⟹ **ブロッカーだけに絞ると分母が変わります**。

### ★★★★★ 256.2 **シートで検算しました** —— **(S1) と (S2) は破れと完全に相補的**

`tools/dbms/l3_sheet_orphok.py`（新規）。シートの `M` を `A = M[:L]`, `T = M[L:]` に切り、
**`hr0(T)` と `hz0(T)` が成り立つ切り方だけ**を分母にしました（組み立てで成り立つ条件）。

    **分母 22563**（`(A, T, j1)` の三つ組）
    ⛔ **`OrphOK` の破れ 1496**（`T` の中で孤児 ∧ `M` では親を持つ）
    ★ **(S1) 的が `T` の錐の中: 0 件** ⟹ **§255 と完全に整合**
    ★ **ブロッカー: 1496（100%）** ⟹ **§255 の裏返し**
    ★ **(S2) 接頭辞が行 0 で越境: 1496（100%）** ⟹ **§256 と完全に整合**

**最小の例:**

    M = [(0,0,0), (1,0,0), (2,1,0), (3,1,0)]、L = 2、T = [(2,1,0), (3,1,0)]、j1 = 1
    ⟹ `T` の根の行 1 = 1、的の行 1 = 1 ⟹ **ブロッカー**
    ⟹ `M` では親は **添字 1 の `(1,0,0)`**（行 1 = 0 < 1、`le0 M 1 3` ✅）⟹ **接頭辞の中**
    ⟹ ⚠ そして `entry M 0 1 = 1 < entry T 0 0 = 2` ⟹ **接頭辞が `T` の根より浅い**（`rsum` の破れ）

**⟹ ⛔⛔ ですから **`OrphOK` は無条件では偽**です。⟹ **`rsum` 型の情報が要ります**。**
**⟹ ⟹ ⛔ そして `rsum` は遺伝しません（§227 で**証明**）。⟹ ⟹ **ここが本当の壁**です。**

**⟹ ★ ただし ★★★ **私の 2 つの十分条件は破れと完全に相補的**（0% / 100%）でした。**
**⟹ ⟹ ★★ ですから **設計は正しく、残っているのは 1 点だけ**です:**

    ⛔ **「的がブロッカー」かつ「接頭辞の列が的の `le0` 祖先」** -/

/-! ## 257. ★★★★★★ **接頭辞の `le0` の鎖は必ずブロックの根を通る**

§256 で「接頭辞の唯一の入口は行 0 の越境」と分かりました。
**⟹ ★★★ そして H12 の `no_row0_parent_from_before_block`（`hr0(Q)` だけ）が
「**ブロックの内部列には接頭辞から `nextrel0` が入れない**」と言います。**
**⟹ ⟹ ★★★★★ ですから **入口はブロックの根 1 つだけ**です。** -/

theorem le0_cross_through_blockRoot {A Q : TrioSeq} {d e n j c : ℕ}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hj : j < Q.length) (hj0 : 0 < j)
    (hc : c < (A ++ mTower Q d e n).length)
    (h : le0 (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      c ((A ++ mTower Q d e n).length + j)) :
    Relation.ReflTransGen (nextrel0 (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)))
      (A ++ mTower Q d e n).length ((A ++ mTower Q d e n).length + j) := by
  set P := A ++ mTower Q d e n with hP
  set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
  set M := P ++ B.take (j + 1) with hM
  have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
  have hMlen : M.length = P.length + (j + 1) := by
    rw [hM, List.length_append, List.length_take, hBlen, Nat.min_eq_left (by omega)]
  obtain ⟨-, -, hrt⟩ := h
  -- 鎖をたどり、**接頭辞から出た最初の一歩**を捕まえます
  have key : ∀ z, Relation.ReflTransGen (nextrel0 M) c z →
      z < P.length ∨ Relation.ReflTransGen (nextrel0 M) P.length z := by
    intro z hz
    induction hz with
    | refl => exact Or.inl hc
    | @tail x y hx hxy ih =>
        rcases ih with hxlt | hxr
        · rcases Nat.lt_or_ge y P.length with hy | hy
          · exact Or.inl hy
          · -- ★ `x` は接頭辞、`y` はブロック ⟹ H12 の定理で `y = P.length`
            have hylt : y < M.length := hxy.2.1
            have hyM : y - P.length < j + 1 := by omega
            have hy0 : y = P.length := by
              by_contra hne
              have hj' : 0 < y - P.length := by omega
              have hMt : M.take (P.length + (y - P.length) + 1)
                  = P ++ B.take ((y - P.length) + 1) := by
                rw [hM, List.take_append, List.take_of_length_le (by omega),
                  show P.length + (y - P.length) + 1 - P.length
                    = (y - P.length) + 1 from by omega, List.take_take,
                  Nat.min_eq_left (by omega)]
              have hstep : nextrel0 (P ++ B.take ((y - P.length) + 1)) x
                  (P.length + (y - P.length)) := by
                rw [← hMt]
                refine (Wset.nextrel0_take (X := M)
                  (l := P.length + (y - P.length) + 1) (by omega) (by omega)).mpr ?_
                rw [show P.length + (y - P.length) = y from by omega]; exact hxy
              exact no_row0_parent_from_before_block (A := A) (Q := Q) (d := d) (e := e)
                (n := n) (j := y - P.length) (c := x) hr0 (by omega) hj' hxlt hstep
            rw [hy0]
            exact Or.inr Relation.ReflTransGen.refl
        · exact Or.inr (hxr.tail hxy)
  rcases key (P.length + j) hrt with hlt | hres
  · omega
  · exact hres

/-! ### 257.1 ⟹ ★★★★★ **`OrphOK` の残差の完成形**

    ✅ 的が `T` の錐の中 ……………………… §255（**3 行とも緑**）
    ✅ 接頭辞が行 0 で越境できない ………… §256（**3 行とも緑**）
    ✅ 越境は**ブロックの根 1 点だけ** …… §257（`hr0(Q)` だけ、**緑**）
    ⛔ **残差**: 接頭辞の列 `c` が
        「行 1 が的より小さい」∧「鎖がブロックの根を通って的に届く」

**⟹ ★★★ そして **`nextrel1` の最小性が `q = P.length`（ブロックの根）に当たる**ので、
そこから **`entry (block) 1 j ≤ entry (block) 1 0`**——つまり **的はブロックの根に対して
ブロッカー**でなければなりません。⟹ ⟹ ★ ＝ **`hnbQ` を的 1 列に絞ったもの**です。**

**⟹ ⟹ ★★★★★ ですから `OrphOK` の残差はこう書けます:**

    ⛔ **「的がブロックの根に対してブロッカー」かつ「接頭辞に行 1 がもっと小さい `le0` 祖先がある」**

⚠ **教訓 14**: §257 は緑ですが、**`OrphOK` はまだ証明されていません**。 -/

/-! ## 258. ★★★★★★★ **(L-O2)**: 行 2 の孤児は「行 1 の親さえあれば」起きません

team-lead / R2 の観測「**塔でも窓でも行 2 の孤児は 0 件**」（165 万件 ／ シート 7930 件）を
定理にします。⟹ ★ §240 の同値と**強い帰納法**だけです。

    `entry T 2 j = 1` の列 `j` に `nextrel1` の親 `y` があるとする
    ⟹ ★ `entry T 2 y = 0` なら **`y` がそのまま行 2 の証人**（`le1` は 1 歩）
    ⟹ ★★ `entry T 2 y = 1` なら **帰納法で `y` の証人 `y'` を取り、`le1` を継ぐ**
    ⟹ ⟹ ★★★ 底は `y = 0`（`hz0` より行 2 = 0）⟹ **必ず止まります**

**⟹ ★★★★★ ですから **(O2) の前提（行 2 の孤児）は、行 1 の親があれば満たされません**。**

⚠ **私の最初の読み（「`nextrel1` の親の行 2 は 0」）は偽**です:
`D_v` の列 2（`(2,2,1)`）の行 1 の親は列 1（`(1,1,1)`、行 2 = 1）。
**⟹ ★ ですから **1 歩では足りず、鎖を登る**必要があります。⟹ シートの 100% は箱の産物でした。 -/

theorem hasParent2_of_row1_parents {T : TrioSeq}
    (hz0 : entry T 2 0 = 0)
    (hz1 : ∀ q, q < T.length → entry T 2 q ≤ 1)
    (hpar : ∀ t, 0 < t → t < T.length → 0 < entry T 2 t → ∃ y, nextrel1 T y t) :
    ∀ j, 0 < j → j < T.length → 0 < entry T 2 j → hasParent T 2 j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj0 hj hpos
    obtain ⟨y, hy⟩ := hpar j hj0 hj hpos
    have hyj : y < j := hy.2.2.1
    have hyl : y < T.length := hy.1
    have hle1 : le1 T y j := ⟨hyl, hj, Relation.ReflTransGen.single hy⟩
    rcases Nat.eq_zero_or_pos (entry T 2 y) with hz | hzp
    · exact (hasParent_two_iff_of_z1 hj hz1 hpos).mpr ⟨y, hyj, hle1, hz⟩
    · -- ★ `y` も行 2 が正 ⟹ `y > 0`（根は `hz0` で 0）⟹ 帰納法
      have hy0 : 0 < y := by
        rcases Nat.eq_zero_or_pos y with h0 | h0
        · rw [h0] at hzp; omega
        · exact h0
      obtain ⟨y', hy'⟩ :=
        (hasParent_two_iff_of_z1 hyl hz1 hzp).mp (ih y hyj hy0 hyl hzp)
      exact (hasParent_two_iff_of_z1 hj hz1 hpos).mpr
        ⟨y', by omega, ⟨hy'.2.1.1, hj, hy'.2.1.2.2.trans hle1.2.2⟩, hy'.2.2⟩

/-! ### 258.1 ⟹ ★★★★★ **(O2) は「行 1 の親」に還元されました**

    ⛔ **(O2) 旧**: 行 2 で的が錐の外のとき、接頭辞が親を供給しうる
    ✅ **(O2) 新**: **行 2 の列に `nextrel1` の親があれば、行 2 の親も必ずある**
       ⟹ ★ ですから **`OrphOK` の行 2 の枝は前提が満たされず、空**になります

**⟹ ★★ 残るのは **「行 2 の列に行 1 の親があるか」**——⟹ ★ **行 1 の話に一本化**されました。**
**⟹ ⟹ ★★★ ＝ **(O1) と同じ問い**です。⟹ ⟹ **`OrphOK` の残差が本当に 1 本**になりました。**

⚠ **教訓 27**: シートでの分母は 7930、行 2 の孤児は 0、`nextrel1` の親は 7930（100%）。
**⟹ ⚠ ですが **100% は証明ではありません**。⟹ **`hpar` は前提として残っています**。 -/

/-! ## 259. ★★★★★ **(L-O1)**: 接頭辞が行 1 の親になれるのは **的がブロッカーのときだけ**

§253 は「的が非ブロッカーなら安全」でした。⟹ ★ その**逆**を証明します。

**⟹ ★★★ 鍵は §253 の `le0_root_append_right`（`hr0(T)` だけ）です:**

    `T` の根は **`T` の全内部列の `le0` 祖先** ⟹ ★ **`nextrel1` の最小性の候補に必ず入る**
    ⟹ ⟹ ★★ 接頭辞の `c < A.length` から `nextrel1` が張れるなら、最小性を `q := A.length`
      に当てて **`entry T 1 j ≤ entry T 1 0`** が出る ＝ **的はブロッカー** -/

theorem prefix_row1_cross_blocker {A T : TrioSeq} {j c : ℕ} (hj0 : 0 < j) (hjT : j < T.length)
    (hs : ∀ x, 0 < x → x < T.length → entry T 0 0 < entry T 0 x)
    (hc : c < A.length)
    (h : nextrel1 (A ++ T) c (A.length + j)) : entry T 1 j ≤ entry T 1 0 := by
  have hroot : le0 (A ++ T) A.length (A.length + j) :=
    le0_root_append_right hj0 hjT hs
  have := h.2.2.2.2.2 A.length ⟨by omega, hroot⟩
  rwa [show A.length = A.length + 0 from by omega, entry_append_right,
    show A.length + 0 + j = A.length + j from by omega, entry_append_right] at this

/-! ### 259.1 ⟹ ★★★★★ **行 1 の二分法が完成しました**（どちらも `hr0(T)` だけ）

    ✅ **的が非ブロッカー** … §253 `orphOK_row1_free` ⟹ **接頭辞は親になれない**
    ✅ **接頭辞が親になった** … §259 `prefix_row1_cross_blocker` ⟹ **的はブロッカー**

**⟹ ★★★ ですから **`OrphOK` の行 1 の破れ ⟺ 的がブロッカー**（`hr0(T)` の下で、両向き）。**
**⟹ ⟹ ★ シートの実測（分母 353、破れは 100% ブロッカー）と**完全に一致**します。** -/

/-- ★★★★★ **`OrphOK` の行 1**: 的がブロッカーでなければ成立（§253 の言い換え、対偶つき）。 -/
theorem orphOK_row1_dichotomy {A T : TrioSeq} {j : ℕ} (hj0 : 0 < j) (hjT : j < T.length)
    (hs : ∀ x, 0 < x → x < T.length → entry T 0 0 < entry T 0 x) :
    (∃ c, c < A.length ∧ nextR (A ++ T) 1 c (A.length + j)) → entry T 1 j ≤ entry T 1 0 := by
  rintro ⟨c, hc, hnr⟩
  unfold nextR at hnr
  rw [if_neg (by omega), if_pos rfl] at hnr
  exact prefix_row1_cross_blocker hj0 hjT hs hc hnr

/-! ### 259.2 ⟹ ★★★★★★ **`OrphOK` の残差の最終形（今日の到達点）**

| 的 | 行 0 | 行 1 | 行 2 |
|---|---|---|---|
| **非ブロッカー** | ✅ §228 | ✅ §253 | ✅ §258（**行 1 の親から自動**） |
| **ブロッカー** | ✅ §228（**無条件**） | ⛔ **残差** | ✅ §258（**行 1 の親があれば**） |

**⟹ ★★★★★ ですから **`OrphOK` の残差は 1 マス**です:**

    ⛔ **「的がブロッカー」かつ「`T` の中で行 1 の親が無い」かつ「接頭辞に親がある」**

**⟹ ★ そして §257 が「**越境はブロックの根 1 点だけ**」と言うので、
接頭辞の親 `c` は **ブロックの根を通って**しか届きません。**
**⟹ ⟹ ★★ ですから **`c` は「行 1 がブロックの根より小さく、根の `le0` 祖先」**でなければなりません。**

⚠ **教訓 14**: 二分法は緑ですが、**残差のマスは埋まっていません**。

### ★★★★★ 259.3 **測定: `OrphOK` の前件は、シートの標準形では一度も満たされません**

`tools/dbms/l3_sheet_orphok.py` の器具で、**シートの `Q` そのもの**（長さ ≤ 8、行 2 ≤ 1）を見ました。

    分母 **694**（そのうち **`hr0` を満たすもの 659**）
    ★ **`hr0` ∧ 接頭辞のどこかに孤児がある: 0 / 659（0.0000%）**
    ⚠ **陽性対照 (1)**: 孤児をもつ行列は **35 個**ある（**全部 `hr0` を満たさない**）
    ⚠ **陽性対照 (2)**: **`hr0` だけでは孤児は防げません**——
      同じ器具で、`hr0` ∧ `hz0` を満たす**窓**（`W` の元）では **1496 / 13712（10.9102%）が孤児**

**⟹ ★★★ ですから **`hr0` ではなく「シートの標準形であること」が効いています**。**
**⟹ ⟹ ⛔ そして **窓は `W` の元**（H12 `window_mem_W`）なのに孤児が出ます。**
**⟹ ⟹ ⟹ ★★★★★ ですから **残差は「`W` の元だが標準形でないもの」に住んでいます**。**

**⟹ ★ ＝ これが `RootNB` が偽で、しかもシートでは真に見える理由です。**
**⟹ ⚠ **`W` は標準形の集合より真に大きい**——⟹ ★ そこを詰めるのが次の設計課題です。** -/

/-! ## 260. ⛔⛔⛔ **`RootZ1` と `RootZ2` も偽です** —— 最終定理がまた空虚でした

`Wset.Om_mem_W (v z) : [(0, v, z)] ∈ W (2*v + z)` は **任意の `z`** を許します。
**⟹ ⛔ ですから `[(0,0,2)] ∈ W 2` で、⟹ ⟹ **行 2 が 2** です。**
**⟹ ⟹ ⟹ ⛔⛔ **`RootZ1`（行 2 ≤ 1）も `RootZ2`（根の行 2 = 0）も偽**になります。**

⚠ H12 の `W_not_zle1_closed`（`H12H2.lean:2220`）が**同じ観察**でした。
**⟹ ★ 私はそれを「`W` は `zle1` で閉じない」としてだけ読み、
⟹ ⛔ **自分の残差 `RootZ1` / `RootZ2` に当てていませんでした**。⟹ **教訓 14 の再発**です。 -/

theorem rootZ1_false : ¬ RootZ1 := by
  intro h
  have hmem : [((0, 0, 2) : ℕ × ℕ × ℕ)] ∈ W 2 := by
    have := Wset.Om_mem_W 0 2; simpa using this
  have := h 2 [((0, 0, 2) : ℕ × ℕ × ℕ)] hmem 0 (by decide)
  exact absurd this (by decide)

theorem rootZ2_false : ¬ RootZ2 := by
  intro h
  have hmem : [((0, 0, 2) : ℕ × ℕ × ℕ)] ∈ W 2 := by
    have := Wset.Om_mem_W 0 2; simpa using this
  have := h 2 [((0, 0, 2) : ℕ × ℕ × ℕ)] hmem (by intro j hj1 hj; simp at hj; omega)
  exact absurd this (by decide)

/-! ### 260.1 ⟹ ★★★★ **直し方: `z < 2` を目標のほうに書く**

⚠ `MTowerClosedS`（`L105Cap.lean:5618`）の前提は **`Q ∈ W u` と `hr0` の 2 つだけ**です。
**⟹ ⛔ ですから `Q = [(0,0,2)]` が通ってしまいます。**

**⟹ ★★★ ですが **このプロジェクトは `z < 2` の断片が対象**です（`CLAUDE.md`）。**
**⟹ ⟹ ★★ ですから **`zle1 Q` と `entry Q 2 0 = 0` を目標の前提に書く**のが正しい形です。**
**⟹ ⟹ ⟹ ★ そうすると **`RootZ1` と `RootZ2` は残差から消えます**（前提そのものになるので）。** -/

/-- ★★★ **`z < 2` に制限した目標**（このプロジェクトの本来の対象）。 -/
def MTowerClosedSZ : Prop :=
  ∀ (u d e n : ℕ) (Q : TrioSeq), Q ∈ W u →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
    (∀ q, q < Q.length → entry Q 2 q ≤ 1) → entry Q 2 0 = 0 →
    mTower Q d e n ∈ W u

open Classical in
/-- ⛔⛔ **使ってはいけません**: `OrphOK`（§261）・`OrphOK0`（§262）・`HeredZ0`（§263）が
**すべて偽と証明済み**なので、この定理は**空虚**です。⟹ ★ 記録として残します。 -/
theorem mTowerClosedSZ_of_residues (horph : OrphOK) (horph0 : OrphOK0)
    (hzd : ∀ u, ZeroDOK u) (hz0h : HeredZ0)
    (hde : ∀ (u : ℕ) (Q : TrioSeq) (d e : ℕ), Q ∈ W u → d = 0 → e = 0) :
    MTowerClosedSZ := by
  intro u d e n Q hQ hs hz1 hz0
  rcases Nat.eq_zero_or_pos Q.length with h0 | hpos
  · have hnil : Q = [] := List.eq_nil_of_length_eq_zero h0
    subst hnil
    rw [mTower_nil]
    exact W_nil u
  · have hP : TowerP'' Q d e :=
      ⟨hpos, fun l hl0 hl1 => hs l hl0 hl1, hz1, hz0, hde u Q d e hQ⟩
    have h := towerClosed_of_hered (u := u) horph horph0 (hzd u) hz0h
      Q d e hP [] (W_nil u) (by simpa using hQ) n
    simpa using h

/-! ### 260.2 ⟹ ★ **残差は 5 本**になりました（`z < 2` の目標に対して）

    `OrphOK` ／ `OrphOK0` ／ `ZeroDOK` ／ `HeredZ0` ／ `d = 0 → e = 0`

**⟹ ⚠ 値段: **消費側（`Final.lean`）が `zle1 Q` と `entry Q 2 0 = 0` を供給する**必要があります。**
**⟹ ★ ⟹ ですが **プロジェクトの対象が `z < 2` の断片**なので、⟹ ★★ **自然な前提**です。**
**⟹ ⟹ ⚠ ただし **`Final.lean` 側の接続は未確認**です。⟹ team-lead の判断待ち。**

⚠ **教訓 14**: `mTowerClosedS_of_residues`（制限なし版）は **前提が偽なので依然空虚**です。
**⟹ ★ 残しますが、**使ってはいけません**。⟹ **使うのは `mTowerClosedSZ_of_residues` です**。 -/

/-! ## 261. ⛔⛔⛔⛔ **`OrphOK` も偽です** —— 組み立ての形での反例（緑）

§259 で「接頭辞が行 1 の親になれるのは的がブロッカーのときだけ」と示しました。
**⟹ ⚠ ですが **ブロッカーのマスは空ではありません**。⟹ ★ 反例を貼ります。**

    `Q = [(0,1,0), (1,1,0), (1,0,0)]`、`d = 2`、`e = 0`、`n = 1`、`A = []`、`j = 1`
    ⟹ `hr0(Q)` ✅ ／ `entry Q 2 0 = 0` ✅ ／ `zle1 Q` ✅ ／ `0 < d` ✅
    ⟹ `mTower Q 2 0 1 = Q`（`Lift1 X 0 = X`、`shiftr01 0 0 X = X`）
    ⟹ ブロック `B = shiftr01 2 0 Q = [(2,1,0), (3,1,0), (3,0,0)]`
    ⟹ `T = B.take 2 = [(2,1,0), (3,1,0)]` ⟹ ★ 列 1 は **`T` の中で孤児**（`1 < 1` は偽）
    ⟹ ⛔ ところが `M = Q ++ T = [(0,1,0),(1,1,0),(1,0,0),(2,1,0),(3,1,0)]` では
       **添字 2 の `(1,0,0)` が親**（行 1 = 0 < 1、`le0` は 2→3→4）

**⟹ ⛔⛔ ですから **`OrphOK` は `TowerP''` の全条件を満たしても偽**です。** -/

section CE261
private def Qce : TrioSeq := [(0, 1, 0), (1, 1, 0), (1, 0, 0)]
private def Mce : TrioSeq := [(0, 1, 0), (1, 1, 0), (1, 0, 0), (2, 1, 0), (3, 1, 0)]

private theorem Mce_nr0_23 : nextrel0 Mce 2 3 := by
  refine ⟨by decide, by decide, by omega, by decide, ?_⟩
  intro q hq; omega

private theorem Mce_nr0_34 : nextrel0 Mce 3 4 := by
  refine ⟨by decide, by decide, by omega, by decide, ?_⟩
  intro q hq; omega

private theorem Mce_le0_24 : le0 Mce 2 4 :=
  ⟨by decide, by decide, (Relation.ReflTransGen.single Mce_nr0_23).tail Mce_nr0_34⟩

private theorem Mce_nr1_24 : nextrel1 Mce 2 4 := by
  refine ⟨by decide, by decide, by omega, by decide, Mce_le0_24, ?_⟩
  intro q ⟨hq1, hq2⟩
  have hle := le0_le' hq2
  rcases Nat.lt_or_ge q 4 with h | h
  · rw [show q = 3 from by omega]; decide
  · rw [show q = 4 from by omega]

private theorem Mce_uniq {y : ℕ} (h : nextrel1 Mce y 4) : y = 2 := by
  have hy : y < 4 := h.2.2.1
  have hlt := h.2.2.2.1
  rcases Nat.lt_or_ge y 2 with h2 | h2
  · rcases Nat.lt_or_ge y 1 with h1 | h1
    · rw [show y = 0 from by omega] at hlt; exact absurd hlt (by decide)
    · rw [show y = 1 from by omega] at hlt; exact absurd hlt (by decide)
  · rcases Nat.lt_or_ge y 3 with h3 | h3
    · omega
    · rw [show y = 3 from by omega] at hlt; exact absurd hlt (by decide)

private theorem Mce_hasParent : hasParent Mce 1 4 :=
  ⟨2, nextR_one_iff.mpr Mce_nr1_24, fun _ hy => Mce_uniq (nextR_one_iff.mp hy)⟩

/-- ⛔⛔⛔ **`OrphOK` は偽**（`hr0` ／ `hz0` ／ `zle1` ／ `0 < d` を全部満たす形で）。 -/
theorem orphOK_false : ¬ OrphOK := by
  intro h
  have hblk : Lift1 (shiftr01 (2 * 1) 0 Qce) (0 * 1) = [(2, 1, 0), (3, 1, 0), (3, 0, 0)] := by
    show Lift1 (shiftr01 2 0 Qce) 0 = _
    rw [Wset.Lift1_zero]
    unfold Qce shiftr01
    rfl
  have htow : mTower Qce 2 0 1 = Qce := by
    unfold mTower
    show ((List.range 1).flatMap fun k => Lift1 (shiftr01 (2 * k) 0 Qce) (0 * k)) = Qce
    simp
  have hM : ([] : TrioSeq) ++ mTower Qce 2 0 1
      ++ (Lift1 (shiftr01 (2 * 1) 0 Qce) (0 * 1)).take (1 + 1) = Mce := by
    rw [htow, hblk]; unfold Qce Mce; rfl
  have hlen : (([] : TrioSeq) ++ mTower Qce 2 0 1).length = 3 := by
    rw [htow]; rfl
  have hnp := h [] Qce 2 0 1 1 (by omega) (by decide) ?_
  · rw [hM, hlen] at hnp
    exact hnp (by
      show hasParent Mce (srow Mce (3 + 1)) (3 + 1)
      rw [show (3 : ℕ) + 1 = 4 from rfl, show srow Mce 4 = 1 from by decide]
      exact Mce_hasParent)
  · rw [hblk,
      show (List.take (1 + 1) ([(2, 1, 0), (3, 1, 0), (3, 0, 0)] : TrioSeq))
        = [(2, 1, 0), (3, 1, 0)] from rfl,
      show srow ([(2, 1, 0), (3, 1, 0)] : TrioSeq) 1 = 1 from by decide]
    rintro ⟨y, hy, -⟩
    rw [nextR_one_iff] at hy
    have : y < 1 := hy.2.2.1
    rw [show y = 0 from by omega] at hy
    exact absurd hy.2.2.2.1 (by decide)

end CE261

/-! ### 261.1 ⛔⛔⛔⛔ **残差 5 本のうち、また 1 本が偽でした**

**⟹ ⚠ `mTowerClosedSZ_of_residues` も `horph : OrphOK` を取るので、**また空虚**です。**

**⟹ ★★★ 直す方向は 1 つしかありません: **`OrphOK` に `Q ∈ W u` を足す**。**
**⟹ ⟹ ⚠ 私の反例の `Q = [(0,1,0),(1,1,0),(1,0,0)]` が `W` に入るかは**未確認**です。**
**⟹ ⟹ ⟹ ★ `W` 所属は有限判定できない（R2）ので、⟹ **Lean で調べるしかありません**。**

**⟹ ★ そして §259 の二分法から、**足すべきものの形は決まっています**:**

    ⛔ **「`Q` の中に、ブロックの根より行 1 が小さい `le0` 祖先をもつブロッカー列」が無いこと**

**⟹ ★★ これは **`hnbQ` でも `hlocQ` でもない、第 3 の形**です。⟹ ⟹ ★ そこを詰めます。** -/

/-! ## 262. ⛔⛔⛔⛔⛔ **`OrphOK0` も偽です** —— 原因は **接頭辞が `Q` の根より浅い**こと

§261 と同じ道具で `j = 0` 版も落ちます。⟹ ★ しかも **100%**（正規化を外すと）。

    `Q = [(2,1,0), (3,0,0)]`、`d = 1`、`e = 0`、`k = 0`、`A = [(0,0,0)]`
    ⟹ `hr0(Q)` ✅ ／ `entry Q 2 0 = 0` ✅ ／ `zle1 Q` ✅ ／ `0 < d` ✅
    ⟹ `mTower Q 1 0 1 = Q`、ブロックの根 `= (3,1,0)`
    ⟹ `T = [(2,1,0), (3,0,0), (3,1,0)]` ⟹ ★ 添字 2 は **`T` の中で孤児**
       （`(3,0,0)` は行 1 が小さいが `le0` 祖先でない: 行 0 が `3 = 3` で上がらない）
    ⟹ ⛔ ところが `M = A ++ T = [(0,0,0),(2,1,0),(3,0,0),(3,1,0)]` では
       **接頭辞の `(0,0,0)` が親**（行 1 = 0 < 1、`le0` は 0→1→3）

**⟹ ★★★★★ **原因は「接頭辞が `Q` の根より浅い」こと**——⟹ ★ ＝ **`rsum` の破れ**です。**
**⟹ ⟹ ⛔ そして `rsum` は遺伝しません（§227 で**証明**）。⟹ ⟹ **今日の全部の偽の芯**です。**

⚠ **測定の注意（教訓 21）**: `entry Q 0 0 = 0` に正規化した箱では **破れ 0 / 624**、
正規化を外すと **破れ 1248 / 1248（100%）**。⟹ ★ **正規化が反例を隠していました**。 -/

section CE262
private def Q0ce : TrioSeq := [(2, 1, 0), (3, 0, 0)]
private def M0ce : TrioSeq := [(0, 0, 0), (2, 1, 0), (3, 0, 0), (3, 1, 0)]
private def T0ce : TrioSeq := [(2, 1, 0), (3, 0, 0), (3, 1, 0)]

private theorem M0ce_nr0_01 : nextrel0 M0ce 0 1 := by
  refine ⟨by decide, by decide, by omega, by decide, ?_⟩
  intro q hq; omega

private theorem M0ce_nr0_13 : nextrel0 M0ce 1 3 := by
  refine ⟨by decide, by decide, by omega, by decide, ?_⟩
  intro q hq
  rw [show q = 2 from by omega]; decide

private theorem M0ce_le0_03 : le0 M0ce 0 3 :=
  ⟨by decide, by decide, (Relation.ReflTransGen.single M0ce_nr0_01).tail M0ce_nr0_13⟩

private theorem M0ce_no_le0_23 : ¬ le0 M0ce 2 3 := by
  rintro ⟨-, -, hrt⟩
  rcases Relation.ReflTransGen.cases_tail hrt with h | ⟨c, hc, hcs⟩
  · omega
  · have h1 : 2 ≤ c := le0_le' ⟨by decide, by simpa using hcs.1, hc⟩
    have h2 : c < 3 := hcs.2.2.1
    rw [show c = 2 from by omega] at hcs
    exact absurd hcs.2.2.2.1 (by decide)

private theorem M0ce_nr1_03 : nextrel1 M0ce 0 3 := by
  refine ⟨by decide, by decide, by omega, by decide, M0ce_le0_03, ?_⟩
  intro q ⟨hq1, hq2⟩
  have hle := le0_le' hq2
  rcases Nat.lt_or_ge q 2 with h | h
  · rw [show q = 1 from by omega]; decide
  · rcases Nat.lt_or_ge q 3 with h' | h'
    · rw [show q = 2 from by omega] at hq2; exact absurd hq2 M0ce_no_le0_23
    · rw [show q = 3 from by omega]

private theorem M0ce_uniq {y : ℕ} (h : nextrel1 M0ce y 3) : y = 0 := by
  have hy : y < 3 := h.2.2.1
  rcases Nat.lt_or_ge y 1 with h0 | h1
  · omega
  · rcases Nat.lt_or_ge y 2 with h1' | h2
    · rw [show y = 1 from by omega] at h; exact absurd h.2.2.2.1 (by decide)
    · rw [show y = 2 from by omega] at h; exact absurd h.2.2.2.2.1 M0ce_no_le0_23

private theorem M0ce_hasParent : hasParent M0ce 1 3 :=
  ⟨0, nextR_one_iff.mpr M0ce_nr1_03, fun _ hy => M0ce_uniq (nextR_one_iff.mp hy)⟩

private theorem T0ce_no_le0_12 : ¬ le0 T0ce 1 2 := by
  rintro ⟨-, -, hrt⟩
  rcases Relation.ReflTransGen.cases_tail hrt with h | ⟨c, hc, hcs⟩
  · omega
  · have h1 : 1 ≤ c := le0_le' ⟨by decide, by simpa using hcs.1, hc⟩
    have h2 : c < 2 := hcs.2.2.1
    rw [show c = 1 from by omega] at hcs
    exact absurd hcs.2.2.2.1 (by decide)

/-- ⛔⛔⛔ **`OrphOK0` は偽**（`hr0` ／ `hz0` ／ `zle1` ／ `0 < d` を全部満たす形で）。 -/
theorem orphOK0_false : ¬ OrphOK0 := by
  intro h
  have hblk : (Lift1 (shiftr01 (1 * (0 + 1)) 0 Q0ce) (0 * (0 + 1))).take 1
      = [((3 : ℕ), (1 : ℕ), (0 : ℕ))] := by
    show (Lift1 (shiftr01 1 0 Q0ce) 0).take 1 = _
    rw [Wset.Lift1_zero]; unfold Q0ce shiftr01; rfl
  have htow : mTower Q0ce 1 0 (0 + 1) = Q0ce := by
    unfold mTower
    show ((List.range 1).flatMap fun k => Lift1 (shiftr01 (1 * k) 0 Q0ce) (0 * k)) = Q0ce
    simp
  have hT : mTower Q0ce 1 0 (0 + 1)
      ++ (Lift1 (shiftr01 (1 * (0 + 1)) 0 Q0ce) (0 * (0 + 1))).take 1 = T0ce := by
    rw [htow, hblk]; unfold Q0ce T0ce; rfl
  have hidx : (0 + 1) * Q0ce.length = 2 := by unfold Q0ce; rfl
  have hnp := h [((0 : ℕ), (0 : ℕ), (0 : ℕ))] Q0ce 1 0 0 (by omega) ?_
  · rw [hT, hidx] at hnp
    refine hnp ?_
    show hasParent ([((0 : ℕ), (0 : ℕ), (0 : ℕ))] ++ T0ce)
      (srow ([((0 : ℕ), (0 : ℕ), (0 : ℕ))] ++ T0ce) (1 + 2)) (1 + 2)
    rw [show ([((0 : ℕ), (0 : ℕ), (0 : ℕ))] ++ T0ce) = M0ce from by unfold T0ce M0ce; rfl,
      show (1 : ℕ) + 2 = 3 from rfl, show srow M0ce 3 = 1 from by decide]
    exact M0ce_hasParent
  · rw [hT, hidx, show srow T0ce 2 = 1 from by decide]
    rintro ⟨y, hy, -⟩
    rw [nextR_one_iff] at hy
    have hy2 : y < 2 := hy.2.2.1
    rcases Nat.lt_or_ge y 1 with h0 | h1
    · rw [show y = 0 from by omega] at hy; exact absurd hy.2.2.2.1 (by decide)
    · rw [show y = 1 from by omega] at hy; exact absurd hy.2.2.2.2.1 T0ce_no_le0_12

end CE262

/-! ### 262.1 ⛔⛔⛔⛔⛔ **今日の結論: 接頭辞の深さを無視した残差はすべて偽**

| # | 残差 | 状態 |
|---|---|---|
| 1 | `HeredNB` | ⛔ 偽（§248） |
| 2 | `RootZ1` | ⛔ 偽（§260） |
| 3 | `RootZ2` | ⛔ 偽（§260） |
| 4 | `OrphOK` | ⛔ 偽（§261） |
| 5 | **`OrphOK0`** | ⛔ **偽**（§262） |

**⟹ ★★★★★ **4 と 5 の原因は同じ**です: **接頭辞 `A` が `Q` の根より浅い**。**
**⟹ ⟹ ★ ＝ **`rsum A Q` の破れ**（`rsum A P := ∀ p ∈ A ++ P, entry P 0 0 ≤ p.1`、`Wset:1317`）。**
**⟹ ⟹ ⟹ ⛔ そして **`rsum` は遺伝しません**（§227 で証明）。**

**⟹ ★★★ ですから **設計は「`A` の深さ」を運ぶ形に変えるしかありません**。⟹ ★ そこが明日の課題です。**

⚠ **教訓 21 の再確認**: `entry Q 0 0 = 0` に正規化した箱では破れ **0 / 624**、
正規化を外すと **1248 / 1248（100%）**。⟹ ★ **正規化が反例を完全に隠していました**。 -/

/-! ## 263. ⛔⛔⛔⛔⛔⛔ **`HeredZ0` も偽です** —— 今日 6 本目

`HeredZ0` は「窓の根の行 2 が 0」。⟹ ★ §224 は **`srow = 2` の段**と **`p = 0` の段**を
潰しましたが、⟹ ⛔ **`srow = 1` かつ `p > 0`** が残っていました。⟹ そこが偽です。

    `B = [(0,0,0), (1,1,1), (2,2,0)]`、`P = []`、`j = 2`、`p = 1`
    ⟹ `hr0(B)` ✅ ／ `entry B 2 0 = 0` ✅ ／ `zle1 B` ✅
    ⟹ `srow B 2 = 1`（行 2 = 0、行 1 = 2 > 0）、**親は添字 1**（行 1 = 1 < 2、一意）
    ⟹ ⛔ 窓 `= [(1,1,1)]` ⟹ **`entry (wnd) 2 0 = 1 ≠ 0`**

**⟹ ★ **`srow = 1` の親は行 2 について何も要求しません**（`nextrel1` の定義に行 2 が無い）。**
**⟹ ⟹ ⛔ ですから **`z = 1` の列がバッドルートになれます**。⟹ ⟹ **`HeredZ0` は偽**です。** -/

section CE263
private def Bz : TrioSeq := [(0, 0, 0), (1, 1, 1), (2, 2, 0)]

private theorem Bz_nr0_12 : nextrel0 Bz 1 2 := by
  refine ⟨by decide, by decide, by omega, by decide, ?_⟩
  intro q hq; omega

private theorem Bz_le0_12 : le0 Bz 1 2 :=
  ⟨by decide, by decide, Relation.ReflTransGen.single Bz_nr0_12⟩

private theorem Bz_nr1_12 : nextrel1 Bz 1 2 := by
  refine ⟨by decide, by decide, by omega, by decide, Bz_le0_12, ?_⟩
  intro q ⟨hq1, hq2⟩
  rw [show q = 2 from by have := le0_le' hq2; omega]

private theorem Bz_uniq {y : ℕ} (h : nextrel1 Bz y 2) : y = 1 := by
  have hy : y < 2 := h.2.2.1
  rcases Nat.lt_or_ge y 1 with h0 | h1
  · rw [show y = 0 from by omega] at h
    exact absurd (h.2.2.2.2.2 1 ⟨by omega, Bz_le0_12⟩) (by decide)
  · omega

private theorem Bz_hasParent : hasParent Bz 1 2 :=
  ⟨1, nextR_one_iff.mpr Bz_nr1_12, fun _ hy => Bz_uniq (nextR_one_iff.mp hy)⟩

/-- ⛔⛔⛔ **`HeredZ0` は偽**。 -/
theorem heredZ0_false : ¬ HeredZ0 := by
  intro h
  have hB : ([] : TrioSeq) ++ Bz.take (2 + 1) = Bz := by unfold Bz; rfl
  have hlen : (([] : TrioSeq) ++ Bz.take (2 + 1)).length - 1 = 2 := by rw [hB]; rfl
  have hsr : srow Bz 2 = 1 := by decide
  have hres := h [] Bz 2 1 (by omega) (by decide) ?_ ?_
  · rw [show wnd ([] : TrioSeq) Bz 2 1 = [((1 : ℕ), (1 : ℕ), (1 : ℕ))] from by
      unfold wnd Bz; rfl] at hres
    exact absurd hres (by decide)
  · rw [hlen, hB, hsr]; exact Bz_hasParent
  · rw [hlen, hB, hsr]
    have := nextR_one_iff.mp (parent_nextR Bz_hasParent)
    rw [Bz_uniq this]; rfl

end CE263

/-! ### 263.1 ⛔⛔⛔⛔⛔⛔ **今日の最終棚卸し: 6 本中 6 本が偽でした**

| # | 残差 | 状態 | 原因 |
|---|---|---|---|
| 1 | `HeredNB` | ⛔ 偽（§248） | 証人が窓の外へ落ちる |
| 2 | `RootZ1` | ⛔ 偽（§260） | `[(0,0,2)] ∈ W 2` |
| 3 | `RootZ2` | ⛔ 偽（§260） | 同上 |
| 4 | `OrphOK` | ⛔ 偽（§261） | 接頭辞が `Q` の根より浅い |
| 5 | `OrphOK0` | ⛔ 偽（§262） | 同上 |
| 6 | **`HeredZ0`** | ⛔ **偽**（§263） | `srow = 1` の親は行 2 を制約しない |

**⟹ ⛔⛔ 残るのは **`ZeroDOK`** と **`d = 0 → e = 0`** の 2 本だけです。**
**⟹ ⟹ ⚠ ですから **`mTowerClosedSZ_of_residues` は今も空虚**です。**

**⟹ ★★★★★ ⟹ **今日の正味の成果は「設計が全部間違っていたと確定させたこと」**です。**
**⟹ ⟹ ★ そして **どこが間違っていたか**も 3 つに整理できました:**

    **(a)** **接頭辞の深さを無視した**（`OrphOK` / `OrphOK0`）⟹ `rsum` が要るが遺伝しない
    **(b)** **窓の根が「元の根」と違うことを無視した**（`HeredNB` / `HeredZ0`）
    **(c)** **`W` が `z < 2` で閉じていない**（`RootZ1` / `RootZ2`）⟹ 目標に書けば消える

**⟹ ★ (c) は §260 で直しました。⟹ ⛔ (a)(b) は**設計のやり直し**が要ります。** -/

/-! ## 264. ⛔⛔⛔⛔ **`Q ∈ W u` を足しても `OrphOK` は偽**です

team-lead の (c)/(RSUM2') に答えるための、決定的な検算です。

**⟹ ★ 帰納法は `A' ++ V ∈ W u` を運ぶので、`Wtower2.W_drop` で **`V ∈ W (lev …)` が出ます**
（H12 の `window_mem_W`）。⟹ ⟹ ★★ ですから **`Q ∈ W u` は各段で使えます**。**

**⟹ ⛔ ですが §261 の反例 `Q = [(0,1,0),(1,1,0),(1,0,0)]` は **行 2 が全部 0** なので、
`zeroRow2_mem_Wself` で **`W u` に入ります**（`lev Q 0 = 2`）。**
**⟹ ⟹ ⛔⛔ ですから **`Q ∈ W u` を足しても `OrphOK` は偽**です。** -/

private theorem Qce_zeroRow2 : ∀ p ∈ Qce, p.2.2 = 0 := by decide

private theorem Qce_lev : lev Qce 0 = 2 := by unfold lev Qce entry; simp

theorem Qce_mem_W {u : ℕ} (hu : 2 ≤ u) : Qce ∈ W u := by
  rw [mem_Wself_iff]
  exact ⟨zeroRow2_mem_Wself Qce_zeroRow2, by rw [Qce_lev]; omega⟩

/-- ⛔ **`W` つきの `OrphOK`**（帰納法が実際に持っている前提を全部入れたもの）。 -/
def OrphOKW : Prop :=
  ∀ (u : ℕ) (A Q : TrioSeq) (d e n j : ℕ), A ∈ W u → Q ∈ W u → A ++ Q ∈ W u →
    (∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) →
    entry Q 2 0 = 0 → (∀ q, q < Q.length → entry Q 2 q ≤ 1) → 0 < d →
    0 < j → j < Q.length →
    ¬ hasParent ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        (srow ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) j) j →
    ¬ hasParent (A ++ mTower Q d e n
          ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        (srow (A ++ mTower Q d e n
          ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
          ((A ++ mTower Q d e n).length + j))
        ((A ++ mTower Q d e n).length + j)

/-- ⛔⛔⛔⛔ **`W` つきでも偽**。⟹ ★ §261 と同じ反例がそのまま通ります。 -/
theorem orphOKW_false : ¬ OrphOKW := by
  intro h
  have hblk : Lift1 (shiftr01 (2 * 1) 0 Qce) (0 * 1) = [(2, 1, 0), (3, 1, 0), (3, 0, 0)] := by
    show Lift1 (shiftr01 2 0 Qce) 0 = _
    rw [Wset.Lift1_zero]; unfold Qce shiftr01; rfl
  have htow : mTower Qce 2 0 1 = Qce := by
    unfold mTower
    show ((List.range 1).flatMap fun k => Lift1 (shiftr01 (2 * k) 0 Qce) (0 * k)) = Qce
    simp
  have hM : ([] : TrioSeq) ++ mTower Qce 2 0 1
      ++ (Lift1 (shiftr01 (2 * 1) 0 Qce) (0 * 1)).take (1 + 1) = Mce := by
    rw [htow, hblk]; unfold Qce Mce; rfl
  have hlen : (([] : TrioSeq) ++ mTower Qce 2 0 1).length = 3 := by rw [htow]; rfl
  have hnp := h 2 [] Qce 2 0 1 1 (W_nil 2) (Qce_mem_W (le_refl 2))
    (by simpa using Qce_mem_W (le_refl 2))
    (by intro l hl0 hl
        have : l < 3 := by simpa [Qce] using hl
        rcases Nat.lt_or_ge l 2 with h | h
        · rw [show l = 1 from by omega]; decide
        · rw [show l = 2 from by omega]; decide)
    (by decide)
    (by intro q hq
        have : q < 3 := by simpa [Qce] using hq
        rcases Nat.lt_or_ge q 1 with h | h
        · rw [show q = 0 from by omega]; decide
        · rcases Nat.lt_or_ge q 2 with h' | h'
          · rw [show q = 1 from by omega]; decide
          · rw [show q = 2 from by omega]; decide)
    (by omega) (by omega) (by simp [Qce]) ?_
  · rw [hM, hlen] at hnp
    exact hnp (by
      show hasParent Mce (srow Mce (3 + 1)) (3 + 1)
      rw [show (3 : ℕ) + 1 = 4 from rfl, show srow Mce 4 = 1 from by decide]
      exact Mce_hasParent)
  · rw [hblk,
      show (List.take (1 + 1) ([(2, 1, 0), (3, 1, 0), (3, 0, 0)] : TrioSeq))
        = [(2, 1, 0), (3, 1, 0)] from rfl,
      show srow ([(2, 1, 0), (3, 1, 0)] : TrioSeq) 1 = 1 from by decide]
    rintro ⟨y, hy, -⟩
    rw [nextR_one_iff] at hy
    have : y < 1 := hy.2.2.1
    rw [show y = 0 from by omega] at hy
    exact absurd hy.2.2.2.1 (by decide)

/-! ### 264.1 ⟹ ⛔ **(RSUM2') の答え: 遺伝は要りませんが、それでは足りません**

    **(1)** 帰納法は **`A' ++ V ∈ W u`** を運びます（`hIH` の前提）
    **(2)** ⟹ ★ `Wtower2.W_drop` ＋ `Wset.W_take` で **`V ∈ W (lev …)`**（H12 `window_mem_W`）
    **(3)** ⟹ ★★ ですから **`∀ u, ∀ Q ∈ W u, P Q` の形の条件は、各段で無料で使えます**
       ⟹ ⟹ ★ **遺伝を証明する必要はありません**（段 `u` が変わるので **`∀ u` は必須**）
    **(4)** ⟹ ⛔ **ですが `OrphOKW` が偽**なので、⟹ **`W` を足しても閉じません**

**⟹ ★★★ ですから **(RSUM2') の答えは「遺伝は要らない。ただしそれでは足りない」**です。** -/

/-! ## 265. ⛔⛔⛔⛔⛔ **`OrphOK0` も `W` ＋ `R1<=R0` を足しても偽**です

§262 の反例 `Q = [(2,1,0), (3,0,0)]`、`A = [(0,0,0)]` を、**帰納法が持つ前提を全部足した形**で
落とします。⟹ ★ さらに **R2 の `R1<=R0`（`∀ i, entry Q 1 i ≤ entry Q 0 i`）も満たします**:

    列 0: `1 ≤ 2` ✅  ／  列 1: `0 ≤ 3` ✅

**⟹ ⛔⛔ ですから **`Q` の側にどんな条件を足しても、`OrphOK0` は救えません**。**
**⟹ ⟹ ★★★ **問題は `A`（接頭辞）の側**です。⟹ ⟹ **`A = [(0,0,0)]` は `W` の元**で、
`Q` の根より **浅い**（行 0 が `0 < 2`）。⟹ ★ ＝ **`rsum` の破れ**。 -/

private theorem Q0ce_zeroRow2 : ∀ p ∈ Q0ce, p.2.2 = 0 := by decide
private theorem Q0ce_lev : lev Q0ce 0 = 2 := by unfold lev Q0ce entry; simp

theorem Q0ce_mem_W {u : ℕ} (hu : 2 ≤ u) : Q0ce ∈ W u := by
  rw [mem_Wself_iff]
  exact ⟨zeroRow2_mem_Wself Q0ce_zeroRow2, by rw [Q0ce_lev]; omega⟩

theorem Ace_mem_W (u : ℕ) : [((0 : ℕ), (0 : ℕ), (0 : ℕ))] ∈ W u := by
  rw [mem_Wself_iff]
  refine ⟨zeroRow2_mem_Wself (by decide), ?_⟩
  show lev [((0 : ℕ), (0 : ℕ), (0 : ℕ))] 0 ≤ u
  unfold lev entry; simp

theorem AQ0ce_mem_W (u : ℕ) : [((0 : ℕ), (0 : ℕ), (0 : ℕ))] ++ Q0ce ∈ W u := by
  rw [mem_Wself_iff]
  refine ⟨zeroRow2_mem_Wself (by decide), ?_⟩
  show lev ([((0 : ℕ), (0 : ℕ), (0 : ℕ))] ++ Q0ce) 0 ≤ u
  unfold lev Q0ce entry; simp

/-- ⛔ **`W` ＋ `R1<=R0` つきの `OrphOK0`**（帰納法が持つ前提を全部入れたもの）。 -/
def OrphOK0W : Prop :=
  ∀ (u : ℕ) (A Q : TrioSeq) (d e k : ℕ), A ∈ W u → Q ∈ W u → A ++ Q ∈ W u →
    (∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) →
    entry Q 2 0 = 0 → (∀ q, q < Q.length → entry Q 2 q ≤ 1) →
    (∀ i, i < Q.length → entry Q 1 i ≤ entry Q 0 i) → 0 < d →
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

/-- ⛔⛔⛔⛔⛔ **`W` ＋ `R1<=R0` を足しても偽**。 -/
theorem orphOK0W_false : ¬ OrphOK0W := by
  intro h
  have hblk : (Lift1 (shiftr01 (1 * (0 + 1)) 0 Q0ce) (0 * (0 + 1))).take 1
      = [((3 : ℕ), (1 : ℕ), (0 : ℕ))] := by
    show (Lift1 (shiftr01 1 0 Q0ce) 0).take 1 = _
    rw [Wset.Lift1_zero]; unfold Q0ce shiftr01; rfl
  have htow : mTower Q0ce 1 0 (0 + 1) = Q0ce := by
    unfold mTower
    show ((List.range 1).flatMap fun k => Lift1 (shiftr01 (1 * k) 0 Q0ce) (0 * k)) = Q0ce
    simp
  have hT : mTower Q0ce 1 0 (0 + 1)
      ++ (Lift1 (shiftr01 (1 * (0 + 1)) 0 Q0ce) (0 * (0 + 1))).take 1 = T0ce := by
    rw [htow, hblk]; unfold Q0ce T0ce; rfl
  have hidx : (0 + 1) * Q0ce.length = 2 := by unfold Q0ce; rfl
  have hnp := h 2 [((0 : ℕ), (0 : ℕ), (0 : ℕ))] Q0ce 1 0 0 (Ace_mem_W 2)
    (Q0ce_mem_W (le_refl 2)) (AQ0ce_mem_W 2)
    (by intro l hl0 hl
        have : l < 2 := by simpa [Q0ce] using hl
        rw [show l = 1 from by omega]; decide)
    (by decide)
    (by intro q hq
        have : q < 2 := by simpa [Q0ce] using hq
        rcases Nat.lt_or_ge q 1 with hq' | hq'
        · rw [show q = 0 from by omega]; decide
        · rw [show q = 1 from by omega]; decide)
    (by intro i hi
        have : i < 2 := by simpa [Q0ce] using hi
        rcases Nat.lt_or_ge i 1 with hi' | hi'
        · rw [show i = 0 from by omega]; decide
        · rw [show i = 1 from by omega]; decide)
    (by omega) ?_
  · rw [hT, hidx] at hnp
    refine hnp ?_
    show hasParent ([((0 : ℕ), (0 : ℕ), (0 : ℕ))] ++ T0ce)
      (srow ([((0 : ℕ), (0 : ℕ), (0 : ℕ))] ++ T0ce) (1 + 2)) (1 + 2)
    rw [show ([((0 : ℕ), (0 : ℕ), (0 : ℕ))] ++ T0ce) = M0ce from by unfold T0ce M0ce; rfl,
      show (1 : ℕ) + 2 = 3 from rfl, show srow M0ce 3 = 1 from by decide]
    exact M0ce_hasParent
  · rw [hT, hidx, show srow T0ce 2 = 1 from by decide]
    rintro ⟨y, hy, -⟩
    rw [nextR_one_iff] at hy
    have hy2 : y < 2 := hy.2.2.1
    rcases Nat.lt_or_ge y 1 with h0 | h1
    · rw [show y = 0 from by omega] at hy; exact absurd hy.2.2.2.1 (by decide)
    · rw [show y = 1 from by omega] at hy; exact absurd hy.2.2.2.2.1 T0ce_no_le0_12

/-! ### 265.1 ⟹ ★★★★★ **結論: `Q` 側の条件では閉じません**

    ✅ **`Q ∈ W u`** ……………… 足しても偽（§264、§265）
    ✅ **`hr0` ／ `hz0` ／ `zle1`** … 足しても偽
    ✅ **`R1<=R0`（R2 の新条件）** … 足しても偽（§265）
    ⟹ ⛔ **`OrphOK` / `OrphOK0` は、`Q` に何を課しても救えません**

**⟹ ★★★ **問題は `A`（接頭辞）です**。⟹ ⟹ **`A = [(0,0,0)]` は `W` の元**なのに、
`Q` の根より **浅い**（行 0 が `0 < 2`）。⟹ ★ ＝ **`rsum A Q` の破れ**。**

**⟹ ★★★★★ ですから **設計は `A` に条件を課すか、`A` が親を供給しても構わない形にする**——
⟹ ★ **その 2 つしかありません**。⟹ ⟹ ⛔ そして **`rsum` は運べません**（§227 ＋ 前のブロックの存在）。**

**⟹ ⟹ ⟹ ★★★★★★ ですから **「`A` が親を供給しても構わない形」が唯一の道**です。**
**⟹ ⚠ そこは `Aop` の節 3（graft）の話で、⟹ ★ **`Wset` / `L105Cap` の領域**です。** -/

/-! ## 266. ⛔⛔⛔⛔⛔⛔ **(L-SNOC) の答え: 道 (B) は測度を壊します**

§265 で「残る道は **(B)「`A` が親を供給しても構わない形」**だけ」と書きました。
**⟹ ⛔ 読みました。⟹ ⟹ **(B) は測度を壊します**。⟹ 理由を書きます。**

### ★ 事実 1: `snocStep_oper_pre` は **親がブロックの中**であることを要求します

```lean
theorem snocStep_oper_pre (hjB : j < B.length) (hpj : p < j) … 
    (hpe : parent (P ++ B.take (j+1)) … = **P.length + p**) :
    ∃ V d0 d1, **V.length = j - p** ∧ (P ++ B.take (j+1))⟦m⟧ = (P ++ B.take p) ++ mTower V d0 d1 m
```

**⟹ ★ 窓の長さは **`j - p < |Q|`** ⟹ ⟹ ★★ `towerMeas V = 3(j-p) + r < 3|Q| + r` ⟹ **減ります** ✅**

### ⛔⛔ 事実 2 —— ★★★ **【2026-08-30 自己訂正】ここは誤りでした**

**⛔ 旧: 「親が `c < P.length` にあると **窓の長さ ≥ n·|Q| − |A|** ⟹ 測度が増える」**

**⟹ ⛔⛔ **算数が間違っています**。⟹ ★ 正しくは **`|V| = |P| + j − c`** で、
`c` が `|P|` に**近ければ窓は短い**です。⟹ ⟹ ⛔ 私は
**「最後のブロックの外」と「`A` の中」を混同**していました。**

**⟹ ★★★★★ そして **実測は逆**でした（シート由来の窓 `Q`、`|Q| ≤ 5`、`n ≤ 2`、`d ≤ 2`、`e ≤ 1`）:**

    分母（親が一意な手）**19,168**
    ⟹ **越境（親が塔／接頭辞）208 件**
    ⟹ ⟹ ★★★★★ **窓 < |Q| が 208 件（100.0000%）**、**窓 ≥ |Q| は 0 件**

**⟹ ★ 理由: **`nextrel` の最小性が親を手前に引き寄せる**ので、越境しても
**1 つ前のブロックの末尾あたり**に落ちます。⟹ ⟹ ★★ **`n` に比例しません**。**

**⟹ ★★★★★★ ⟹ ですから **測度はまだ生きている可能性があります**。**

### ★★★★ 事実 2'（訂正版）: **`hbound` は必要より強い**

`towerMeas` が要求するのは **`|V| < |Q|`**、すなわち **`j0 > |P| + j − |Q|`** だけです。
**⟹ ⛔ ところが `hbound` は **`j0 ≥ |P|`**（最後のブロックの中）を要求しています。**
**⟹ ⟹ ★★★ ですから **`hbound` を「親が末尾 `|Q|` 列の中」に弱められる**はずです。**

**⟹ ★ そして `oper` の定義は **`j0` がどこでも動きます**（`M.take j0 ++ (range n).flatMap …`）。**
**⟹ ⟹ ★★★★ ですから **`snocStep_oper_pre` を「親がどこでも」版に一般化**できるはずです。**
**⟹ ⟹ ⟹ ⚠ そこが次の作業です。**

⚠ **教訓 14**: 上の 208/208 は**測定**です。⟹ ★ **箱は小さい**（`|Q| ≤ 5`、`n ≤ 2`）。
**⟹ ⛔ ですが **旧「事実 2」の算数が誤りであること**は、測定に依らず確かです。

### ★★★★★ ⟹ **構造的な結論**

    ★ **この帰納法は「バッドルートが最後のブロックの中にある」ことを本質的に使っています**
    ⟹ ★★ それが `hbound`（`(A ++ mTower).length ≤ parent`）です
    ⟹ ⟹ ⛔ そして **`hbound` が破れるのが、まさに残差の場合**です
    ⟹ ⟹ ⟹ ⛔⛔ **`OrphOK` はその穴を塞ぐための（偽の）パッチ**でした

**⟹ ★★★★★★ ですから **直すには測度を変えるしかありません**。⟹ ⟹ ★ 候補:**

    **(M1)** 測度に **`|A|` や `n` を入れる** ⟹ ⚠ ですが `A` は帰納法の外側で ∀ 量化されています
    **(M2)** **`|V|` ではなく別の量**（例: 順序数の高さ）で測る ⟹ ★ 大工事
    **(M3) ★★★★ 「親が接頭辞にある」場合に、**別の閉包定理**を使う
        ⟹ ★ ＝ `L53.PrefixCopies` / `Wtower2.ShiftTowerClosed` の系統
        ⟹ ⟹ ⚠ そこは私の担当外です

**⟹ ⚠ ですから **私の側の結論は「この設計では閉じない」**です。⟹ ★ 測度の設計は R2/team-lead の領域です。**

⚠ **教訓 14**: 上は**読解**であって証明ではありません。**⟹ ★ ですが `snocStep_oper_pre` の型が
`V.length = j - p` を返している以上、`p` が `P` の外なら窓が伸びるのは**型から見えます**。 -/

/-! ## 267. ★★★★★ **(L-AMIN)**: 残差を `amin` の言葉で 1 行にします

H12 が `Cgraft.amin`（`Cgraft:848`、**行 0 祖先鎖の行 1 の最小値**）で
**前提なしの同値**を出しました（`H12Export.lean:3689/3716`）:

    `hasParent M 1 j ↔ amin M j < entry M 1 j`
    `¬ hasParent M 1 j ↔ amin M j = entry M 1 j`

**⟹ ★★★ ですから `OrphOK` の行 1 の残差が **1 本の不等式**になります。** -/

/-! ⚠ **`import H12Export` は「最後にビルドされた版」しか見えません**。
H12 の最新分（`amin` の 2 本）は未ビルドなので、⟹ ★ **今回は逐語で写します**
（`H12Export.lean:3689 / 3716`）。⟹ ⟹ ★ ビルドが更新されたら `H12Export.` に差し替えます。 -/

/-- ★★★★★★★ **行 1 の親の存在は `amin` で決まる**（前提なし）。 -/
theorem hasParent1_iff_amin_lt {M : TrioSeq} {j : ℕ} (hj : j < M.length) :
    hasParent M 1 j ↔ amin M j < entry M 1 j := by
  constructor
  · rintro ⟨y, hy, -⟩
    unfold nextR at hy
    rw [if_neg (by omega), if_pos rfl] at hy
    exact Nat.lt_of_le_of_lt (amin_le hy.2.2.2.2.1.2.2) hy.2.2.2.1
  · intro h
    obtain ⟨y, hrt, heq⟩ := amin_mem M j
    have hyj : y ≤ j := rtg0_index_le hrt
    have hylt : y < j := by
      rcases Nat.eq_or_lt_of_le hyj with he | hl
      · exfalso
        rw [he] at heq
        omega
      · exact hl
    have hle0 : le0 M y j := ⟨by omega, hj, hrt⟩
    obtain ⟨y', hy'⟩ := exists_nextrel1_of_le0_lt hj ⟨y, hylt, hle0, by omega⟩
    exact ⟨y', by
      show nextR M 1 y' j
      unfold nextR; rw [if_neg (by omega), if_pos rfl]; exact hy', by
      intro b hb
      unfold nextR at hb
      rw [if_neg (by omega), if_pos rfl] at hb
      exact nextrel1_src_unique hb hy'⟩


/-- ★★★★★ ⟹ **孤児 ⟺ `amin` が的の行 1 に等しい**。 -/
theorem orphan_row1_iff_amin_eq {M : TrioSeq} {j : ℕ} (hj : j < M.length) :
    ¬ hasParent M 1 j ↔ amin M j = entry M 1 j := by
  rw [hasParent1_iff_amin_lt hj]
  have hle : amin M j ≤ entry M 1 j := amin_le Relation.ReflTransGen.refl
  omega



/-- ★★★★★ **`OrphOK` の行 1 の破れ ＝ 「接頭辞が `amin` を下げる」**（前提なし）。 -/
theorem orphOK_row1_break_iff_amin {A T : TrioSeq} {j : ℕ} (hjT : j < T.length) :
    (¬ hasParent T 1 j ∧ hasParent (A ++ T) 1 (A.length + j))
      ↔ (amin T j = entry T 1 j ∧
          amin (A ++ T) (A.length + j) < entry (A ++ T) 1 (A.length + j)) := by
  have hjM : A.length + j < (A ++ T).length := by rw [List.length_append]; omega
  rw [orphan_row1_iff_amin_eq hjT, hasParent1_iff_amin_lt hjM]

/-- ★★★★ ⟹ **入れ替えた形**（`entry` を `T` の言葉に揃えたもの）。 -/
theorem orphOK_row1_break_amin_lt {A T : TrioSeq} {j : ℕ} (hjT : j < T.length)
    (hnp : ¬ hasParent T 1 j) (hp : hasParent (A ++ T) 1 (A.length + j)) :
    amin (A ++ T) (A.length + j) < amin T j := by
  have hjM : A.length + j < (A ++ T).length := by rw [List.length_append]; omega
  have h1 := (orphan_row1_iff_amin_eq hjT).mp hnp
  have h2 := (hasParent1_iff_amin_lt hjM).mp hp
  rw [show A.length + j = A.length + j from rfl, entry_append_right] at h2
  omega

/-! ### 267.1 ⟹ ★★★★★ **残差の最終形（1 行）**

    ⛔ **`amin (A ++ T) (|A| + j) < amin T j`**
    ＝ **「接頭辞が、`j` の行 0 祖先鎖の行 1 の最小値を下げる」**

**⟹ ★ そして §257 が「越境はブロックの根 1 点だけ」と言うので、⟹ ★★ **鎖は必ず根を通ります**。**
**⟹ ⟹ ★★★ ですから **下げられるのは「根より前の鎖の部分」だけ**です:**

    `amin (A ++ T) (|A| + j) = min (amin T j) (amin (A ++ T) |A|)`   ← ★ **分解できるはず**

**⟹ ★★★★ ⟹ ですから **残差は `amin (A ++ T) |A| < amin T j`**——⟹ ★ **`T` の根の鎖の話**です。**
**⟹ ⟹ ★ ＝ **接頭辞に「`T` の根の行 0 祖先で、行 1 が `amin T j` より小さい列」がある**こと。**

⚠ **`min` の分解は未証明**です（`amin` は `sInf` なので、鎖の分割補題が要ります）。
**⟹ ★ H12 の `amin` まわりに既にあるかもしれません。⟹ **書く前に grep してください**。** -/

/-! ## 268. ★★★★★★ **(L-AMIN) の仕上げ**: 残差は「`T` の根の鎖」の話に落ちます

§267 で残差は **`amin (A ++ T) (|A| + j) < amin T j`** になりました。
**⟹ ★ ここで §253 の `shallow_append_right` ＋ H12 の `nextrel0_src_ge_of_shallow` が効きます。**

⚠ **書く前に索引を引きました**: `Cgraft` に `amin_cons`（1 列の接頭辞）・`amin_graft_low`・
`amin_take`・`amin_le1` はありますが、**一般の `A ++ T` の分解はありません**。⟹ ★ 書きます。 -/

/-- ★★★★★ **接頭辞から出た行 0 の鎖は、必ず `T` の根を通る**（`hr0(T)` だけ）。 -/
theorem rtg0_cross_through_root {A T : TrioSeq} {y j : ℕ}
    (hs : ∀ x, 0 < x → x < T.length → entry T 0 0 < entry T 0 x)
    (hy : y < A.length)
    (h : Relation.ReflTransGen (nextrel0 (A ++ T)) y (A.length + j)) :
    Relation.ReflTransGen (nextrel0 (A ++ T)) y A.length ∨ A.length + j < A.length := by
  have hsh := shallow_append_right (A := A) hs
  have key : ∀ z, Relation.ReflTransGen (nextrel0 (A ++ T)) y z →
      z < A.length ∨ Relation.ReflTransGen (nextrel0 (A ++ T)) y A.length := by
    intro z hz
    induction hz with
    | refl => exact Or.inl hy
    | @tail x w hx hxw ih =>
        rcases ih with hxlt | hres
        · rcases Nat.lt_or_ge w A.length with hw | hw
          · exact Or.inl hw
          · rcases Nat.eq_or_lt_of_le hw with hw0 | hw0
            · rw [hw0]; exact Or.inr (hx.tail hxw)
            · exact absurd (nextrel0_src_ge_of_shallow hsh (by omega) hxw) (by omega)
        · exact Or.inr hres
  rcases key (A.length + j) h with hlt | hres
  · exact Or.inr hlt
  · exact Or.inl hres

/-- ★★★★★★ ⟹ **残差は「`T` の根の `amin`」に落ちます**（`hr0(T)` だけ）。 -/
theorem amin_break_at_root {A T : TrioSeq} {j : ℕ} (hj0 : 0 < j) (hjT : j < T.length)
    (hs : ∀ x, 0 < x → x < T.length → entry T 0 0 < entry T 0 x)
    (h : amin (A ++ T) (A.length + j) < amin T j) :
    amin (A ++ T) A.length < amin T j := by
  obtain ⟨y, hrt, heq⟩ := amin_mem (A ++ T) (A.length + j)
  rcases Nat.lt_or_ge y A.length with hy | hy
  · -- ★ 最小を与える列が接頭辞の中 ⟹ 鎖は `T` の根を通る
    rcases rtg0_cross_through_root (A := A) (T := T) hs hy hrt with hres | hbad
    · exact lt_of_le_of_lt (amin_le hres) (by omega)
    · omega
  · -- ⛔ 最小を与える列が `T` の中 ⟹ `amin T j` がそれ以下なので矛盾
    exfalso
    obtain ⟨y', rfl⟩ : ∃ y', y = A.length + y' := ⟨y - A.length, by omega⟩
    have hylt : y' ≤ j := by
      have := rtg0_index_le hrt; omega
    have hyT : y' < T.length := by omega
    have hrtT : Relation.ReflTransGen (nextrel0 T) y' j := by
      have hL : A.length + T.length ≤ (A ++ T).length := by rw [List.length_append]
      have := le0_window (T := A ++ T) (s := A.length) (L := T.length) hL hyT hjT
        ⟨by rw [List.length_append]; omega, by rw [List.length_append]; omega, hrt⟩
      rw [drop_take_append_right] at this
      exact this.2.2
    have := amin_le hrtT
    rw [entry_append_right] at heq
    omega

/-! ### 268.1 ⟹ ★★★★★★ **残差の最終形（今日の到達点）**

    ⛔ **`amin (A ++ T) |A| < amin T j`**
    ＝ **「接頭辞に、`T` の根の行 0 祖先で、行 1 が `amin T j` より小さい列がある」**

**⟹ ★ **`j` が消えました**（左辺は `j` に依らない）。⟹ ⟹ ★★ ですから残差は:**

    **`amin (A ++ T) |A| < min { amin T j : j は `T` の中で行 1 の孤児 }`**

**⟹ ★★★ ＝ **「接頭辞の `amin` が、`T` の孤児の `amin` より小さい」** 1 本です。**
**⟹ ⟹ ★ そして §262 の反例で確かめると: `A = [(0,0,0)]`、`T` の根は `(2,1,0)`**
**⟹ ⟹ ⟹ `amin (A ++ T) 1 = min(0, 1) = 0`、`amin T 2 = 1` ⟹ ⛔ **`0 < 1`** ⟹ **破れます** ✓**

**⟹ ★★★★ ですから **「接頭辞の `amin` を上から押さえる」**のが、次の設計で要るものです。**
**⟹ ⚠ ⟹ ですがそれは **`rsum` の行 1 版**（H12 の `rsum1`）で、⟹ ⛔ **運べません**。**

⚠ **教訓 14**: §268 は緑ですが、**残差は縮んだだけで、消えていません**。 -/

/-! ## 269. ⚠⚠ **(L-ARG) の答え: `argOK` と `rsum` は同じではありません** —— むしろ**両立しません**

R2 の報告「**`argOK` ＝ `rsum` そのもの**」を確かめました。⟹ ⛔ **同じではありません**。

    `Wset:1314`  `argOK R : ∀ p ∈ R, **0 < p.1**`
      ＝ 「`R` の全列が **深さ 0 より真に深い**」＝ **頭 `(0,v,z)` が狭義に最も浅い**
    `Wset:1317`  `rsum A P : ∀ p ∈ A ++ P, **entry P 0 0 ≤ p.1**`
      ＝ 「`A ++ P` の全列が **`P` の根以上に深い**」＝ **接頭辞が `P` の根より浅くない**（弱い不等号）

**⟹ ★ **どちらも「根が最も浅い」型**ですが、⟹ ⛔ **切れ目に対する向きが逆**です:**

    `argOK` … **頭（`A` の側）が最も浅い**ことを言う
    `rsum`  … **後ろ（`P` の側）の根が最も浅い**ことを言う

**⟹ ⛔⛔ ですから `CoreCap` の配置（`A = [(0,v,z)]`、`P = M`）では **両立しません**。** -/

theorem argOK_rsum_incompatible {v z : ℕ} {M : TrioSeq} (hne : M ≠ [])
    (harg : Wset.argOK M) : ¬ Wset.rsum [((0, v, z) : ℕ × ℕ × ℕ)] M := by
  intro hr
  have h0 : entry M 0 0 ≤ 0 := by
    have := hr ((0, v, z) : ℕ × ℕ × ℕ) (by simp)
    simpa using this
  have hM0 : M.getD 0 (0, 0, 0) ∈ M := by
    cases M with
    | nil => exact absurd rfl hne
    | cons a t => simp
  have := harg _ hM0
  have hent : entry M 0 0 = (M.getD 0 (0, 0, 0)).1 := by unfold entry; simp
  omega

/-! ### 269.1 ⟹ ★★★ **正しい言い方**

**⟹ ★ **R2 の観察の中身は正しい**です:「**根が最も浅いという条件が、再帰の下で保たれない**」。**
**⟹ ⟹ ⛔ ですが **`argOK` と `rsum` は同じ命題ではありません**。⟹ ★ **同じ「型」の別の条件**です。**

    ★ 私の **失敗の型 (a)**（接頭辞の深さ）と **型 (b)**（窓の根が元の根と違う）が、
      ⟹ ★★ **`argOK` の喪失（R2 の I3、16〜17%）と同じ現象**を指しています
    ⚠ ですから **「私の §227 が `CoreCap` にも直接効く」とは言えません**
      ⟹ ★ §227 は **`rsum` の窓への遺伝**についてで、`argOK` の再取得とは**別の命題**です

**⟹ ⚠ **教訓 14**: 名前が違うものを「同じ」と言うと、⟹ ⛔ **今日 3 回起きた「主語のずれ」**になります。**

## 270. ★★★★★ **(L-M3) の答え: `PrefixCopies` は接頭辞に条件を課しません**

```lean
def PrefixCopies : Prop :=
  ∀ (u n : ℕ) (A Q : TrioSeq), **A ++ Q ∈ W u** →
    **(∀ q ∈ Q, entry Q 0 0 ≤ q.1)** →                -- ★ 条件は `Q` の側だけ
    A ++ ((List.range n).flatMap fun _ => Q) ∈ W u
```

**⟹ ★★★★★ **側条件は `Q` の中の話だけ**で、⟹ ⟹ ★ **`A` の深さには何も要求しません**。**
**⟹ ⟹ ★★★ ですから **`PrefixCopies` は、私たちが欲しい「形」そのもの**です。**

**⟹ ⚠ ただし 2 つ制約があります:**

    ⛔ **`d = e = 0`（同じブロックの繰り返し）**に限られます
      ⟹ ★ 私の `ZeroDOK` がまさにこれ（`mTower Q 0 0 n = n 個のコピー`）
    ⛔ そして **`PrefixCopies` 自身が未証明**です（`A = []` の場合だけ緑: `prefixCopies_nil`）

**⟹ ★★★★ ⟹ ですから **(M3) の中身は「`PrefixCopies` を `d > 0` に一般化する」**ことです。**
**⟹ ⟹ ★ そして **なぜ `d = e = 0` なら `A` に条件が要らないのか**——⟹ ⚠ そこが鍵だと思います:**

    ★ `d = 0` ⟹ **コピーどうしの行 0 が等しい** ⟹ **`nextrel0` はブロックをまたげません**
      （`nextrel0` は行 0 の狭義増加を要求するので）
    ⟹ ★★ ですから **接頭辞がどれだけ浅くても、鎖が塔の中で止まります**
    ⟹ ⟹ ★★★ ⟹ **`d = 0` が「越境を構造的に禁じている」**——⟹ ★ **`rsum` の代わりに働いています**

**⟹ ⛔ ⟹ ですから **`d > 0` にすると、その保護が消えます**。⟹ ★ **一般化はそのままでは通りません**。**
**⟹ ⟹ ★★ ⟹ **`d > 0` では「行 0 が上がる」ので、接頭辞から鎖が入れます**（私の §256/§257）。**

⚠ **教訓 14**: 上は**読解**です。⟹ ★ ですが **`nextrel0` が狭義増加を要求する**のは定義です。 -/

/-! ## 271. ★★★★★★ **`d = 0` の保護を定理にします** —— `PrefixCopies` が接頭辞に条件を要らない理由

§270 で「`d = 0` なら `nextrel0` がブロックをまたげない」と読みました。⟹ ★ 証明します。

    `d = 0` ⟹ ブロック `k` の列 `q` の行 0 は **`entry Q 0 q`**（`k` に依らない）
    ⟹ ★ 的が **`k' * |Q| + q'`（`q' > 0`）**なら、最小性を **`j := k' * |Q|`（そのブロックの根）**に
      当てて `entry Q 0 q' ≤ entry Q 0 0` ⟹ ⛔ `hr0` と矛盾
    ⟹ ★ 的が **ブロックの根（`q' = 0`）**なら、始点の行 0 は `entry Q 0 (…) ≥ entry Q 0 0` なので
      **狭義増加が取れません**
    ⟹ ⟹ ★★★★★ ですから **どちらの場合も越境できません**。 -/

theorem mTower_entry0_of_d_zero {Q : TrioSeq} {e n k q : ℕ} (hk : k < n) (hq : q < Q.length) :
    entry (mTower Q 0 e n) 0 (k * Q.length + q) = entry Q 0 q := by
  rw [mTower_entry hk hq]
  show entry (Lift1 (shiftr01 (0 * k) 0 Q) (e * k)) 0 q = entry Q 0 q
  rw [Wset.entry0_Lift1, Nat.zero_mul]
  show entry (shiftr01 0 0 Q) 0 q = entry Q 0 q
  rw [shiftr01_zero]

/-- ★★★★★★ **`d = 0` では `nextrel0` はブロックをまたげません**（`hr0(Q)` だけ）。 -/
theorem no_nextrel0_cross_of_d_zero {Q : TrioSeq} {e n a k' q' : ℕ} (hQ : 0 < Q.length)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hk' : k' < n) (hq' : q' < Q.length) (ha : a < k' * Q.length) :
    ¬ nextrel0 (mTower Q 0 e n) a (k' * Q.length + q') := by
  intro h
  have hlen : (mTower Q 0 e n).length = n * Q.length := mTower_length Q 0 e n
  have halen : a < (mTower Q 0 e n).length := h.1
  -- `a` を「ブロック `ka` の列 `qa`」と書く
  set ka := a / Q.length with hka
  set qa := a % Q.length with hqa
  have haeq : ka * Q.length + qa = a := by
    rw [hka, hqa, Nat.mul_comm]; exact Nat.div_add_mod a Q.length
  have hqalt : qa < Q.length := Nat.mod_lt _ hQ
  have hkalt : ka < n := by
    rw [hlen] at halen
    rw [hka]
    exact (Nat.div_lt_iff_lt_mul hQ).mpr (by omega)
  have hea : entry (mTower Q 0 e n) 0 a = entry Q 0 qa := by
    rw [← haeq]; exact mTower_entry0_of_d_zero hkalt hqalt
  have heb : entry (mTower Q 0 e n) 0 (k' * Q.length + q') = entry Q 0 q' :=
    mTower_entry0_of_d_zero hk' hq'
  have hlt := h.2.2.2.1
  rw [hea, heb] at hlt
  rcases Nat.eq_zero_or_pos q' with hq0 | hq0
  · -- ★ 的がブロックの根 ⟹ `entry Q 0 qa < entry Q 0 0` は `hr0` に反する
    rw [hq0] at hlt
    rcases Nat.eq_zero_or_pos qa with h0 | h0
    · rw [h0] at hlt; omega
    · exact absurd (hr0 qa h0 hqalt) (by omega)
  · -- ★ 的が内部列 ⟹ 最小性を「そのブロックの根」に当てる
    have hroot : entry (mTower Q 0 e n) 0 (k' * Q.length) = entry Q 0 0 := by
      have := mTower_entry0_of_d_zero (Q := Q) (e := e) (n := n) (k := k') (q := 0) hk' hQ
      rwa [Nat.add_zero] at this
    have hmin := h.2.2.2.2 (k' * Q.length) ⟨by omega, by omega⟩
    rw [hroot, heb] at hmin
    exact absurd (hr0 q' hq0 hq') (by omega)

/-! ### 271.1 ⟹ ★★★★★ **これが `d = 0` の保護の正体**です

**⟹ ★ `nextrel0` が越境できない ⟹ ★★ 私の §256（`no_nextR_of_no_le0_cross`）により、
**`nextrel1` も `nextrel2` も越境できません**（どちらも `le0` を含むので）。**
**⟹ ⟹ ★★★ ですから **`d = 0` の塔では、接頭辞がどれだけ浅くても親を供給できません**。**
**⟹ ⟹ ⟹ ★★★★★ ＝ **`PrefixCopies` が `A` に条件を課さなくてよい理由**です。**

**⟹ ⛔ そして **`d > 0` ではこの保護が消えます**（行 0 が `d*k` だけ上がるので越境できる）。**
**⟹ ⟹ ★ ＝ **私の §256/§257 が扱っている場面**そのものです。**

⚠ **教訓 14**: これは **`ZeroDOK` の証明ではありません**。⟹ ★ **`d = 0` の場合の道具**です。
`ZeroDOK` は `A ++ mTower Q 0 0 n ∈ W u` という **`W` の閉包**の主張で、
上は **親の位置**についての主張です。⟹ ⟹ ★ **繋げるには `snoc_orphan_W` が要ります**。 -/

/-! ## 272. ★★★★ **`d = 0` の保護の `le0` 版**（鎖にする）＋ ⚠ **保護の射程の正直な限界**

§271 は 1 歩の話でした。⟹ ★ 鎖にします（`nextrel0` は添字を増やすので、境界を越える最初の 1 歩を捕まえる）。 -/

theorem no_le0_cross_of_d_zero {Q : TrioSeq} {e n a k' q' : ℕ} (hQ : 0 < Q.length)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (ha : a < k' * Q.length) :
    ¬ Relation.ReflTransGen (nextrel0 (mTower Q 0 e n)) a (k' * Q.length + q') := by
  intro h
  -- 鎖の中で「はじめて `k' * |Q|` 以上になる」ノードを捕まえる
  have key : ∀ z, Relation.ReflTransGen (nextrel0 (mTower Q 0 e n)) a z →
      z < k' * Q.length ∨ False := by
    intro z hz
    induction hz with
    | refl => exact Or.inl ha
    | @tail x w hx hxw ih =>
        rcases ih with hxlt | hf
        · rcases Nat.lt_or_ge w (k' * Q.length) with hw | hw
          · exact Or.inl hw
          · -- ★ `w` はブロック `k'` 以降。⟹ `w` の属するブロックを取って §271 に当てる
            exfalso
            have hwlen : w < (mTower Q 0 e n).length := hxw.2.1
            rw [mTower_length] at hwlen
            set kw := w / Q.length with hkw
            set qw := w % Q.length with hqw
            have hweq : kw * Q.length + qw = w := by
              rw [hkw, hqw, Nat.mul_comm]; exact Nat.div_add_mod w Q.length
            have hqwlt : qw < Q.length := Nat.mod_lt _ hQ
            have hkwlt : kw < n := by
              rw [hkw]; exact (Nat.div_lt_iff_lt_mul hQ).mpr (by omega)
            have hkwge : k' ≤ kw := by
              rw [hkw]
              exact (Nat.le_div_iff_mul_le hQ).mpr (by omega)
            have hxlt' : x < kw * Q.length := by
              have : k' * Q.length ≤ kw * Q.length := Nat.mul_le_mul_right _ hkwge
              omega
            refine no_nextrel0_cross_of_d_zero (Q := Q) (e := e) (n := n) (a := x)
              (k' := kw) (q' := qw) hQ hr0 hkwlt hqwlt hxlt' ?_
            rw [hweq]; exact hxw
        · exact Or.inr hf
  rcases key (k' * Q.length + q') h with hlt | hf
  · omega
  · exact hf

/-! ### 272.1 ⚠⚠ **保護の射程の限界**（正直に書きます）

**⟹ ★ §271/§272 は **塔の中どうし**の越境を禁じます（前提は `hr0(Q)` だけ）。**
**⟹ ⛔ ですが **接頭辞 `A` からブロック `k'` の根への越境は禁じません**。⟹ 理由:**

    `A` の列 `c` の行 0 が `entry Q 0 0` より**浅い**とき、
    ⟹ ★ 的 ＝ ブロック `k'` の根（行 0 ＝ `entry Q 0 0`）に対して
    ⟹ ⟹ **最小性は「間の列の行 0 ≥ `entry Q 0 0`」で済み**、`hr0` の下で**すべて成立**
    ⟹ ⟹ ⟹ ⛔ **`nextrel0 c (A.length + k' * |Q|)` が張れてしまいます**

**⟹ ⚠ ですから **`PrefixCopies` の「`A` に条件が要らない」理由は、これだけではありません**。**
**⟹ ★ ⟹ **ブロック根が `A` に親を持ってもよい**——⟹ ★★ そこは `snoc_orphan_W` ではなく
**graft の側**で処理されているはずです。⟹ ⟹ ★ **`W_flatMap_copies`（`A = []` で緑）の証明を読む**必要があります。**

**⟹ ⛔ ですから **(L-ZD)「`prefixCopies_nil` を `A ≠ []` に持ち上げる」は、私の道具では届きません**。**
**⟹ ⟹ ★ 届かない場所を明示します: **ブロック根が接頭辞に親を持つ場合**です。**
**⟹ ⟹ ⟹ ★★ ＝ **今日ずっと問題だった場所と同じ**（`OrphOK0` の反例もその形でした）。**

⚠ **教訓 14**: §271/§272 は緑ですが、**`ZeroDOK` には届きません**。**⟹ 過大に読まないでください。** -/

/-! ## 273. ★★★★★★★ **(L-GEN)**: `snocStep_oper_pre` の「親がどこでも」版

§266 の訂正で「**`hbound` は必要より強い**」と分かりました。⟹ ★ 一般形を書きます。

**⟹ ★ 材料は 2 本とも**一般**です:**

    `Lcone.oper_eq_gexp_gen` … `M⟦n⟧ = gexp M (parent …) (|M|-1-parent …) d0 d1 n`（**親の位置は任意**）
    `L105.gexp_eq_take_append_mTower` … `gexp M j0 Lb d0 d1 n = M.take j0 ++ mTower ((M.drop j0).take Lb) d0 d1 n`

**⟹ ⟹ ★★★ ですから `P ++ B.take (j+1)` の形も `P.length + p` という書き方も、
**もともと本質ではありませんでした**。** -/

open Classical in
theorem snocStep_oper_gen {T : TrioSeq} {c m : ℕ}
    (hL : T.length - 1 ≠ 0)
    (hz : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0 ∧
      entry T 2 (T.length - 1) = 0))
    (hpar : hasParent T (srow T (T.length - 1)) (T.length - 1))
    (hpe : parent T (srow T (T.length - 1)) (T.length - 1) = c) :
    ∃ (V : TrioSeq) (d0 d1 : ℕ), V.length = T.length - 1 - c ∧
      T⟦m⟧ = T.take c ++ mTower V d0 d1 m := by
  have hclt : c < T.length := by
    rw [← hpe]
    exact nextR_index_lt (parent_nextR hpar) |>.trans_le (by omega)
  refine ⟨(T.drop c).take (T.length - 1 - c),
    (if 0 < srow T (T.length - 1) then entry T 0 (T.length - 1) - entry T 0 c else 0),
    (if 1 < srow T (T.length - 1) then entry T 1 (T.length - 1) - entry T 1 c else 0),
    ?_, ?_⟩
  · rw [List.length_take, List.length_drop]; omega
  · rw [oper_eq_gexp_gen m hL hz hpar, hpe,
      gexp_eq_take_append_mTower (show c + (T.length - 1 - c) ≤ T.length from by omega)]

/-! ### 273.1 ⟹ ★★★★★★ **`hbound` を `|V| < |Q|` に置き換えられます**

**⟹ ★ §273 は **親の位置に何も条件を課しません**。⟹ ⟹ ★★ ですから:**

    ⛔ **旧**: `hbound`（`(A ++ mTower).length ≤ parent`）＝ **親が最後のブロックの中**
    ★★★★★ **新**: **`T.length - 1 - c < |Q|`**（＝ **窓が `Q` より短い**）だけ

**⟹ ★★★ そして **後者のほうが真に弱い**です:**

    `hbound` ⟹ `c ≥ |A ++ mTower|` ⟹ `|V| = |A ++ mTower| + j - c ≤ j < |Q|` ✅
    ⟹ ⛔ **逆は言えません**（親が 1 つ前のブロックの末尾にあっても `|V| < |Q|` はありえます）

**⟹ ★★★★★ ⟹ ですから **越境の手も、窓さえ短ければ帰納法に乗ります**。**
**⟹ ⟹ ★ そして **実測では越境 208 件すべてで `|V| < |Q|`** でした（§266 の訂正）。**

⚠ **教訓 14**: §273 は緑ですが、**`|V| < |Q|` はまだ証明していません**（測定 208/208）。
**⟹ ★ 次はそこです。⟹ ⟹ ★★ そして **`towerClosed_of_hered` の配線をやり直す**必要があります。** -/

/-! ## 274. ★★★★★★ **窓が短い理由**: 親は「的より浅い列」より後ろにいます

§273 で残ったのは **`|V| < |Q|`**（＝ 親が末尾 `|Q|` 列の中）です。⟹ ★ その一般的な理由を書きます。

**⟹ ★★★ `nextrel0` の最小性は「間の列は的より浅くない」と言います。**
**⟹ ⟹ ★ ですから **的より真に浅い列 `c` があれば、親は `c` 以降**でなければなりません。** -/

theorem nextrel0_src_ge_of_gap {M : TrioSeq} {y b c : ℕ}
    (hcb : c < b) (hlt : entry M 0 c < entry M 0 b) (h : nextrel0 M y b) : c ≤ y := by
  by_contra hc
  exact absurd (h.2.2.2.2 c ⟨by omega, hcb⟩) (by omega)

/-! ### 274.1 ⟹ ★★★★★ **塔での意味**

塔の中で、的が **ブロック `n` の位置 `j`**（行 0 ＝ `entry Q 0 j + d·n`）のとき、
**ブロック `n-1` の同じ位置 `j`**（行 0 ＝ `entry Q 0 j + d·(n-1)`）は、⟹ ★ **`0 < d` なら真に浅い**。

**⟹ ★★★★★ ですから §274 より **行 0 の親は「1 つ前のブロックの同じ位置」以降**にいます。**
**⟹ ⟹ ★★★ ＝ **`|V| ≤ |Q|`**（窓は高々 `Q` の長さ）。**

**⟹ ⚠ ただし これは **`srow = 0`（行 0 の親）**のときだけです。**
**⟹ ⟹ ★ `nextrel1` / `nextrel2` は最小性が `le0` / `le1` 祖先の上なので、⟹ ⛔ **同じ議論は通りません**。**
**⟹ ⟹ ⟹ ★★ ですが **`nextrel1` も `nextrel2` も `le0 M y b` を含みます**（§256）。**
**⟹ ⟹ ⟹ ⟹ ★★★ そして **`le0` の鎖の最後の 1 歩は `nextrel0`** なので、⟹ ★ **その始点は `c` 以降**。**
**⟹ ⟹ ⟹ ⟹ ⟹ ⚠ **ですが `y` 自身が `c` 以降とは限りません**（鎖はもっと手前から来られます）。**

**⟹ ★ ですから **行 1・行 2 は別の議論が要ります**。⟹ ⟹ **実測は 208/208 で `|V| < |Q|`** でした。**

⚠ **教訓 14**: §274 は緑ですが、**`|V| < |Q|` の証明ではありません**（行 0 だけ、しかも `≤`）。 -/

/-- ★★★ **`le0` の鎖の最後の 1 歩**（`nextrel0`）の始点も `c` 以降。 -/
theorem rtg0_last_step_ge_of_gap {M : TrioSeq} {a b c : ℕ}
    (hcb : c < b) (hlt : entry M 0 c < entry M 0 b) (hab : a < b)
    (h : Relation.ReflTransGen (nextrel0 M) a b) :
    ∃ x, c ≤ x ∧ x < b ∧ Relation.ReflTransGen (nextrel0 M) a x ∧ nextrel0 M x b := by
  rcases Relation.ReflTransGen.cases_tail h with h0 | ⟨x, hax, hxb⟩
  · omega
  · exact ⟨x, nextrel0_src_ge_of_gap hcb hlt hxb, hxb.2.2.1, hax, hxb⟩

/-! ## 275. ★★★★★★★★ **一般の snoc 段**: 親の位置で場合分けしません

§273 を**明示形**にしてから組みます。⟹ ★ **`hbound` も孤児の枝も要りません**。

**⟹ ★★★ 骨: `T⟦m⟧ = T.take c ++ mTower V d0 d1 m`（`V = (T.drop c).take (|T|-1-c)`）で、**

    `T.take c ∈ W u` ……………… ★ `T.dropLast ∈ W u` の接頭辞（`Wset.W_take`）
    `T.take c ++ V = T.dropLast` … ★ **`List.take_add` でぴったり**
    ⟹ ⟹ ★★★★ ですから `hIH` が **そのまま** `T⟦m⟧ ∈ W u` を与え、`mem_of_oper_mem` で `T ∈ W u`

**⟹ ★★★★★ **義務は 2 つだけ**: **`TowerP'' V d0 d1`** と **測度の減少**。**
**⟹ ⟹ ★ ＝ 今までの「良い手」と同じ 2 つ。⟹ ⟹ ★★ **越境の手も同じ枠に入ります**。** -/

open Classical in
/-- ★★★★★★ §273 の**明示形**（`V` と `d0`/`d1` を具体的に書いたもの）。 -/
theorem snocStep_oper_gen_eq {T : TrioSeq} {c : ℕ} (m : ℕ)
    (hL : T.length - 1 ≠ 0)
    (hz : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0 ∧
      entry T 2 (T.length - 1) = 0))
    (hpar : hasParent T (srow T (T.length - 1)) (T.length - 1))
    (hpe : parent T (srow T (T.length - 1)) (T.length - 1) = c) :
    T⟦m⟧ = T.take c ++ mTower ((T.drop c).take (T.length - 1 - c))
      (if 0 < srow T (T.length - 1) then entry T 0 (T.length - 1) - entry T 0 c else 0)
      (if 1 < srow T (T.length - 1) then entry T 1 (T.length - 1) - entry T 1 c else 0) m := by
  rw [oper_eq_gexp_gen m hL hz hpar, hpe,
    gexp_eq_take_append_mTower (show c + (T.length - 1 - c) ≤ T.length from by
      have hclt : c < T.length := by
        rw [← hpe]
        exact (nextR_index_lt (parent_nextR hpar)).trans_le (by omega)
      omega)]

/-- ★★ `T.take c ++ 窓 = T.dropLast`（`List.take_add`）。 -/
theorem take_append_window {T : TrioSeq} {c : ℕ} (hc : c ≤ T.length - 1) :
    T.take c ++ (T.drop c).take (T.length - 1 - c) = T.dropLast := by
  rw [List.dropLast_eq_take, ← List.take_append_drop c (T.take (T.length - 1))]
  congr 1
  · rw [List.take_take, Nat.min_eq_left (by omega)]
  · rw [List.drop_take]

open Classical in
/-- ★★★★★★★★ **一般の snoc 段**: 親の位置に条件なし。義務は `TowerP''` と測度だけ。 -/
theorem hsnoc_gen {u : ℕ} {Q T : TrioSeq} {d e c : ℕ}
    {P : TrioSeq → ℕ → ℕ → Prop}
    (hIH : ∀ V d0 d1, P V d0 d1 → towerMeas V d0 d1 < towerMeas Q d e →
      ∀ A', A' ∈ W u → A' ++ V ∈ W u → ∀ m, A' ++ mTower V d0 d1 m ∈ W u)
    (hL : T.length - 1 ≠ 0)
    (hz : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0 ∧
      entry T 2 (T.length - 1) = 0))
    (hpar : hasParent T (srow T (T.length - 1)) (T.length - 1))
    (hpe : parent T (srow T (T.length - 1)) (T.length - 1) = c)
    (hpre : T.dropLast ∈ W u)
    (hPV : P ((T.drop c).take (T.length - 1 - c))
      (if 0 < srow T (T.length - 1) then entry T 0 (T.length - 1) - entry T 0 c else 0)
      (if 1 < srow T (T.length - 1) then entry T 1 (T.length - 1) - entry T 1 c else 0))
    (hmeas : towerMeas ((T.drop c).take (T.length - 1 - c))
        (if 0 < srow T (T.length - 1) then entry T 0 (T.length - 1) - entry T 0 c else 0)
        (if 1 < srow T (T.length - 1) then entry T 1 (T.length - 1) - entry T 1 c else 0)
      < towerMeas Q d e) :
    T ∈ W u := by
  have hclt : c < T.length := by
    rw [← hpe]
    exact (nextR_index_lt (parent_nextR hpar)).trans_le (by omega)
  have hc1 : c ≤ T.length - 1 := by omega
  have hTc : T.take c ∈ W u := by
    have := Wset.W_take (u := u) (M := T.dropLast) hpre c
    rwa [List.dropLast_eq_take, List.take_take, Nat.min_eq_left (by omega)] at this
  have hcat : T.take c ++ (T.drop c).take (T.length - 1 - c) ∈ W u := by
    rw [take_append_window hc1]; exact hpre
  refine mem_of_oper_mem ?_
  intro m _
  rw [snocStep_oper_gen_eq m hL hz hpar hpe]
  exact hIH _ _ _ hPV hmeas (T.take c) hTc hcat m

/-! ### 275.1 ⟹ ★★★★★★★★ **設計が 1 本になりました**

    ⛔ **旧**: `hbound`（親が最後のブロックの中）＋ **孤児の枝**（`OrphOK` / `OrphOK0`、**偽**）
    ★★★★★ **新**: **`hsnoc_gen` 1 本**。義務は **`TowerP''` の遺伝**と **測度の減少**だけ

**⟹ ★★★ **`OrphOK` も `OrphOK0` も `hbound` も要りません**。⟹ ⟹ ★ **偽の残差が 2 本消えます**。**

**⟹ ⚠ 残る義務（どちらも未証明）:**

    ⛔ **(O-A) `TowerP''` が窓 `(T.drop c).take (|T|-1-c)` に遺伝する**
       ⟹ ★ `hr0` は §221（`hr0_wnd`）の一般化で出るはず（`window_of_rtg0` は親の位置に依らない）
       ⟹ ⚠ `hz0` は **§263 で偽**（`HeredZ0`）⟹ ⛔ **ここが残ります**
    ⛔ **(O-B) `|V| < |Q|`**（測度の減少）⟹ ★ 実測 208/208、⟹ ⚠ **未証明**

⚠ **教訓 14**: §275 は緑ですが、**2 つの義務は未証明**です。⟹ **「閉じた」ではありません**。 -/

/-! ## 276. ★★★★★ **(O-A) の 1/3**: `hr0` は窓に遺伝します（**親の位置に依らない**）

§221 の `hr0_wnd` は `P.length + p` の形で書いていましたが、⟹ ★ 中身は
**`le0 T (親) (末尾)` ＋ `Lcone.window_of_rtg0` ＋ `L105.window_root_shallow`** だけです。
**⟹ ⟹ ★★★ ですから **親がどこにいても同じ**です。** -/

open Classical in
theorem hr0_wnd_gen {T : TrioSeq} {c : ℕ}
    (hpar : hasParent T (srow T (T.length - 1)) (T.length - 1))
    (hpe : parent T (srow T (T.length - 1)) (T.length - 1) = c) :
    ∀ l, 0 < l → l < ((T.drop c).take (T.length - 1 - c)).length →
      entry ((T.drop c).take (T.length - 1 - c)) 0 0
        < entry ((T.drop c).take (T.length - 1 - c)) 0 l := by
  have hle0 : le0 T c (T.length - 1) := by
    have h := nextR_le0 (parent_nextR hpar)
    rw [hpe] at h; exact h
  have hclt : c < T.length := hle0.1
  have hlast : T.length - 1 < T.length := by
    have := hle0.2.1; omega
  refine window_root_shallow (M := T) (j0 := c) (Lb := T.length - 1 - c)
    (by omega) ?_
  intro l hl0 hl1
  exact window_of_rtg0 hle0.2.2 (by omega) l hl0 (by omega)

/-! ### 276.1 ⟹ ★ **(O-A) の残り**

    ✅ **`hr0`** …… §276（**親の位置に依らない**、緑）
    ✅ **`hz1`** …… `entry` は窓で不変（`Wset.entry_take` ＋ `entry_drop`）
    ⛔ **`hz0`** …… **§263 で偽**（`HeredZ0`）⟹ ★ **ここだけが残ります**
    ⛔ **`(d = 0 → e = 0)`** … §233 の一般化が要ります

**⟹ ★★ ですから **(O-A) の本当の穴は `hz0` 1 つ**です。**
**⟹ ⟹ ★ そして `hz0` は **§240.1 / §255 / §258 で使っています**（行 2 の証人の底）。**
**⟹ ⟹ ⟹ ⚠ ですから **`hz0` を落とすと行 2 の議論が全部壊れます**。⟹ ★ **そこが次の設計課題**です。** -/

/-! ## 277. ★★★★★★★★★ **新しい骨格**: 不変量は `hr0` だけ、義務は測度だけ

§275（`hsnoc_gen`）と §276（`hr0` の遺伝）で、⟹ ★ **不変量から `hz0` / `hz1` / `(d=0→e=0)` が
落とせるかもしれません**。⟹ ⟹ ★★ **`hsnoc_gen` はそれらを使わない**からです。 -/

/-- ★★★ **新しい不変量**: `0 < |Q|` と `hr0` だけ。 -/
def TowerR (Q : TrioSeq) (_d _e : ℕ) : Prop :=
  0 < Q.length ∧ (∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)

open Classical in
/-- ⛔ **残る唯一の義務（旧・強すぎる形）**: 窓が `Q` より短い。
⚠ **§277.6 で偽と証明済み**。⟹ ★ 本当に要るのは §277.8 の `MeasOK2`（測度そのもの）です。 -/
def MeasOK : Prop :=
  ∀ (A Q : TrioSeq) (d e n j : ℕ), 0 < Q.length → j < Q.length →
    hasParent (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (srow (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        ((A ++ mTower Q d e n
          ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1))
      ((A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1) →
    (A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1
      - parent (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
          (srow (A ++ mTower Q d e n
            ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
            ((A ++ mTower Q d e n
              ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1))
          ((A ++ mTower Q d e n
            ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1)
      < Q.length

open Classical in
/-- ★★★★★ **本当の義務（§277.8）**: 窓の**測度**が減る。⟹ `|V| < |Q|` はその十分条件。 -/
def MeasOK2 : Prop :=
  ∀ (T Q : TrioSeq) (d e : ℕ),
    hasParent T (srow T (T.length - 1)) (T.length - 1) →
    towerMeas ((T.drop (parent T (srow T (T.length - 1)) (T.length - 1))).take
        (T.length - 1 - parent T (srow T (T.length - 1)) (T.length - 1)))
      (if 0 < srow T (T.length - 1) then entry T 0 (T.length - 1)
        - entry T 0 (parent T (srow T (T.length - 1)) (T.length - 1)) else 0)
      (if 1 < srow T (T.length - 1) then entry T 1 (T.length - 1)
        - entry T 1 (parent T (srow T (T.length - 1)) (T.length - 1)) else 0)
      < towerMeas Q d e

/-! ### 277.1 ⟹ ★ **1 段の snoc**（`MeasOK` を仮定して） -/

open Classical in
theorem snocStep_gen {u : ℕ} {A Q : TrioSeq} {d e n j : ℕ}
    (hmeas : MeasOK2) (hj : j < Q.length)
    (hIH : ∀ V d0 d1, TowerR V d0 d1 → towerMeas V d0 d1 < towerMeas Q d e →
      ∀ A', A' ∈ W u → A' ++ V ∈ W u → ∀ m, A' ++ mTower V d0 d1 m ∈ W u)
    (hne : (A ++ mTower Q d e n
      ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j) ≠ [])
    (hall : ∀ j', j' ≤ j →
      A ++ mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j' ∈ W u) :
    A ++ mTower Q d e n
      ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1) ∈ W u := by
  set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
  set T := A ++ mTower Q d e n ++ B.take (j + 1) with hT
  have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
  have hBt : B.take (j + 1) = B.take j ++ [B.getD j (0, 0, 0)] := by
    rw [List.take_add_one]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have hsp : T = (A ++ mTower Q d e n ++ B.take j) ++ [B.getD j (0, 0, 0)] := by
    rw [hT, hBt, ← List.append_assoc]
  have hdl : T.dropLast = A ++ mTower Q d e n ++ B.take j := by
    rw [hsp, List.dropLast_concat]
  have hpre : T.dropLast ∈ W u := by rw [hdl]; exact hall j (le_refl j)
  have hprelen : 0 < (A ++ mTower Q d e n ++ B.take j).length :=
    List.length_pos_iff.mpr hne
  have hlen1 : T.length - 1 ≠ 0 := by
    rw [hsp, List.length_append, List.length_singleton]; omega
  by_cases hz : entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0 ∧
      entry T 2 (T.length - 1) = 0
  · -- ★ 末尾が全部 0 ⟹ `oper` は `Pred` ⟹ 接頭辞そのもの
    refine mem_of_oper_mem ?_
    intro m _
    unfold oper
    rw [if_neg hlen1, if_pos hz]
    unfold Pred
    rw [if_neg (by omega)]
    exact hpre
  · by_cases hpar : hasParent T (srow T (T.length - 1)) (T.length - 1)
    · -- ★ 親がある ⟹ §275
      refine hsnoc_gen (Q := Q) (T := T) (d := d) (e := e)
        (c := parent T (srow T (T.length - 1)) (T.length - 1))
        (fun V d0 d1 hPV hlt A' hA' hAV m => hIH V d0 d1 hPV hlt A' hA' hAV m)
        hlen1 hz hpar rfl hpre ?_ ?_
      · -- `TowerR` の遺伝
        refine ⟨?_, hr0_wnd_gen hpar rfl⟩
        rw [List.length_take, List.length_drop]
        have hlt := nextR_index_lt (parent_nextR hpar)
        omega
      · -- 測度の減少
        exact hmeas T Q d e hpar
    · -- ★ 孤児 ⟹ `snoc_orphan_W`
      rw [hsp]
      refine snoc_orphan_W _ (by rw [← hdl]; exact hpre) hne ?_
      have hlen : (A ++ mTower Q d e n ++ B.take j).length = T.length - 1 := by
        conv_rhs => rw [hsp]
        rw [List.length_append]
        simp
        omega
      rw [hlen, ← hsp]
      exact hpar

/-! ### 277.2 ⟹ ★★★★★★★★ **新しい骨格** -/

open Classical in
theorem towerClosed_gen {u : ℕ} (hmeas : MeasOK2) :
    ∀ Q d e, TowerR Q d e → ∀ A, A ∈ W u → A ++ Q ∈ W u →
      ∀ n, A ++ mTower Q d e n ∈ W u := by
  refine tower_of_measure_step2 (u := u) TowerR towerMeas ?_
  intro Q d e hP hIH A hA hAQ
  refine prefixTowerClosed_of_snocStepStrong1 hA hAQ ?_
  intro n j hn hj hall
  refine snocStep_gen (u := u) hmeas hj hIH ?_ hall
  intro hc
  have : (A ++ mTower Q d e n
      ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length = 0 := by rw [hc]; rfl
  rw [List.length_append, List.length_append, mTower_length] at this
  have : 0 < n * Q.length := Nat.mul_pos (by omega) hP.1
  omega

/-! ### 277.3 ⟹ ★★★★★★★★★ **残差が 1 本になりました**

    ⛔ **`MeasOK`**（窓が `Q` より短い）——**それだけ**

**⟹ ★ 消えたもの: `OrphOK` / `OrphOK0` / `HeredZ0` / `HeredNB` / `RootNB` / `ZeroDOK` /
`RootZ1` / `RootZ2` / `(d = 0 → e = 0)`。⟹ ⟹ ★★★ **全部要りません**。**

**⟹ ⚠ そして `MeasOK` は **今日はじめて「偽と分かっていない」新しい残差**です。**
**⟹ ⟹ ★ 実測 **208/208**（`|Q| ≤ 5`、`n ≤ 2`）⟹ ⚠ **箱が小さい**。**
**⟹ ⟹ ⟹ ★★ §274 が **行 0 の場合の理由**を与えます（1 つ前のブロックの同位置が真に浅い）。**

⚠ **教訓 14**: `MeasOK` は**未証明**です。⟹ ★ **偽かもしれません**。⟹ **大きい箱で測ってください**。 -/

/-! ### 277.4 ★★★★★★★★★★ **`MTowerClosedS` は `MeasOK` 1 本から出ます**

`z < 2` の制限すら要りません（`RootZ1` / `RootZ2` が消えたので）。 -/

open Classical in
theorem mTowerClosedS_of_measOK (hmeas : MeasOK2) : MTowerClosedS := by
  intro u d e n Q hQ hs
  rcases Nat.eq_zero_or_pos Q.length with h0 | hpos
  · have hnil : Q = [] := List.eq_nil_of_length_eq_zero h0
    subst hnil
    rw [mTower_nil]
    exact W_nil u
  · have h := towerClosed_gen (u := u) hmeas Q d e
      ⟨hpos, fun l hl0 hl1 => hs l hl0 hl1⟩ [] (W_nil u) (by simpa using hQ) n
    simpa using h

/-! ### 277.5 ⟹ ★★★★★★★★★★ **今日の到達点**

    ⛔ **残差は `MeasOK` 1 本だけ**です（`z < 2` の制限も要りません）

**⟹ ★ 消えたもの（今朝は 6 本、途中で 7 本まで増えたもの）:**

    `HeredNB` ／ `RootNB` ／ `RootZ1` ／ `RootZ2` ／ `OrphOK` ／ `OrphOK0` ／
    `HeredZ0` ／ `ZeroDOK` ／ `(d = 0 → e = 0)` ⟹ **全部不要**

**⟹ ★★★ 理由は 1 つ: **`hbound`（親が最後のブロックの中）が本質ではなかった**からです。**
**⟹ ⟹ ★ `snocStep_oper_pre` の型に書いてあった `P.length + p` を、⟹ ⛔ 私が「本質」と読み、**
**⟹ ⟹ ⟹ ⛔⛔ **その周りに 6 本の（偽の）残差を積んでいました**。**

**⟹ ⚠ そして `MeasOK` は **未証明**です。⟹ ★ **偽かもしれません**。**

    ★ 実測 **208/208**（`|Q| ≤ 5`、`n ≤ 2`、`d ≤ 2`、`e ≤ 1`）
    ★ §274 が **行 0 の場合の理由**（1 つ前のブロックの同位置が `0 < d` で真に浅い）
    ⛔ **行 1・行 2 は未解決**（最小性が `le0` / `le1` 祖先の上なので）

⚠ **教訓 14**: **`MeasOK` が偽なら、この骨格も倒れます**。⟹ ★ **大きい箱で測ってください**。 -/

/-! ### 277.6 ⛔⛔⛔⛔ **`MeasOK` も偽です** —— §262 の反例がそのまま効きます

⚠ **30 分前に「今日はじめて偽と分かっていない残差」と書きました。⟹ ⛔ 誤りでした。**
**⟹ ★ **自分の §262 の反例を当てるのを忘れていました**（運用「既知の反例を新しい残差に当てる」）。**

    `A = [(0,0,0)]`、`Q = [(2,1,0),(3,0,0)]`、`d = 1`、`e = 0`、`n = 1`、`j = 0`
    ⟹ `T = [(0,0,0), (2,1,0), (3,0,0), (3,1,0)]`（＝ §262 の `M0ce`）
    ⟹ `|T| - 1 = 3`、`srow = 1`、**親 = 0**（接頭辞の中）
    ⟹ ⛔ `|V| = 3 - 0 = 3`、`|Q| = 2` ⟹ **`3 < 2` は偽** -/

theorem measOK_false : ¬ MeasOK := by
  intro h
  have hblk : (Lift1 (shiftr01 (1 * 1) 0 Q0ce) (0 * 1)).take (0 + 1)
      = [((3 : ℕ), (1 : ℕ), (0 : ℕ))] := by
    show (Lift1 (shiftr01 1 0 Q0ce) 0).take 1 = _
    rw [Wset.Lift1_zero]; unfold Q0ce shiftr01; rfl
  have htow : mTower Q0ce 1 0 1 = Q0ce := by
    unfold mTower
    show ((List.range 1).flatMap fun k => Lift1 (shiftr01 (1 * k) 0 Q0ce) (0 * k)) = Q0ce
    simp
  have hT : [((0 : ℕ), (0 : ℕ), (0 : ℕ))] ++ mTower Q0ce 1 0 1
      ++ (Lift1 (shiftr01 (1 * 1) 0 Q0ce) (0 * 1)).take (0 + 1) = M0ce := by
    rw [htow, hblk]; unfold Q0ce M0ce; rfl
  have hlen : M0ce.length - 1 = 3 := rfl
  have hsr : srow M0ce 3 = 1 := by decide
  have hres := h [((0 : ℕ), (0 : ℕ), (0 : ℕ))] Q0ce 1 0 1 0 (by decide) (by decide) ?_
  · rw [hT, hlen, hsr] at hres
    rw [show parent M0ce 1 3 = 0 from
      M0ce_uniq (nextR_one_iff.mp (parent_nextR M0ce_hasParent))] at hres
    have : Q0ce.length = 2 := rfl
    omega
  · rw [hT, hlen, hsr]; exact M0ce_hasParent

/-! ### 277.7 ⟹ ★★★★ **ですが骨格は生きています** —— 要るのは**弱い**測度条件です

**⟹ ⛔ `MeasOK`（`|V| < |Q|`）は偽。⟹ ★ ですが **`towerClosed_gen` が本当に要るのは
`towerMeas V d0 d1 < towerMeas Q d e`** であって、⟹ ★★ **`|V| < |Q|` はその十分条件**でした。**

**⟹ ⚠ そして `natMeasure w r = 3w + r`（`r ≤ 2`）なので、⟹ ⛔ **`|V| ≥ |Q|` なら測度は減りません**。**
**⟹ ⟹ ★★★ ですから **測度そのものを変えるしかありません**（team-lead の (M2)）。**

**⟹ ★ ただし **骨格（§275 / §277）は測度に依りません**:**

    `tower_of_measure_step2` は **任意の `meas : TrioSeq → ℕ → ℕ → ℕ`** で動きます
    ⟹ ★★ ですから **`towerMeas` を差し替えるだけ**で、⟹ ★ **§277 の証明はそのまま通ります**

**⟹ ★★★★ ⟹ ですから **今日の成果は「残差が `測度の減少` 1 本になった」**ことです。**
**⟹ ⟹ ★ ＝ **R2 の (MEAS) が、はじめて正しい問い**になりました。**

⚠ **教訓 14 ＋ 新運用**: **新しい残差を書いたら、その日の反例を全部当てる**。
**⟹ ⛔ 今日 2 回目の同じ失敗です**（`RootZ1` のときも H12 の反例を当てていませんでした）。 -/

/-! ## 278. ⛔⛔⛔⛔⛔ **`MeasOK2` も偽です** —— そして**原因が最終的に確定**しました

§277.8 で `MeasOK` を測度そのもの（`MeasOK2`）に直しました。⟹ ⛔ **それも偽**です。
**⟹ ★ 同じ `M0ce`（§262 の反例）で落ちます:**

    `T = M0ce = [(0,0,0), (2,1,0), (3,0,0), (3,1,0)]`、`Q = Q0ce = [(2,1,0), (3,0,0)]`、`d = 1`、`e = 0`
    ⟹ 親 = 0 ⟹ `V = M0ce.take 3`（`|V| = 3`）、`d0 = 3 - 0 = 3`、`d1 = 0`
    ⟹ `towerMeas V 3 0 = 3·3 + rankDE 3 0 = 10`
    ⟹ `towerMeas Q 1 0 = 3·2 + rankDE 1 0 = 7`
    ⟹ ⛔ **`10 < 7` は偽** -/

theorem measOK2_false : ¬ MeasOK2 := by
  intro h
  have hsr : srow M0ce 3 = 1 := by decide
  have hlen : M0ce.length - 1 = 3 := rfl
  have hpar : hasParent M0ce (srow M0ce (M0ce.length - 1)) (M0ce.length - 1) := by
    rw [hlen, hsr]; exact M0ce_hasParent
  have hc : parent M0ce 1 3 = 0 :=
    M0ce_uniq (nextR_one_iff.mp (parent_nextR M0ce_hasParent))
  have hres := h M0ce Q0ce 1 0 hpar
  rw [hlen, hsr, hc] at hres
  have hV : (M0ce.drop 0).take (3 - 0) = [((0 : ℕ), (0 : ℕ), (0 : ℕ)), (2, 1, 0), (3, 0, 0)] := by
    unfold M0ce; rfl
  rw [hV] at hres
  have h1 : towerMeas [((0 : ℕ), (0 : ℕ), (0 : ℕ)), (2, 1, 0), (3, 0, 0)]
      (if (0 : ℕ) < 1 then entry M0ce 0 3 - entry M0ce 0 0 else 0)
      (if (1 : ℕ) < 1 then entry M0ce 1 3 - entry M0ce 1 0 else 0) = 10 := by decide
  have h2 : towerMeas Q0ce 1 0 = 7 := by decide
  rw [h1, h2] at hres
  omega

/-! ### 278.1 ⛔⛔⛔⛔⛔⛔ **原因の確定: `rsum` は 1 段で必ず壊れます**

私の実測（`hr0(Q)` 真、`(d = 0 → e = 0)` を課したもの）:

| `d` | `A = []` | `A ≠ []` |
|---|---|---|
| `d = 0` | ★ **破れ 0**（164 件） | ⛔ **破れ 1,080 / 1,736** |
| `d = 1` | ★ **破れ 0**（580 件） | ⛔ **破れ 1,572 / 3,892** |
| `d = 2` | ★ **破れ 0**（672 件） | ⛔ **破れ 1,240 / 3,928** |

**⟹ ★★★★★ **`A = []` なら 1,416 / 1,416 で成立、`A ≠ []` なら 39% 破れる**。**
**⟹ ⟹ ★ `d` で場合分けしても**変わりません**。⟹ ⛔ **`d = 0` の枝を戻しても直りません**。**

**⟹ ★★★★★★★ そして **なぜ 1 段で壊れるか**が言えます:**

    ★ 段 0 では `A = []` ⟹ **`rsum [] Q` は `hr0` から真** ✅
    ★★ 段 1 では **`A' = A ++ mTower Q d e n ++ B.take p`**
      ⟹ ★ そこには **ブロック 0 の根**（行 0 ＝ `entry Q 0 0`）が入っています
      ⟹ ⟹ ★★ 一方 **窓 `V` の根**は行 0 ＝ `entry Q 0 p + d·n`
      ⟹ ⟹ ⟹ ★★★ **`0 < d` かつ `0 < n` なら、ブロック 0 の根のほうが真に浅い**
      ⟹ ⟹ ⟹ ⟹ ⛔ **`rsum A' V` は偽** ⟹ **段 1 で必ず壊れます**

**⟹ ★★★★★★ ⟹ **今日死んだ 10 本すべてが、この 1 つの構造**です:**

    `hbase` ／ `rsum` ／ `h1out` ／ `hnbQ` ／ `HeredNB` ／ `RootZ1` ／ `RootZ2` ／
    `OrphOK` ／ `OrphOK0` ／ `HeredZ0` ／ `MeasOK` ／ `MeasOK2`

**⟹ ★ 全部 **「接頭辞が今の `Q` の根より浅くなりうる」**で死んでいます。**
**⟹ ⟹ ★★★ そして **それは塔を作った瞬間に必ず起きます**（前のブロックが残るから）。**

⚠ **教訓 14**: これは **`MTowerClosedS` が偽**という意味ではありません。
**⟹ ★ **この帰納法（窓に落として測度を減らす）が通らない**、という意味です。

### ⚠⚠ 278.2 **R2 の「破れは `j = 0` だけ」との食い違い** —— **正規化の罠、今日 3 回目**

R2: 「**`j ≥ 1` は 1,396,800 件で 100%**、破れは `j = 0` の 57,375 件だけ。**`A` は影響しない**（96.3430% / 96.3430%）」。

**⟹ ⛔ 私の実測は逆です**（`Q` の根の行 0 ＝ **2**、`(d = 0 → e = 0)` を課す）:

| | `d = 0` | `d = 1` | `d = 2` |
|---|---|---|---|
| **`j = 0`** | ⛔ 破れ 420 | ⛔ 破れ 420 / 1,428 | ⛔ 破れ 260 / 1,508 |
| **`j ≥ 1`** | ⛔ 破れ 344 / 1,000 | ⛔ 破れ 688 / 2,000 | ⛔ 破れ 608 / 2,048 |

**⟹ ★ そして **破れは全部 `A ≠ []`**（`A = []` では 1,416 / 1,416 で成立）。**

**⟹ ★★★★★ **食い違いの原因は、たぶん正規化**です:**

    ★ R2 の `Q` はシート由来 ⟹ **根の行 0 が 0**（`entry Q 0 0 = 0`）
    ⟹ ★★ すると `A` の列は行 0 ≥ 0 ＝ `entry Q 0 0` ⟹ **`rsum A Q` が自動で成立**
    ⟹ ⟹ ⛔ **接頭辞が浅くなれません** ⟹ **破れが見えません**
    ★ 私の `Q` は **根の行 0 ＝ 2** ⟹ `A = [(0,0,0)]` が **真に浅い** ⟹ **破れます**

**⟹ ⚠⚠ **今日 3 回目の正規化の罠**です（(W15) ／ `OrphOK0` の 0/624 ／ ここ）。**
**⟹ ★ ⟹ R2 に **`entry Q 0 0 > 0` の `Q`（窓由来）で測り直す**よう伝えてください。**

### ⛔⛔ 278.3 **`j ≥ 1` でも破れます** —— R2 の「160,020 / 160,020」への反例

R2:「**`A` が浅い ∧ `j ≥ 1` なら測度は 100% 減る（160,020 件、破れ 0）**」。
**⟹ ⛔ 私の箱では **`j ≥ 1` の破れが 1,296 件**あります。⟹ ★ **最小の例**:**

```
Q = [(2,1,0), (3,1,0)]、d = 1、e = 0、n = 1、**j = 1**、A = [(0,0,0)]
⟹ T = [(0,0,0), (2,1,0), (3,1,0), (3,1,0), (4,1,0)]、idx = 4、srow = 1
⟹ **親 = 0（接頭辞の中）** ⟹ |V| = 4、|Q| = 2、d0 = 4、d1 = 0
⟹ ⛔ meas 13 vs 7 ⟹ **減りません**
```

**⟹ ★ `Q` の**行 1 が全部 1**（`e = 0` なので塔でも変わらない）⟹ ★★ **塔の中に候補が無い**。**
**⟹ ⟹ ★★★ そして 接頭辞の `(0,0,0)` は行 1 = 0 < 1 ⟹ **唯一の候補** ⟹ **親になります**。**

**⟹ ⛔⛔ ですから **`j = 0` に限った話ではありません**。⟹ ★ **`A` が浅いことが唯一の原因**です。**
**⟹ ⟹ ⚠ R2 の箱には **「行 1 が全部等しい `Q`」が無い**のだと思います（`hnz` 的な形）。**

### ⛔⛔ 278.4 **`NoOrph`（行 1 の孤児が無い）も遺伝しません** —— そして**私も箱の罠にかかりました**

H12 の (W38) の答えとして「`NoOrph Q :⟺ ∀ j, 0 < entry Q 1 j → amin Q j < entry Q 1 j` を
測り直す価値があるかも」と書きました。⟹ ★ **測りました**。

    ⛔ **小さい箱**（`|Q| ≤ 3`、`n ≤ 2`、根の行 0 ∈ {0, 2}、`A` 4 種）
      ⟹ **`NoOrph(Q) → NoOrph(V)` が 4,116 / 4,116（100.0000%）**
      ⟹ ★ 対照も通る（`NoOrph(Q)` 偽の群では `NoOrph(V)` 偽が 1,564 件）
    ⛔⛔ **シートのバッドルート窓**（分母 **5,512**）
      ⟹ **破れ 262（4.7533%）** ⟹ ★★ **遺伝しません**

**⟹ ⚠⚠ **私も今日 5 回目の罠にかかりました**（小さい箱の 100%）。⟹ ★ **シートで裏を取って助かりました**。**

**⟹ ★ 反例（シート由来）:**

```
B = [(0,0,0),(1,0,0),(2,1,0),(3,2,0),(4,1,0),(3,2,0)]、p = 2、j = 5
⟹ V = [(2,1,0), (3,2,0), (4,1,0)]
⟹ ⛔ `V` の列 2（行 1 = 1）は **`V` の中で行 1 の孤児**（候補は行 1 = 1, 2 で どちらも小さくない）
⟹ ★ ですが `B` の中では **添字 1 の `(1,0,0)`（行 1 = 0）** が証人 ⟹ **窓の根 2 より手前**
```

**⟹ ★★★ **今朝の `hlocQ` とまったく同じ機構**です（証人が窓の外に落ちる）。**
**⟹ ⟹ ⛔ ですから **`NoOrph` も不変量として運べません**。⟹ ★ **H12 の穴は埋まりません**。** -/

/-! ## 279. ★★★★★★★★ **(L-A) の答え ＋ `A` を含む測度への一般化**

**(L-A) の答え（1 行）: 帰納法は `A` について **`A ∈ W u` と `A ++ Q ∈ W u` の 2 つ**を持っています。**
**⟹ ★ ですが `tower_of_measure_step2` の `meas` は **`(Q, d, e)` しか見ません**。**
**⟹ ⟹ ★★★ ですから **`meas` を `(A, Q, d, e)` に一般化**します。⟹ ★ **証明の骨は同じ**です。** -/

theorem tower_of_measure_step3 {u : ℕ}
    (P : TrioSeq → ℕ → ℕ → Prop) (meas : TrioSeq → TrioSeq → ℕ → ℕ → ℕ)
    (hstep : ∀ A Q d e, P Q d e → A ∈ W u → A ++ Q ∈ W u →
      (∀ A' V d0 d1, P V d0 d1 → meas A' V d0 d1 < meas A Q d e →
        A' ∈ W u → A' ++ V ∈ W u → ∀ m, A' ++ mTower V d0 d1 m ∈ W u) →
      ∀ n, A ++ mTower Q d e n ∈ W u) :
    ∀ A Q d e, P Q d e → A ∈ W u → A ++ Q ∈ W u →
      ∀ n, A ++ mTower Q d e n ∈ W u := by
  have key : ∀ s A Q d e, meas A Q d e ≤ s → P Q d e → A ∈ W u → A ++ Q ∈ W u →
      ∀ n, A ++ mTower Q d e n ∈ W u := by
    intro s
    induction s with
    | zero =>
      intro A Q d e hle hP hA hAQ n
      exact hstep A Q d e hP hA hAQ
        (fun _ _ _ _ _ hlt _ _ _ => absurd hlt (by omega)) n
    | succ s ih =>
      intro A Q d e hle hP hA hAQ n
      exact hstep A Q d e hP hA hAQ
        (fun A' V d0 d1 hPV hlt hA' hAV m =>
          ih A' V d0 d1 (by omega) hPV hA' hAV m) n
  intro A Q d e hP hA hAQ n
  exact key (meas A Q d e) A Q d e (le_refl _) hP hA hAQ n

/-! ### 279.1 ⟹ ★★★★ **`hsnoc_gen` はそのまま使えます**

§275 の `hsnoc_gen` は `hIH` を **述語 `P` について一般**に取っています。
**⟹ ★ ですが `hIH` の型が **`meas V d0 d1 < meas Q d e`** で書かれています。**
**⟹ ⟹ ★★ `(A, Q, d, e)` 版では **`meas A' V d0 d1 < meas A Q d e`** になります。**
**⟹ ⟹ ⟹ ★ ですから **`hsnoc_gen` も測度を引数にする形に一般化**すれば、そのまま通ります。** -/

open Classical in
/-- ★★★★★★★ **`hsnoc_gen` の `(A, Q, d, e)` 測度版**。 -/
theorem hsnoc_gen3 {u : ℕ} {A Q T : TrioSeq} {d e c : ℕ}
    {P : TrioSeq → ℕ → ℕ → Prop} {meas : TrioSeq → TrioSeq → ℕ → ℕ → ℕ}
    (hIH : ∀ A' V d0 d1, P V d0 d1 → meas A' V d0 d1 < meas A Q d e →
      A' ∈ W u → A' ++ V ∈ W u → ∀ m, A' ++ mTower V d0 d1 m ∈ W u)
    (hL : T.length - 1 ≠ 0)
    (hz : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0 ∧
      entry T 2 (T.length - 1) = 0))
    (hpar : hasParent T (srow T (T.length - 1)) (T.length - 1))
    (hpe : parent T (srow T (T.length - 1)) (T.length - 1) = c)
    (hpre : T.dropLast ∈ W u)
    (hPV : P ((T.drop c).take (T.length - 1 - c))
      (if 0 < srow T (T.length - 1) then entry T 0 (T.length - 1) - entry T 0 c else 0)
      (if 1 < srow T (T.length - 1) then entry T 1 (T.length - 1) - entry T 1 c else 0))
    (hmeas : meas (T.take c) ((T.drop c).take (T.length - 1 - c))
        (if 0 < srow T (T.length - 1) then entry T 0 (T.length - 1) - entry T 0 c else 0)
        (if 1 < srow T (T.length - 1) then entry T 1 (T.length - 1) - entry T 1 c else 0)
      < meas A Q d e) :
    T ∈ W u := by
  have hclt : c < T.length := by
    rw [← hpe]
    exact (nextR_index_lt (parent_nextR hpar)).trans_le (by omega)
  have hc1 : c ≤ T.length - 1 := by omega
  have hTc : T.take c ∈ W u := by
    have := Wset.W_take (u := u) (M := T.dropLast) hpre c
    rwa [List.dropLast_eq_take, List.take_take, Nat.min_eq_left (by omega)] at this
  have hcat : T.take c ++ (T.drop c).take (T.length - 1 - c) ∈ W u := by
    rw [take_append_window hc1]; exact hpre
  refine mem_of_oper_mem ?_
  intro m _
  rw [snocStep_oper_gen_eq m hL hz hpar hpe]
  exact hIH (T.take c) _ _ _ hPV hmeas hTc hcat m

/-! ### 279.2 ⟹ ★★★ **(b) の出発点がそろいました**

    ✅ **帰納法の枠** …… §279 `tower_of_measure_step3`（`meas : (A, Q, d, e) → ℕ`）
    ✅ **1 段の snoc** … §279.1 `hsnoc_gen3`（`A' = T.take c` が**自動で決まります**）
    ⛔ **残る義務** …… **`meas (T.take c) V d0 d1 < meas A Q d e`** となる `meas` を見つけること

**⟹ ★★★★★ ★ そして **`A'` は自由ではなく `T.take c`** です。⟹ ⟹ ★★ **測度の設計が楽になります**:**

    ★ **`A` は伸びるだけではありません**: `A' = T.take c` で、⟹ **`c` は親の位置**
    ⟹ ★★ 親がブロックの中 ⟹ `A'` は `A` より**長い**
    ⟹ ⛔ 親が接頭辞の中 ⟹ `A'` は **`A` より短い**（`c < |A|`）
    ⟹ ⟹ ★★★ ですから **`|A'|` は単調ではありません**（今日の測定と整合）

**⟹ ★ ですが **`A' ++ V = T.dropLast`** なので、⟹ ★★ **`|A'| + |V| = |T| - 1`** です。**
**⟹ ⟹ ⚠ そして `|T| - 1` は **snoc のたびに伸びます** ⟹ ⛔ **和も単調ではありません**。**

⚠ **教訓 14**: 枠は緑ですが、**`meas` はまだ 1 つも見つかっていません**。

### ⛔⛔ 279.3 **`A` を含む候補も 6 個とも駄目**でした（実測）

母集団: 根の行 0 ∈ {0, 2}、`A` 5 種（空・浅い列あり）、`d ≤ 2`、`e ≤ 1`、`n ≤ 2`、`|Q| ≤ 3`。
比べるのは **`(A' = T.take c, V)` vs `(A, Q)`**（＝ 帰納法が要求する形）。

| 候補 | 減 | 同 | ⛔ 増 |
|---|---|---|---|
| `lev V 0`（親の水準） | 30.86% | | ⛔ **32.09%** |
| `lev A' (|A'|−1)`（接頭辞の末尾） | 4.66% | | ⛔ **51.72%** |
| `A'` の中の浅い列の数 | 18.34% | | ⛔ **69.14%** |
| 浅さのギャップ | 18.34% | | ⛔ **69.14%** |
| `|A'|` | 18.34% | | ⛔ **69.14%** |
| **`|A'| + |V|`** | ★ **0.00%** | 21.5% | ⛔ **78.49%** |

**⟹ ⛔ **6 個とも増えます**。⟹ ★ とくに **`|A'| + |V| = |T| − 1` は一度も減りません**（0.00%）。**
**⟹ ⟹ ★★★ ＝ **snoc のたびに列が伸びるから**です。⟹ ⟹ ★ **「大きさ」型の量は全部駄目**。**

**⟹ ★★★★★ ⟹ ですから **(b) も単純な測度では閉じません**。**
**⟹ ⟹ ⛔ 減るものがあるとすれば **順序数型の量**——⟹ ★ **それは証明したい命題そのもの**です。**

⚠ **教訓 14**: 「6 個が駄目」であって「全部駄目」ではありません。
**⟹ ★ ですが **`|A'| + |V|` が 0.00% 減**という事実は、**構造から出ています**（列が伸びる）。 -/

/-! ## 280. ★★★★★★ **`lev(親) < lev(的)`** —— 行 1・行 2 は定義から出ます（行 0 は出ません）

`Wset.lev M j = 2 · entry M 1 j + entry M 2 j`。⟹ ★ 親の水準を測度に使う案（team-lead ＋ 私）の
**段内の事実**を先に緑にします。

    **行 1** … `nextrel1` は `entry M 1 y < entry M 1 j` を与える
      ⟹ ⚠ **行 2 は何も言わない** ⟹ ★ **`zle1`（行 2 ≤ 1）**の下でだけ `lev` が下がる
    **行 2** … `nextrel2` は `entry M 2 y < entry M 2 j` ＋ `le1 M y j`（`y < j` なら行 1 も狭義に小さい）
      ⟹ ★ **両方下がる** ⟹ **`zle1` すら要りません**
    ⛔ **行 0** … `nextrel0` は行 1・行 2 について**何も言いません**
      ⟹ ⟹ ★ しかも `srow = 0` は `entry M 1 j = 0 ∧ entry M 2 j = 0` ⟹ **`lev M j = 0`**
      ⟹ ⟹ ⟹ ⛔ **`lev(親) < 0` は不可能** ⟹ **行 0 では原理的に出ません** -/

theorem lev_lt_of_nextrel2 {M : TrioSeq} {y j : ℕ} (hyj : y < j) (h : nextrel2 M y j) :
    lev M y < lev M j := by
  have h2 : entry M 2 y < entry M 2 j := h.2.2.2.1
  have h1 : entry M 1 y < entry M 1 j := by
    -- `le1 M y j` は `y < j` なら 1 歩以上 ⟹ 行 1 が狭義に増える
    obtain ⟨-, -, hrt⟩ := h.2.2.2.2.1
    clear h h2
    induction hrt with
    | refl => omega
    | @tail b c hab hbc ih =>
        rcases Nat.lt_or_ge y b with hb | hb
        · exact lt_trans (ih hb) hbc.2.2.2.1
        · have : y = b := by
            have := rtg1_index_le hab
            omega
          rw [this]; exact hbc.2.2.2.1
  unfold lev; omega

theorem lev_lt_of_nextrel1 {M : TrioSeq} {y j : ℕ}
    (hz1 : entry M 2 y ≤ 1) (h : nextrel1 M y j) : lev M y < lev M j := by
  have h1 : entry M 1 y < entry M 1 j := h.2.2.2.1
  unfold lev; omega

/-! ### 280.1 ⛔ **行 0 では出ません**（`srow = 0` なら `lev` が 0） -/

theorem lev_zero_of_srow_zero {M : TrioSeq} {j : ℕ} (h : srow M j = 0) : lev M j = 0 := by
  unfold srow at h
  by_cases h2 : 0 < entry M 2 j
  · rw [if_pos h2] at h; omega
  · rw [if_neg h2] at h
    by_cases h1 : 0 < entry M 1 j
    · rw [if_pos h1] at h; omega
    · unfold lev; omega

/-! ### 280.2 ⟹ ★★ **段内は出ました。残るのは「段をまたいで推移するか」**

    ✅ **行 1**（`zle1` の下） … §280 `lev_lt_of_nextrel1`
    ✅ **行 2** ……………… §280 `lev_lt_of_nextrel2`（**前提なし**）
    ⛔ **行 0** ……………… **原理的に出ません**（`lev(的) = 0`）

**⟹ ⚠ そして **段をまたぐと比べる相手が変わります**:**

    段 `k` の窓の根 ＝ **段 `k` の的の親** ⟹ ★ `lev` はその段の中では下がる
    段 `k+1` の的 ＝ **`T` の末尾**（新しく snoc した列）⟹ ⛔ **段 `k` の的とは別物**
    ⟹ ⟹ ⛔ ですから **段内の `lev(親) < lev(的)` からは、段をまたぐ減少は出ません**

**⟹ ★ 測度に使うには **`lev V 0 < lev Q 0`**（窓の根 vs いまの `Q` の根）が要ります。**
**⟹ ⟹ ⚠ そして **`Q` の根と的は別の列**なので、⟹ ★ **§280 は直接は効きません**。**

⚠ **教訓 14**: §280 は緑ですが、**測度の減少ではありません**。⟹ ★ **段内の事実**だけです。

### ⛔ 280.3 **`lev V 0 < lev Q 0` も駄目**でした（実測、`srow` で分けても）

母集団: 根の行 0 ∈ {0, 2}、行 2 も振る、`A` 5 種（浅い列あり）、`d ≤ 2`、`e ≤ 1`、`n ≤ 2`。

| `srow`（的） | 減 | 同 | ⛔ 増 |
|---|---|---|---|
| **0** | **2.63%** | 54.1% | ⛔ 43.3% |
| **1** | **31.63%** | 34.0% | ⛔ 34.4% |
| **2** | **27.25%** | 36.9% | ⛔ 35.9% |

**⟹ ⛔ **`srow` で分けても 27〜32% しか減りません**。⟹ ★ **測度になりません**。**
**⟹ ⟹ ★ §280 が言うのは **`lev(親) < lev(的)`** であって、⟹ ⛔ **`lev(親) < lev(Q の根)` ではありません**。**
**⟹ ⟹ ⟹ ★★ **`Q` の根と的は無関係な 2 列**なので、⟹ ★ **段内の事実は測度に持ち上がりません**。** -/

/-! ## 281. ★★★★★ **H12 の `rankDE = srow` は「同じ測度の言い換え」**——ですが**大きな帰結**があります

H12 の (W44): **`rankDE (wd0 P B j p) (wd1 P B j p) = srow(末尾)`**（等号、緑）。

**⟹ ⚠ ★ これは **測度を変えません**。⟹ ⟹ ★ `towerMeas` は元から `3|V| + rankDE` で、
`rankDE (wd0) (wd1)` が `srow` に等しいだけです。⟹ ★★ **同じ関数の別の書き方**です。**

**⟹ ★★★★★ ⟹ ですが **帰結が大きい**です。⟹ ★ **実測**（根の行 0 ∈ {0,2}、行 2 も振る、
`A` 5 種（浅い列あり）、`d ≤ 2`、`e ≤ 1`、`n ≤ 2`、`srow ≥ 1`）:**

    測度 `3|V| + srow` ……… **減 81.31% ／ 同 0.00% ／ ⛔ 増 18.69%**
    ★★★★★★★ **`|V| = |Q|` の段** … **`srow < rankDE d e` が 14,160 / 14,160 ＝ 100.0000%**

**⟹ ★★★★★★★ ⟹ **等号の段は 100% 救われます**。⟹ ★ **私の 3,114 件の心配は消えました**。**
**⟹ ⟹ ★★ そして **`同` が 0.00%** ⟹ ⟹ ★ **破れは全部 `|V| > |Q|`** です。**

### ⟹ ★★★★★ 281.1 **残差の最終形（今日の最後）**

    ⛔ **`|V| > |Q|` の段だけ**（実測 18.69%）
    ⟹ ★ そして **`|V| > |Q|` ⟺ 親が「1 つ前のブロックの同位置」より手前**
    ⟹ ⟹ ★★ ＝ **接頭辞 `A` が `Q` の根より浅いとき**（§278 の診断）

**⟹ ★ ですから **`|V| = |Q|` と `|V| < |Q|` は片づき、`|V| > |Q|` だけが残ります**。**

### ⛔ 281.2 **team-lead の候補 (2) は駄目**でした

「**`A'` の中で `V` の根より浅い列の数**」（`Q` の根ではなく `V` の根を基準に）:

    ⟹ ⛔ **減 18.69% ／ 同 12.35% ／ 増 68.96%** ⟹ ★ **基準を変えても駄目**でした

⚠ **教訓 14**: §281 は**測定**です。⟹ ★ `rankDE_eq_srow` 自体は H12 の緑の定理です。 -/

/-! ## 282. ★★★★★★★ **(RES-T1): 残差の段は連続しません**（実測 15,720 / 15,720）

§281 で残差が **`|V| > |Q|` の段だけ**に絞れました。⟹ ★ **その段が連続するか**を測りました。

    箱: `|Q| ≤ 3`、`d ∈ {1,2}`、`e ≤ 1`、`n ≤ 2`、`A` 3 種（**`|A| ≤ 1`**）、根の行 0 ∈ {0, 2}、
      ⛔ **そして `srow = 0` の段を全部飛ばしていました**
    分母（残差の段からの遷移）**15,720**
    ★ **残差 → 良い: 15,720（100.00%）** ／ **残差 → 残差: 0 件**

⚠⚠⚠ **【2026-08-30 撤回】この 0% は箱の産物でした。R2 が正しく、私が誤りです。**

    ⛔ **箱の穴 3 つ**: **`|A| = 2` が無い**（残差は `c < |A|` なので `|A| ≥ 2` が要る）／
      **`d = 0` が無い**／ ★★★ **`srow = 0` の段を `continue` で全部飛ばしていた**
    ⛔ **コードのバグ**: `oper` の定義は **`d0 := if 0 < i1 then … else 0`** なのに、
      私は**番人なしで** `d0` を計算していました ⟹ `srow = 0` で `d0` が誤り

**⟹ ★ R2 の反例を、番人を入れて再現しました:**

```
A = [(0,0,0),(1,0,0)]、Q = [(2,0,0),(3,0,0)]、d = 0、e = 0、n = 1、j = 0
1 段目: srow = 0、c = 1 ⟹ |V| = 3 > |Q| = 2 ⟹ **残差**
2 段目 n2 = 1, 2, 3: ⟹ **|V2| = 4, 7, 10** ⟹ **どれも残差** ⟹ ★ **R2 の数字と一致**
```

**⟹ ★★★ ⟹ ただし **`srow ≥ 1` に限れば 0 件は正しい**（15,720 件）。**
**⟹ ⟹ ★ そして **R2 の反例は 1 段目も 2 段目も `srow = 0`**。**
**⟹ ⟹ ⟹ ★★★★ ですから **「残差 → 残差 は `srow = 0` でだけ起きる」**かもしれません。**
**⟹ ⟹ ⟹ ⟹ ★★ そして **`srow = 0` ⟹ `d0 = d1 = 0` ⟹ 塔は同一コピー ⟹ `PrefixCopies` の場面**です。**

**⟹ ★ 機構: 残差 ＝ 「親が前 ⟹ **窓が塔を丸ごと飲む**」⟹ ★★ `V` が長くなる。**
**⟹ ⟹ ★★★ 長い `V` で塔を作ると、**次の親は `V` の最後のブロックの中**に落ちます ⟹ **良い群**。**

⚠ **教訓（私自身の 4 番目）**: **小さい箱の 100% は、対照が通っても信用できません**。
**⟹ ★ 大きい箱とシートで裏を取る必要があります。**

### ⚠⚠ 282.1 **Lean で書くときの問題**（先に書いておきます）

**⟹ ⛔ 「残差か良いか」は **状態 `(A, Q, d, e)` の性質ではありません**。**
**⟹ ★ `hstep` は **`∀ n j`** なので、⟹ ⟹ **同じ状態から良い手も残差の手も出ます**。**
**⟹ ⟹ ★★ ですから **「2 段先の測度」をそのまま測度にはできません**。**

**⟹ ★★★ ⟹ **本当に要るのは `meas(2 段先) < meas(いま)`** です:**

    ★ 残差の段で `meas` は増える（`|V| > |Q|`）
    ★★ 次の良い段で減る（`|V'| < |V|`）
    ⟹ ⚠ ですが **`|V'| < |Q|` とは限りません** ⟹ ⛔ **2 段でも増えるかもしれません**

**⟹ ★★★★★ ⟹ ですから **(RES-T1) が 100% でも、それだけでは足りません**。**
**⟹ ⟹ ★ **`meas(2 段先) < meas(いま)` を別に測る**必要があります。⟹ ★★ **測定中**です。**

⚠ **教訓 14**: 「残差が連続しない」は**必要条件**であって、**十分ではありません**。

### ⛔⛔⛔ 282.2 **測りました: 2 段でも減りません**（30.89% 増）

    分母（残差 → 良い の 2 段）**15,720**
    ★ 2 段で減る ……… 9,424（59.95%）
    ⚠ 同 ……………… 1,440（9.16%）
    ⛔ **2 段でも増える** … **4,856（30.89%）**

**⟹ ⛔ 反例:**

```
Q = [(2,1,0), (3,0,0)]、d = 1、e = 0、n = 2、j = 0、A = [(0,0,0)]
⟹ 1 段目（残差）: |V| = 5（|Q| = 2 なので増える）
⟹ 2 段目（良い）: |V2| = 3
⟹ ⛔ meas: 7 → 10 ⟹ **2 段でも増えます**
```

**⟹ ★ 理由: 残差の段で **`|V|` が `|Q|` の 2 倍以上**になり、⟹ ★★ 次の段で `|V'| < |V|` でも
**`|V'| > |Q|` のまま**だからです。⟹ ⟹ ★★★ **`n` を大きくすると差がもっと開きます**。**

**⟹ ⛔⛔⛔ ですから **(RES-T1) が 100% でも、この枠は閉じません**。**
**⟹ ⟹ ★★★ ⟹ **`k` 段まとめても同じ**はずです（残差のたびに `|V|` が `n` 倍近く伸びるので）。**

### ⛔⛔⛔⛔ 282.3 **最終結論: この枠では閉じません**

    ★ **`|A'| + |V| = |T| − 1`**（`T` ごとに固定）＋ **`|T|` は snoc で伸びる**
    ⟹ ⛔ **「大きさ」型の自然数測度は原理的に存在しません**（team-lead の算術）
    ⟹ ⛔ **`lev` 型・「浅さ」型も実測で全滅**（候補 10 個）
    ⟹ ⛔ **`srow` は等号の段を救うが、`|V| > |Q|` は救えない**（§281）
    ⟹ ⛔ **残差は連続しないが、2 段でも減らない**（§282.2）

**⟹ ★★★★★ ⟹ **`tower_of_measure_step2/3` の枠は、測度では閉じません**。**
**⟹ ⟹ ★ 残るのは **枠そのものを変える**——⟹ ⚠ ですが `Aop` の 3 節は既に使い切っています。 -/

/-! ## 283. ⛔⛔⛔ **(G1) も駄目**でした —— 良い群も「再帰」です

team-lead の最後の望み:「**良い群（`c ≥ |A|`）を IH なしで処理できれば、再帰は残差だけになり、
残差では `|A|` が `n` に依らず真に減るので `|A|` だけで整礎**」。

**⟹ ★ 問い: **`A' ++ mTower V d0 d1 m` は `A ++ mTower Q d e N` の take で作れますか**。**

**⟹ ⛔ 実測（良い群だけ、`|Q| ≤ 3`、`d ≤ 2`、`e ≤ 1`、`n ≤ 2`、`m ≤ 2`、`A` 3 種、根の行 0 ∈ {0,2}）:**

    分母 **15,024**
    ★ **`N ≤ n` で接頭辞になる** … **3,384（22.52%）** ⟹ ★ **この分だけは無料**
    ⛔ **`N > n` で接頭辞** ……… **4,128（27.48%）** ⟹ **循環**（H12 の (W46) と同じ壁）
    ⛔⛔ **どの `N` でも接頭辞にならない** … **7,512（50.00%）**

**⟹ ★★★ **半分は接頭辞ですらありません**。⟹ ⛔ **(G1) は成り立ちません**。**

### ★ 283.1 **理由（構造）**

**⟹ ★ 新しい持ち上げ量 **`(d0, d1)` は `(d, e)` と違います**。**
**⟹ ⟹ ★★ ですから **`mTower V d0 d1 m` は `mTower Q d e N` の部分列ではありません**——
**周期が違う**のです。**
**⟹ ⟹ ⟹ ★ 反例: `Q = [(0,0,0),(1,0,0)]`、`d = 1`、`e = 1`、`n = 1`、`j = 0`、`A = []`、`m = 2`
⟹ `V = Q` だが **`(d0, d1) ≠ (d, e)`** ⟹ ⛔ **別の塔**。**

### ⛔⛔⛔⛔ 283.2 **これで枠の望みは全部消えました**

    ⛔ 測度（大きさ型）…… 原理的に無い（`|A'| + |V| = |T| − 1` 固定、`|T|` は伸びる）
    ⛔ 測度（`lev` 型・浅さ型）… 実測で全滅（候補 10 個）
    ⛔ `srow` ………………… 等号の段だけ救う
    ⛔ 2 段まとめ …………… 30.89% 増（§282.2）
    ⛔ **順序数 `omega·|A| + towerMeas`** … **良い群で `|A|` が `n` 比例で増える**（team-lead の算術）
    ⛔ **(G1)「良い群を無料に」** … **50% は接頭辞ですらない**（§283、**今回**）

**⟹ ★★★★★ ⟹ **`tower_of_measure_step2/3` の枠は、閉じません**。⟹ ★ **枠ごと変えるしかありません**。** -/

/-! ## 284. ★★★★★ **(G2) の土台**: `srow = 0` の段は **同一コピー**（＝ `PrefixCopies` の場面）

§282 の撤回で「残差 → 残差 は `srow = 0` でだけ起きるかもしれない」と分かりました。
**⟹ ★ その `srow = 0` の段が何かを、定義から書きます。** -/

theorem wd0_zero_of_srow_zero {T : TrioSeq} {c : ℕ} (h : srow T (T.length - 1) = 0) :
    (if 0 < srow T (T.length - 1) then entry T 0 (T.length - 1) - entry T 0 c else 0) = 0 := by
  rw [h]; simp

theorem wd1_zero_of_srow_zero {T : TrioSeq} {c : ℕ} (h : srow T (T.length - 1) = 0) :
    (if 1 < srow T (T.length - 1) then entry T 1 (T.length - 1) - entry T 1 c else 0) = 0 := by
  rw [h]; simp

/-- ★★★★★ **`srow = 0` の段は「同一コピーの塔」**（`mTower V 0 0 m`）。 -/
theorem snocStep_oper_srow_zero {T : TrioSeq} {c : ℕ} (m : ℕ)
    (hL : T.length - 1 ≠ 0)
    (hz : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0 ∧
      entry T 2 (T.length - 1) = 0))
    (hpar : hasParent T (srow T (T.length - 1)) (T.length - 1))
    (hpe : parent T (srow T (T.length - 1)) (T.length - 1) = c)
    (h0 : srow T (T.length - 1) = 0) :
    T⟦m⟧ = T.take c ++ mTower ((T.drop c).take (T.length - 1 - c)) 0 0 m := by
  rw [snocStep_oper_gen_eq m hL hz hpar hpe, wd0_zero_of_srow_zero (c := c) h0,
    wd1_zero_of_srow_zero (c := c) h0]

/-! ### 284.1 ⟹ ★★★★ **(G2) の形**

    ★ **`srow = 0` の段** ⟹ **`mTower V 0 0 m` ＝ `V` の同一コピー `m` 個**
      ⟹ ⟹ ★★ ＝ **`L53.PrefixCopies` の結論そのもの**
      ⟹ ⟹ ⟹ ★ そして **`PrefixCopies` は接頭辞 `A` に条件を課しません**（私の §270）
    ★★ **`srow ≥ 1` の段** ⟹ 私の実測では **残差 → 残差 が 0 件**（15,720 件、`srow ≥ 1` に限る）

**⟹ ★★★★★ ⟹ ですから **(G2)「`srow = 0` は `PrefixCopies` に、`srow ≥ 1` は測度に」**の形が見えます。**

**⟹ ⚠ ただし 3 つ確かめる必要があります:**

    ⛔ **(a) `PrefixCopies` 自身が未証明**（`A = []` だけ緑: `prefixCopies_nil`）
    ⛔ **(b) `srow ≥ 1` に限っても、2 段で減るか**は未確認（§282.2 は `srow ≥ 1` で 30.89% 増でした）
    ⛔ **(c) 「残差 → 残差 は `srow = 0` でだけ」自体が未確認**（測定中）

**⟹ ⚠ とくに (b) が厳しいです。⟹ ★ §282.2 は `srow ≥ 1` の箱でしたが、**それでも 30.89% 増**でした。**
**⟹ ⟹ ⛔ ですから **`srow = 0` を外しても、`srow ≥ 1` の 2 段は減りません**。**
**⟹ ⟹ ⟹ ★★ ですから **(G2) は「残差 → 残差 が無い」だけでは足りません**（§282.1 の指摘のとおり）。**

### ★★★★★ 284.2 **(c) を測りました: 残差 → 残差 は 100% が `srow = 0`**

`srow = 0` ／ `d = 0` ／ `|A| = 2` を全部入れ、`oper` の番人つきで測り直しました。

    分母 **59,418**
    ⛔ **残差 → 残差: 168（0.2827%）** ⟹ ★ **R2 の 0.2798% とほぼ一致**
    ★★★★★ **その 168 件は全部 `1 段目 srow = 0` かつ `2 段目 srow = 0`**

**⟹ ★★★ ですから **「残差 → 残差 は `srow = 0` でだけ起きる」は正しい**です。**
**⟹ ⟹ ★ そして **`srow ≥ 1` に限れば 残差 → 残差 は 0 件**（私の 15,720 件）——**撤回不要**でした。**

### ⛔ 284.3 **それでも (G2) は閉じません**

**⟹ ⛔ §282.2（`srow ≥ 1` の箱）で **2 段でも 30.89% 増**でした。**
**⟹ ⟹ ★ ですから **`srow = 0` を `PrefixCopies` に押し込めても、`srow ≥ 1` の 2 段が減りません**。**
**⟹ ⟹ ⟹ ★★ ＝ §282.1 で先に書いたとおり:**
**「残差が連続しない」は必要条件であって、十分ではありません。**

⚠ **教訓 14**: §284 は緑ですが、**(G2) が閉じる保証はありません**。 -/

/-! ## 285. ★★★★★★★★ **(G3): 残核を 2 本の既知の命題に落とします**

§284 で `srow = 0` の段が「同一コピー」だと分かりました。⟹ ★ **3 通り全部を書きます**。

| 末尾の `srow` | `(d0, d1)` | 後継の形 | 名前 |
|---|---|---|---|
| **0** | `(0, 0)` | `mTower V 0 0 m`（**同一コピー**） | **`PrefixCopies`**（`L53Subst:3599`） |
| **1** | `(d0, 0)` | `mTower V d0 0 m`（**行 0 だけ**） | **`shTower`**（`Wtower2:1688`） |
| **2** | 両方 > 0 | `mTower V d0 d1 m` | 一般（R2 実測: 残差 0 件） |

**⟹ ★ `d0` / `d1` は `oper` の定義の番人（`if 0 < i1` / `if 1 < i1`）から**直接**出ます。** -/

theorem wd1_zero_of_srow_one {T : TrioSeq} {c : ℕ} (h : srow T (T.length - 1) = 1) :
    (if 1 < srow T (T.length - 1) then entry T 1 (T.length - 1) - entry T 1 c else 0) = 0 := by
  rw [h]; simp

/-- ★★★★★★ **`srow = 1` の段は「行 0 だけ持ち上げる塔」**（`e = 0`、＝ `shTower` の形）。 -/
theorem snocStep_oper_srow_one {T : TrioSeq} {c : ℕ} (m : ℕ)
    (hL : T.length - 1 ≠ 0)
    (hz : ¬ (entry T 0 (T.length - 1) = 0 ∧ entry T 1 (T.length - 1) = 0 ∧
      entry T 2 (T.length - 1) = 0))
    (hpar : hasParent T (srow T (T.length - 1)) (T.length - 1))
    (hpe : parent T (srow T (T.length - 1)) (T.length - 1) = c)
    (h1 : srow T (T.length - 1) = 1) :
    T⟦m⟧ = T.take c ++ mTower ((T.drop c).take (T.length - 1 - c))
      (entry T 0 (T.length - 1) - entry T 0 c) 0 m := by
  rw [snocStep_oper_gen_eq m hL hz hpar hpe, wd1_zero_of_srow_one (c := c) h1,
    show (if 0 < srow T (T.length - 1) then entry T 0 (T.length - 1) - entry T 0 c else 0)
      = entry T 0 (T.length - 1) - entry T 0 c from by rw [h1]; simp]

/-- ★★★★ **`e = 0` の塔は `shTower`**（`Lift1 X 0 = X`、`shiftr01` の掛け算の向きだけ違います）。 -/
theorem mTower_zero_e (Q : TrioSeq) (d n : ℕ) :
    mTower Q d 0 n = (List.range n).flatMap fun k => shiftr01 (d * k) 0 Q := by
  unfold mTower
  refine List.flatMap_congr (fun k _ => ?_)
  rw [Nat.zero_mul, Wset.Lift1_zero]

/-! ### 285.1 ⟹ ★★★★★★★★ **残核の言い換え（証明ではありません）**

    ★ **`srow = 0`** ⟹ 後継 ＝ **`V` の同一コピー `m` 個** ⟹ ★★ **`PrefixCopies` の形**
    ★ **`srow = 1`** ⟹ 後継 ＝ **`shTower V d0 m`**（行 0 だけ） ⟹ ★★ **`ShiftTowerClosed` の形**
    ⚠ **`srow = 2`** ⟹ 一般形。⟹ ★ R2 の実測では **残差 0 件** ⟹ ⛔ **型ではまだ言えていません**

**⟹ ★★★ ⟹ ですから **`MTowerClosedS` の残核は、次の 2 本 ＋ 行 2 の 1 点**です:**

    ⛔ **`PrefixCopiesOpen`**（`L53Subst:3801`）… 「**接頭辞に `Q` の根より浅い列がある**」場合
      ⟹ ★ **今日 12 本の死から抽出した形と、逐語で同じ**でした
      ⟹ ⚠ R2 実測: **開いている側が 65.81%**（分母 15,425）⟹ **corner case ではありません**
    ⛔ **`ShiftTowerClosed`**（`L51Tower:21`）… `e = 0` の塔
    ⚠ **行 2（`srow = 2`）で残差が本当に 0 か** … 実測のみ

**⟹ ★ **どちらも既に名前がついていて、既に未証明として記録されている**ものです。**
**⟹ ⟹ ★★ ですから **今日の探索は、既知の 2 本に戻ってきた**——⟹ ★ **問題の核は 1 つ**でした。**

⚠ **教訓 14**: §285 は**言い換え**です。⟹ ★ **何も証明していません**。 -/

/-! ## 286. ★★★★★ **`PrefixCopiesOpen` は「行 2 に 1 がある」場合だけ**です

✅ **ビルドが更新され、`import H12Export` で H12 の最新分（294 本）が見えるようになりました**
（探針で確認）。⟹ ★ **逐語の写しはもう要りません**。

**⟹ ★ H12 の `prefix_mem_of_zeroRow2`（`W_add` を通らない唯一の扉）を当てます:**

    `A ∈ W u` ∧ `A ≠ []` ∧ **`A` も `T` も行 2 ≡ 0** ⟹ `A ++ T ∈ W u`
    ⟹ ★★ **`rsum` も `T ∈ W u` も要りません**（`mem_Wself_iff` ＋ `zeroRow2_mem_Wself` 経由） -/

theorem prefixCopiesOpen_of_zeroRow2 {u n : ℕ} {A Q : TrioSeq}
    (hzA : ∀ p ∈ A, p.2.2 = 0) (hzQ : ∀ p ∈ Q, p.2.2 = 0)
    (hA : A ∈ W u) (hAne : A ≠ []) :
    A ++ ((List.range n).flatMap fun _ => Q) ∈ W u := by
  refine H12Export.prefix_mem_of_zeroRow2 hzA ?_ hA hAne
  intro p hp
  rw [List.mem_flatMap] at hp
  obtain ⟨-, -, hp⟩ := hp
  exact hzQ p hp

/-! ### 286.1 ⟹ ★★★ **ですから `PrefixCopiesOpen` の中身は「行 2 に 1 がある」場合だけ**

**⟹ ⚠ そして **これは深い結果ではありません**。⟹ ★ **行 2 ≡ 0 の列は全部 `Wself` に入る**
（`Wtower2.zeroRow2_mem_Wself`）ので、⟹ ★★ **`lev(根) ≤ u` さえあれば無条件**です。**

**⟹ ★ ですが **開いている部分の場所が確定**します:**

    ✅ **`A` も `Q` も行 2 ≡ 0** …… **無料**（§286、`rsum` 不要）
    ⛔ **どちらかに行 2 = 1 がある** … **開いている**

**⟹ ★★★ ⟹ そして **`z < 2` の断片では行 2 ∈ {0, 1}** なので、⟹ ★ **`z = 1` の列がある場合**が残差です。**
**⟹ ⟹ ★ ＝ 生成元 `D_v = (0,0,0)(1,1,1)(2,2,1)…` の **`z = 1` の列**そのものです。**

**⟹ ⚠ R2 の (PCO-2)「開いている側 65.81%」は、⟹ ★ **たぶん `rsum` の破れで数えたもの**です。**
**⟹ ⟹ ★ ですから **「行 2 に 1 があるか」で数え直すと、もっと小さくなるはず**です。**

    **(PCO-3) ★★★ R2 に: **`PrefixCopiesOpen` の分母のうち、`A` も `Q` も行 2 ≡ 0 の割合**
      ⟹ ★ その分は **§286 で無料**です ⟹ ⟹ **本当に開いている分がわかります**

⚠ **教訓 14**: §286 は緑ですが、**`PrefixCopiesOpen` を証明したのではありません**。
**⟹ ★ **行 2 ≡ 0 の場合だけ**です。 -/

/-! ## 287. ★★★★★★ **(L-OPA) の下ごしらえ**: 祖先関係は `A ++ P` と `P` で**両方向**に一致します

§242 で `le0` は両方向、`le1` は `M → 窓` が緑でした。⟹ ★ **`le1` の逆向き**を足します。

**⟹ ★ 鍵（§254 と同じ）: `nextrel1 M (|A|+a) (|A|+b)` の最小性の候補 `q` は `q > |A|+a ≥ |A|`
⟹ ⟹ ★★ **必ず `P` の範囲**にいます。⟹ ⟹ ⟹ **接頭辞は最小性に効きません**。** -/

theorem le0_append_iff {A P : TrioSeq} {a b : ℕ} (ha : a < P.length) (hb : b < P.length) :
    le0 (A ++ P) (A.length + a) (A.length + b) ↔ le0 P a b := by
  have hL : A.length + P.length ≤ (A ++ P).length := by rw [List.length_append]
  constructor
  · intro h
    have := le0_window (T := A ++ P) (s := A.length) (L := P.length) hL ha hb h
    rwa [drop_take_append_right] at this
  · intro h
    refine le0_window' (T := A ++ P) (s := A.length) (L := P.length) hL ha hb ?_
    rwa [drop_take_append_right]

theorem nextrel1_append_of {A P : TrioSeq} {a b : ℕ} (ha : a < P.length) (hb : b < P.length)
    (h : nextrel1 P a b) : nextrel1 (A ++ P) (A.length + a) (A.length + b) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨by rw [List.length_append]; omega, by rw [List.length_append]; omega, by omega, ?_,
    (le0_append_iff ha hb).mpr h5, ?_⟩
  · rw [entry_append_right, entry_append_right]; exact h4
  · intro q ⟨hq1, hq2⟩
    have hqle : q ≤ A.length + b := le0_le' hq2
    obtain ⟨q', rfl⟩ : ∃ q', q = A.length + q' := ⟨q - A.length, by omega⟩
    have hq'b : q' ≤ b := by omega
    have := h6 q' ⟨by omega, (le0_append_iff (by omega) hb).mp hq2⟩
    rw [entry_append_right, entry_append_right]
    exact this

theorem le1_append_of {A P : TrioSeq} {a b : ℕ} (ha : a < P.length) (hb : b < P.length)
    (h : le1 P a b) : le1 (A ++ P) (A.length + a) (A.length + b) := by
  obtain ⟨-, -, hrt⟩ := h
  refine ⟨by rw [List.length_append]; omega, by rw [List.length_append]; omega, ?_⟩
  have key : ∀ c, Relation.ReflTransGen (nextrel1 P) a c → c < P.length →
      Relation.ReflTransGen (nextrel1 (A ++ P)) (A.length + a) (A.length + c) := by
    intro c hc
    induction hc with
    | refl => intro _; exact Relation.ReflTransGen.refl
    | @tail x y hx hxy ih =>
        intro hyP
        have hxP : x < P.length := hxy.1
        exact (ih hxP).tail (nextrel1_append_of hxP hyP hxy)
  exact key b hrt hb

theorem le1_append_iff {A P : TrioSeq} {a b : ℕ} (ha : a < P.length) (hb : b < P.length) :
    le1 (A ++ P) (A.length + a) (A.length + b) ↔ le1 P a b := by
  constructor
  · intro h
    have hL : A.length + P.length ≤ (A ++ P).length := by rw [List.length_append]
    have := le1_window (T := A ++ P) (s := A.length) (L := P.length) hL ha hb h
    rwa [drop_take_append_right] at this
  · exact le1_append_of ha hb

/-! ### 287.1 ⟹ ★★★★★ **これで `oper` の写しの `if` が一致します**

`oper M n` の写しは

    `(entry M 0 j + (if **le0 M j0 j** then k·d0 else 0), entry M 1 j + (if **le1 M j0 j** then k·d1 else 0), …)`

**⟹ ★ `M = A ++ P`、`j0 = |A| + p`、`j = |A| + j'` のとき、⟹ ★★ §287 で
**`le0 M j0 j ↔ le0 P p j'`** と **`le1 M j0 j ↔ le1 P p j'`**（**前提なし**）。**
**⟹ ⟹ ★★★ ですから **写しの中身が `P` の側と一致**します。⟹ ★ **`rsum` は要りません**。**

⚠ **残るのは「バッドルートが `P` の中」＝ `parent (A ++ P) i (|A|+|P|−1) = |A| + p`** です。 -/

/-! ## 288. ★★★★★★★★ **(L-OPA)**: `oper (A ++ P) n = A ++ oper P n` を **`rsum` なしで**

`Wset.oper_append_gen`（`Wset:1414`）は **`rsum A P`** を要求します。
**⟹ ★ ですが本当に要るのは **「バッドルートが `P` の中」**だけです。**

**⟹ ★★★ そして §273 の `snocStep_oper_gen_eq` を**両側に**当てるだけで出ます:**

    `M⟦n⟧ = M.take c ++ mTower ((M.drop c).take (|M|−1−c)) d0 d1 n`（**親の位置は任意**）

**⟹ ⟹ ★★★★★ **`mTower` の中の `Lift1` は「窓の中の `le1`」で判定**するので、⟹ ★ **接頭辞は効きません**。**
**⟹ ⟹ ⟹ ★★ ですから **`rsum` は要りません**。⟹ ★ **§287 すら要りませんでした**（`gexp` が吸収済み）。 -/

open Classical in
theorem oper_append_of_parent_in {A P : TrioSeq} {p : ℕ} (n : ℕ) (hP : 2 ≤ P.length)
    (hzP : ¬ (entry P 0 (P.length - 1) = 0 ∧ entry P 1 (P.length - 1) = 0 ∧
      entry P 2 (P.length - 1) = 0))
    (hparP : hasParent P (srow P (P.length - 1)) (P.length - 1))
    (hpeP : parent P (srow P (P.length - 1)) (P.length - 1) = p)
    (hparM : hasParent (A ++ P) (srow (A ++ P) ((A ++ P).length - 1))
      ((A ++ P).length - 1))
    (hpeM : parent (A ++ P) (srow (A ++ P) ((A ++ P).length - 1))
      ((A ++ P).length - 1) = A.length + p) :
    (A ++ P)⟦n⟧ = A ++ P⟦n⟧ := by
  have hMlen : (A ++ P).length = A.length + P.length := List.length_append
  have hlastM : (A ++ P).length - 1 = A.length + (P.length - 1) := by omega
  have hplt : p < P.length := by
    rw [← hpeP]
    exact (nextR_index_lt (parent_nextR hparP)).trans_le (by omega)
  have hE : ∀ i, entry (A ++ P) i ((A ++ P).length - 1) = entry P i (P.length - 1) := by
    intro i; rw [hlastM, entry_append_right]
  have hEc : ∀ i, entry (A ++ P) i (A.length + p) = entry P i p := by
    intro i; rw [entry_append_right]
  have hsr : srow (A ++ P) ((A ++ P).length - 1) = srow P (P.length - 1) := by
    unfold srow; rw [hE 2, hE 1]
  have hzM : ¬ (entry (A ++ P) 0 ((A ++ P).length - 1) = 0 ∧
      entry (A ++ P) 1 ((A ++ P).length - 1) = 0 ∧
      entry (A ++ P) 2 ((A ++ P).length - 1) = 0) := by
    rw [hE 0, hE 1, hE 2]; exact hzP
  rw [snocStep_oper_gen_eq n (by omega) hzM hparM hpeM,
    snocStep_oper_gen_eq n (by omega) hzP hparP hpeP]
  have hLb : (A ++ P).length - 1 - (A.length + p) = P.length - 1 - p := by omega
  have hdrop : (A ++ P).drop (A.length + p) = P.drop p := by
    rw [show A.length + p = A.length + p from rfl, ← List.drop_drop, List.drop_left]
  have htake : (A ++ P).take (A.length + p) = A ++ P.take p := by
    rw [List.take_append]
    congr 1
    · exact List.take_of_length_le (by omega)
    · congr 1; omega
  rw [hLb, hdrop, htake, hE 0, hE 1, hEc 0, hEc 1, hsr, List.append_assoc]

/-! ### 288.1 ⟹ ★★★★★★★★ **`rsum` の 3 つの用途のうち 1 つが外れました**

    ✅ **`oper_append_gen`** … **§288 で `rsum` なし**（バッドルートが `P` の中だけ）
    ⛔ `hasParent_append_gen`（`Wset:1445`）… まだ `rsum`
    ⛔ `domT_append` / `graft_append`（`Wset:1487`）… まだ `rsum`

**⟹ ★ そして **`XA_closed` の節 2（`oper`）の枝が、`rsum` の `A` 側なしで通る**ことになります。**
**⟹ ⟹ ⚠ ただし **`XA_closed` は 3 つの節すべてで `rsum` を使います** ⟹ ⛔ **1 つ外しても足りません**。**
**⟹ ⟹ ⟹ ★ **残り 2 つも同じ手で外せるか**——⟹ ★★ **そこが次です**。**

⚠ **教訓 14**: §288 は緑ですが、**`W_add` を弱めたわけではありません**。⟹ ★ **3 つのうち 1 つ**です。 -/

/-! ## 289. ★★★★★★★★ **`hasParent_append_gen` を `rsum` なしに** —— これで `W_add` の 3 用途が全部動きます

`Wset.lean` を読むと、**`rsum` の残り 2 用途も `hasParent_append_gen` 1 本に集約**されます:

    `graft_append`（`Wset:1434`）… ★ **`rsum` を使いません**（`P ≠ []` だけ）
    `domT_append`（`Wset:1487`）… ★ `rsum` は **`hasParent_append_gen` 経由だけ**

**⟹ ★★★★★ ですから **`hasParent_append_gen` を弱められれば、`W_add` の 3 用途が全部動きます**。** -/

theorem nextrel0_append_iff {A P : TrioSeq} {a b : ℕ} (ha : a < P.length) (hb : b < P.length) :
    nextrel0 (A ++ P) (A.length + a) (A.length + b) ↔ nextrel0 P a b := by
  have hL : A.length + P.length ≤ (A ++ P).length := by rw [List.length_append]
  have := nextrel0_window (T := A ++ P) (s := A.length) (L := P.length) hL ha hb
  rw [drop_take_append_right] at this
  exact this.symm

theorem nextrel2_append_of {A P : TrioSeq} {a b : ℕ} (ha : a < P.length) (hb : b < P.length)
    (h : nextrel2 P a b) : nextrel2 (A ++ P) (A.length + a) (A.length + b) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨by rw [List.length_append]; omega, by rw [List.length_append]; omega, by omega, ?_,
    le1_append_of ha hb h5, ?_⟩
  · rw [entry_append_right, entry_append_right]; exact h4
  · intro q ⟨hq1, hq2⟩
    have hqle : q ≤ A.length + b := le1_le' hq2
    obtain ⟨q', rfl⟩ : ∃ q', q = A.length + q' := ⟨q - A.length, by omega⟩
    have := h6 q' ⟨by omega, (le1_append_iff (by omega) hb).mp hq2⟩
    rw [entry_append_right, entry_append_right]
    exact this

theorem nextrel1_append_iff {A P : TrioSeq} {a b : ℕ} (ha : a < P.length) (hb : b < P.length) :
    nextrel1 (A ++ P) (A.length + a) (A.length + b) ↔ nextrel1 P a b := by
  constructor
  · intro h
    refine ⟨ha, hb, by have := h.2.2.1; omega, ?_,
      (le0_append_iff ha hb).mp h.2.2.2.2.1, ?_⟩
    · have := h.2.2.2.1
      rwa [entry_append_right, entry_append_right] at this
    · intro q ⟨hq1, hq2⟩
      have := h.2.2.2.2.2 (A.length + q)
        ⟨by omega, (le0_append_iff (by exact hq2.1) hb).mpr hq2⟩
      rwa [entry_append_right, entry_append_right] at this
  · exact nextrel1_append_of ha hb

theorem nextrel2_append_iff {A P : TrioSeq} {a b : ℕ} (ha : a < P.length) (hb : b < P.length) :
    nextrel2 (A ++ P) (A.length + a) (A.length + b) ↔ nextrel2 P a b := by
  constructor
  · intro h
    refine ⟨ha, hb, by have := h.2.2.1; omega, ?_,
      (le1_append_iff ha hb).mp h.2.2.2.2.1, ?_⟩
    · have := h.2.2.2.1
      rwa [entry_append_right, entry_append_right] at this
    · intro q ⟨hq1, hq2⟩
      have := h.2.2.2.2.2 (A.length + q)
        ⟨by omega, (le1_append_iff (by exact hq2.1) hb).mpr hq2⟩
      rwa [entry_append_right, entry_append_right] at this
  · exact nextrel2_append_of ha hb

theorem nextR_append_iff {A P : TrioSeq} {i a b : ℕ} (ha : a < P.length) (hb : b < P.length) :
    nextR (A ++ P) i (A.length + a) (A.length + b) ↔ nextR P i a b := by
  unfold nextR
  by_cases h0 : i = 0
  · rw [if_pos h0, if_pos h0]; exact nextrel0_append_iff ha hb
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : i = 1
    · rw [if_pos h1, if_pos h1]; exact nextrel1_append_iff ha hb
    · rw [if_neg h1, if_neg h1]; exact nextrel2_append_iff ha hb

/-- ★★★★★★★★ **`rsum` なしの `hasParent_append`**（要るのは「行 0 で越境できない」だけ）。 -/
theorem hasParent_append_of_noCross {A P : TrioSeq} {i j : ℕ} (hj : j < P.length)
    (hnc : ∀ c, c < A.length → ¬ le0 (A ++ P) c (A.length + j)) :
    hasParent (A ++ P) i (A.length + j) ↔ hasParent P i j := by
  constructor
  · intro h
    exact hasParent_peel_of_noCross
      (fun y hy => no_nextR_of_no_le0_cross (hnc y hy)) h
  · rintro ⟨y, hy, huniq⟩
    have hylt : y < P.length := by
      have := nextR_index_lt hy; omega
    refine ⟨A.length + y, (nextR_append_iff hylt hj).mpr hy, ?_⟩
    intro y' hy'
    rcases Nat.lt_or_ge y' A.length with hlt | hge
    · exact absurd hy' (no_nextR_of_no_le0_cross (hnc y' hlt))
    · obtain ⟨y'', rfl⟩ : ∃ y'', y' = A.length + y'' := ⟨y' - A.length, by omega⟩
      have hy''lt : y'' < P.length := by
        have := nextR_index_lt hy'; omega
      rw [huniq y'' ((nextR_append_iff hy''lt hj).mp hy')]

/-! ### 289.1 ⟹ ★★★★★★★★ **`W_add` の 3 用途が全部「行 0 の越境なし」に落ちました**

    ✅ **節 2**（`oper`）…… §288 `oper_append_of_parent_in`（バッドルートが `P` の中）
    ✅ **節 1**（長さ ≤ 1）… §289 `hasParent_append_of_noCross`
    ✅ **節 3**（graft）…… `graft_append` は **`rsum` を使わず**、`domT_append` は §289 経由

**⟹ ★★★ ⟹ ですから **`W_add` の `rsum` は「行 0 で越境できない」に弱められる**はずです。**
**⟹ ⟹ ★ そして **`rsum ⟹ 行 0 で越境できない`** は言えますが、⟹ ★★ **逆は言えません**（真に弱い）。**

⚠ **教訓 14**: §289 は緑ですが、**`W_add` を書き直したわけではありません**。
**⟹ ★ `XA_closed` は `Wset.lean` にあり、私は触りません。⟹ ⟹ ★★ **`L106` に弱めた版を作る**必要があります。**

### ⛔⛔ 289.2 **【自己訂正】弱まっていませんでした** —— `NoCross` は実質 `rsum` と同値

「`rsum` を『行 0 で越境できない』(`NoCross`) に弱められる」と報告しました。⟹ ⛔ **測ったら同値**でした。

    `NoCross A B :⟺ ∀ c < |A|, ¬ le0 (A ++ B) c ((A ++ B).length − 1)`

    分母 **18,468**（根の行 0 ∈ {0,2,3}、`A` 6 種（浅い列あり）、行 2 も振る）
    ★ `NoCross` 真 ∧ `rsum` 真 …… **7,182（38.89%）**
    ⛔ `NoCross` 偽 ∧ `rsum` 偽 …… **11,286（61.11%）**
    ⛔⛔ **`NoCross` 真 ∧ `rsum` 偽 … 0 件**

**⟹ ⛔ ですから **`NoCross` は `rsum` より真に弱くありません**（この箱では同値）。**
**⟹ ★ 理由（構造）: `A` に `B` の根より浅い列があると、⟹ ★★ その列から **`B` の根へ `nextrel0` が張れます**
（`hr0(B)` の下で `B` の全列が根以上なので最小性が通る）⟹ ⟹ ★★★ **そこから末尾へ `le0` で届きます**。**

**⟹ ⚠ ですから **§288 / §289 は「必要十分の形」ではありますが、新しい扉ではありません**。**
**⟹ ⟹ ★ **道具としては正しく、`rsum` が何のために要るかを正確にした**——⟹ ★★ **そこが価値**です。**

★ **ただし 1 つ良い副産物**: **`NoCross` は `oper` で保たれます**（実測 **18,468 / 18,468**）。
**⟹ ★ `rsum` も同じ（`oper_mem_ge`）なので、⟹ ⟹ **同値なら当然**です。** -/

/-! ### §292 `hr0` は窓に受け継がれる —— 後継は必ず `PrefixCopies` の族に残る

`oper` の窓は **`V = (T.drop c).take (t − c)`**（**親の列 `T[c]` を含む**）。
`V[0] = T[c]` は親であり、`nextrel0` の最小性から `(c, t)` のどの列以下。
⟹ **`hr0 V` は無料**（前提は `nextrel0` だけ）⟹ **族は保たれる**。

⚠ 私は §290 までこの窓を `T[c+1 .. t−1]` と 1 つずらして測っていた。
そのせいで「`hr0(V)` が 7.17% で偽」と報告したが、**それは誤り**である。
正しい窓では `hr0 V` は**定理**（実測でも 6,998,760 / 6,998,760）。 -/

/-- **窓の先頭は窓の中で最浅**（前提なし、`nextrel0` だけ）。 -/
theorem hr0_window {T : TrioSeq} {c t : ℕ} (h : nextrel0 T c t) :
    ∀ q ∈ (T.drop c).take (t - c), entry T 0 c ≤ q.1 := by
  intro q hq
  rw [List.mem_iff_getElem] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  have hlen : ((T.drop c).take (t - c)).length ≤ t - c := by
    simp [List.length_take]
  have hit : i < t - c := lt_of_lt_of_le hi hlen
  have hidx : ((T.drop c).take (t - c))[i] = T[c + i]'(by
      have := h.2.1
      omega) := by
    rw [List.getElem_take, List.getElem_drop]
  rw [hidx]
  have hE : ∀ (j : ℕ) (hj : j < T.length), entry T 0 j = (T[j]'hj).1 := by
    intro j hj
    simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  have hcj : c + i < T.length := by have := h.2.1; omega
  rw [← hE (c + i) hcj]
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · simp
  · have hmin := h.2.2.2.2 (c + i) ⟨by omega, by omega⟩
    have := h.2.2.2.1
    omega

end L106
end TRIO

/-! ## §290 (L-ROT): 良い枝の窓は `|Q|` より短い —— 周期性だけで出る

**(L-ROT)** への答え。`T = A ++ Q^n` の周期部分は `|Q|` 周期なので、
**親が接頭辞 `A` の外にあるなら、窓 `V` の長さは `|Q|` 未満**である。
⟹ **良い枝では次の `Q` が真に短くなる**（`|Q'| = |V| < |Q|`）。

実測（`|Q| <= 4`、`n <= 5`、`A` 10 種、`srow` 0/1/2 すべて、分母 28,829,600）:
非残差 11,059,650 件すべてで `|V| < |Q|`、例外 0 件（`tools/dbms/l3_rot.py`）。
以下は `srow = 0` の場合の**型での証明**。 -/

namespace TRIO
namespace L106

open Wset
open L105
open Classical

/-- **周期部分では窓は周期より短い**（前提なし、`nextrel0`）。

`c` 以降が周期 `m` で繰り返しているなら、`c` は `t` から `m` 未満の距離にある。
理由: そうでなければ `c + m` が `(c, t]` に入り、そこの行 0 は `entry T 0 c` に等しい。
`c + m = t` なら `entry T 0 c < entry T 0 t = entry T 0 c` で矛盾、
`c + m < t` なら `nextrel0` の最小性から `entry T 0 t <= entry T 0 c` で矛盾。 -/
theorem window_lt_of_periodic0 {T : TrioSeq} {a m c t : ℕ} (hm : 0 < m)
    (hper : ∀ x, a ≤ x → x + m ≤ t → entry T 0 (x + m) = entry T 0 x)
    (hc : a ≤ c) (h : nextrel0 T c t) : t - c < m := by
  rcases Nat.lt_or_ge (t - c) m with hok | hcon
  · exact hok
  · exfalso
    obtain ⟨-, -, hlt, hdeep, hmin⟩ := h
    have hcm : c + m ≤ t := by omega
    have heq : entry T 0 (c + m) = entry T 0 c := hper c hc hcm
    rcases eq_or_lt_of_le hcm with h1 | h1
    · rw [h1] at heq; omega
    · have hmn := hmin (c + m) ⟨by omega, h1⟩
      omega

/-- 同じことを `srow = 0` の親について述べた形。 -/
theorem parent_dist_lt_of_periodic0 {T : TrioSeq} {a m t : ℕ} (hm : 0 < m)
    (hper : ∀ x, a ≤ x → x + m ≤ t → entry T 0 (x + m) = entry T 0 x)
    (hs : srow T t = 0) (hpar : hasParent T (srow T t) t)
    (hc : a ≤ parent T (srow T t) t) :
    t - parent T (srow T t) t < m := by
  have h1 := parent_nextR hpar
  rw [hs] at h1 hc ⊢
  rw [nextR, if_pos rfl] at h1
  exact window_lt_of_periodic0 hm hper hc h1

/-- 写しの列は `Q` を `|Q|` 周期で読む（前提なし）。 -/
theorem getD_copies_mod {Q : TrioSeq} :
    ∀ (n x : ℕ), x < n * Q.length →
      ((List.range n).flatMap fun _ => Q).getD x (0, 0, 0) = Q.getD (x % Q.length) (0, 0, 0) := by
  intro n
  induction n with
  | zero => intro x hx; simp at hx
  | succ n ih =>
    intro x hx
    have hsplit : ((List.range (n + 1)).flatMap fun _ => Q)
        = Q ++ ((List.range n).flatMap fun _ => Q) := by
      rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    rw [hsplit]
    rcases Nat.lt_or_ge x Q.length with hlt | hge
    · rw [getD_append_left hlt, Nat.mod_eq_of_lt hlt]
    · obtain ⟨y, rfl⟩ : ∃ y, x = Q.length + y := ⟨x - Q.length, by omega⟩
      rw [getD_append_right', Nat.add_mod_left]
      refine ih y ?_
      simp only [Nat.succ_mul] at hx
      omega

/-- `A ++ Q^n` の行 0 は、接頭辞より右で `|Q|` 周期（前提なし）。 -/
theorem entry_copies_periodic {A Q : TrioSeq} {n x : ℕ}
    (hx : A.length ≤ x) (hlt : x + Q.length < A.length + n * Q.length) :
    entry (A ++ (List.range n).flatMap fun _ => Q) 0 (x + Q.length)
      = entry (A ++ (List.range n).flatMap fun _ => Q) 0 x := by
  have hE : ∀ (M : TrioSeq) (y : ℕ), entry M 0 y = (M.getD y (0, 0, 0)).1 := fun _ _ => rfl
  have e1 : ∀ y, A.length ≤ y → y < A.length + n * Q.length →
      entry (A ++ (List.range n).flatMap fun _ => Q) 0 y
        = entry Q 0 ((y - A.length) % Q.length) := by
    intro y hy hy2
    obtain ⟨z, rfl⟩ : ∃ z, y = A.length + z := ⟨y - A.length, by omega⟩
    rw [show A.length + z - A.length = z from by omega, entry_append_right, hE, hE,
      getD_copies_mod n z (by omega)]
  rw [e1 (x + Q.length) (by omega) hlt, e1 x hx (by omega)]
  congr 1
  have hxx : x + Q.length - A.length = (x - A.length) + Q.length := by omega
  rw [hxx, Nat.add_mod_right]

/-- ★★★ **(L-ROT) の答え（`srow = 0`）**: 親が接頭辞 `A` の外にあるなら、
窓の長さは `|Q|` 未満。⟹ **良い枝では次の `Q` が真に短い**。 -/
theorem good_window_lt_of_copies {A Q : TrioSeq} {n t : ℕ} (hm : 0 < Q.length)
    (ht : t < A.length + n * Q.length)
    (hs : srow (A ++ (List.range n).flatMap fun _ => Q) t = 0)
    (hpar : hasParent (A ++ (List.range n).flatMap fun _ => Q)
      (srow (A ++ (List.range n).flatMap fun _ => Q) t) t)
    (hc : A.length ≤ parent (A ++ (List.range n).flatMap fun _ => Q)
      (srow (A ++ (List.range n).flatMap fun _ => Q) t) t) :
    t - parent (A ++ (List.range n).flatMap fun _ => Q)
      (srow (A ++ (List.range n).flatMap fun _ => Q) t) t < Q.length :=
  parent_dist_lt_of_periodic0 hm
    (fun x hx hxt => entry_copies_periodic hx (by omega)) hs hpar hc

/-! ### §291 (L-OUT): 残差は「塔の根の行 0」を真に下げる

**(L-OUT)** を調べる途中で出た、**2 行で出る新しい量**。
`nextrel0` の最小性は「間の列はすべて的以上」なので、
**親は、親と的の間にあるどの列よりも真に浅い**。
⟹ 特に **残差（親が接頭辞 `A` の中）なら、親は塔の根より真に浅い**。
⟹ ⟹ **残差のあとの新しい塔の根の行 0 は、真に小さくなる**（0 で下に有界）。 -/

/-- **親は、親と的の間のどの列よりも真に浅い**（前提なし、2 行）。 -/
theorem parent_lt_of_between {T : TrioSeq} {c r t : ℕ}
    (h : nextrel0 T c t) (hcr : c < r) (hrt : r < t) :
    entry T 0 c < entry T 0 r := by
  have h1 := h.2.2.2.2 r ⟨hcr, hrt⟩
  have h2 := h.2.2.2.1
  omega

/-- ★★★ **残差なら、親は塔の根より真に浅い**。

`T = A ++ (塔)`、親 `c < |A|`、的 `t` は塔の中（`|A| < t`）のとき、
新しい塔の根 `T[c]` の行 0 は、古い塔の根 `T[|A|]` の行 0 より真に小さい。
⟹ **残差のたびに「塔の根の行 0」が真に減る**（`n` に依らない、0 で下に有界）。 -/
theorem residue_root_lt {A P : TrioSeq} {c t : ℕ}
    (h : nextrel0 (A ++ P) c t) (hc : c < A.length) (ht : A.length < t) :
    entry (A ++ P) 0 c < entry P 0 0 := by
  have hr : entry (A ++ P) 0 A.length = entry P 0 0 := by
    have : A.length = A.length + 0 := by omega
    rw [this, entry_append_right]
  rw [← hr]
  exact parent_lt_of_between h hc ht

/-! ### §293 `nu`（相異なる行 0 の値の個数）が両枝で非増加な理由 —— 型で 3 行

team-lead の (CAND-V)。`PrefixCopies`（`d = e = 0`）では **持ち上げが無い**ので、
`A ++ Q^n` のどの列も **`A ++ Q` の列そのもの**。
⟹ 接頭辞 `A' = T.take c` も窓 `V = (T.drop c).take (t−c)` も `T` の部分列なので、
⟹ **`A' ++ V` の行 0 の値は `A ++ Q` の値の部分集合** ⟹ **`nu` は両枝で非増加**。

⚠ **これは「非増加」だけである。「いつ減るか」は別問題**（R2 が測っている）。
⚠ そして **`d > 0` では偽**（持ち上げが新しい行 0 の値を作る。実測 増 72〜79%）。 -/

/-- **`A ++ Q^n` のどの列も `A ++ Q` の列**（前提なし）。 -/
theorem mem_of_mem_copies {A Q : TrioSeq} {n : ℕ} {q : ℕ × ℕ × ℕ}
    (h : q ∈ A ++ (List.range n).flatMap fun _ => Q) : q ∈ A ++ Q := by
  rcases List.mem_append.mp h with hq | hq
  · exact List.mem_append.mpr (Or.inl hq)
  · rw [List.mem_flatMap] at hq
    obtain ⟨-, -, hq⟩ := hq
    exact List.mem_append.mpr (Or.inr hq)

/-- ★★★ **接頭辞と窓を合わせても、新しい列は出ない**（`d = e = 0` の族、前提なし）。
⟹ **`nu`（相異なる行 0 の値の個数）は両枝で非増加**。 -/
theorem mem_of_mem_prefix_window {A Q : TrioSeq} {n c t : ℕ} {q : ℕ × ℕ × ℕ}
    (h : q ∈ (A ++ (List.range n).flatMap fun _ => Q).take c
          ++ (((A ++ (List.range n).flatMap fun _ => Q).drop c).take (t - c))) :
    q ∈ A ++ Q := by
  refine mem_of_mem_copies (A := A) (Q := Q) (n := n) ?_
  rcases List.mem_append.mp h with hq | hq
  · exact List.mem_of_mem_take hq
  · exact List.mem_of_mem_drop (List.mem_of_mem_take hq)

/-! ### §294 (L-MIN2) 「直前が親」は最小形に帰着しない —— `srow != 0` が `d0 > 0` を強制する

team-lead の (L-MIN2)。「的の直前の列が親」なら **窓は 1 列**（`|V| = 1`）で、
H12 の最小形（`A ++ replicate n q`）に見える。⟹ ⛔ **だが `WSnocOpen1` では帰着しない**。

理由: `WSnocOpen1` は **`srow != 0`** を仮定する。`oper` の `d0` は
`if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0` なので、`srow != 0` なら
`d0 = entry T 0 t - entry T 0 c`。そして **`nextrel1` は `le0 c t` を、`nextrel2` は
`le1 c t` を含む**ので、`c != t` から **`entry T 0 c < entry T 0 t`** ⟹ **`d0 > 0`**。

⟹ ★ 後継は `A ++ replicate m q`（持ち上げ 0）ではなく、
**`A ++ [q, q+(d0,d1,0), q+(2d0,2d1,0), ...]`（1 列ずつ持ち上がる塔）**。
⟹ ⚠ これは私の §291 の反例（`Q = [(1,0,0),(2,1,0)]`、omega の塔）そのものの形であり、
**どの自然数値測度も同時に不変にする**族である。 -/

/-- ★★★ **`srow != 0` の親は、行 0 でも真に浅い** ⟹ **`oper` の `d0` は正**。 -/
theorem entry0_lt_of_nextR_srow_ne_zero {T : TrioSeq} {i c t : ℕ}
    (hi : i ≠ 0) (h : nextR T i c t) : entry T 0 c < entry T 0 t := by
  rw [nextR, if_neg hi] at h
  by_cases h1 : i = 1
  · rw [if_pos h1] at h
    exact entry0_lt_of_le0_ne h.2.2.2.2.1 (by have := h.2.2.1; omega)
  · rw [if_neg h1] at h
    exact entry0_lt_of_le0_ne (le0_of_le1' h.2.2.2.2.1) (by have := h.2.2.1; omega)

/-- 同じことを `srow` で述べた形（`WSnocOpen1` の場面）。 -/
theorem entry0_lt_parent_of_srow_ne_zero {T : TrioSeq} {t : ℕ}
    (hs : srow T t ≠ 0) (hp : hasParent T (srow T t) t) :
    entry T 0 (parent T (srow T t) t) < entry T 0 t :=
  entry0_lt_of_nextR_srow_ne_zero hs (parent_nextR hp)

/-! ### §295 `srow = 2` は `d1 > 0` を強制する —— 「`d1 = 0` だから行 1 は全写しで同じ」は `srow = 1` のときだけ

§294 の行 1 版。`oper` の `d1` は `if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0` なので、
**`srow = 2` なら `d1 = entry T 1 t - entry T 1 c`**。そして `nextrel2` は `le1 c t` を含むので
**`d1 > 0`**。⟹ **`srow = 2` の塔では、行 1 が写しごとに上がります**。

⚠ ですから「`d1 = 0` なので行 1 は全写しで同じ ⟹ `srow >= 1` なら常に残差」は
**`srow = 1`（`d1 = 0`）のときだけ**正しい。実測（分母 4,424,454、1 段目が `srow != 0`、直前が親）:

    1 段目 srow=1（d1=0）／後継 srow=0 ⟹ 親は塔     1,464,750
    1 段目 srow=1（d1=0）／後継 srow=1 ⟹ 親は接頭辞   279,384  ✅
    1 段目 srow=1（d1=0）／後継 srow=2 ⟹ 親は接頭辞   239,070  ✅
    1 段目 srow=2（d1>0）／後継 srow=1 ⟹ **親は塔**  2,441,250  ⛔

⟹ `d1 = 0` の 3 行は「`srow >= 1` なら残差」を支持するが、
   **`d1 > 0` の 1 行が反例**（例外 0 ではなく 2,441,250 件）。 -/

/-- ★★★ **`srow = 2` の親は、行 1 でも真に浅い** ⟹ **`oper` の `d1` は正**。 -/
theorem entry1_lt_of_nextR_two {T : TrioSeq} {c t : ℕ}
    (h : nextR T 2 c t) : entry T 1 c < entry T 1 t := by
  rw [nextR, if_neg (by decide), if_neg (by decide)] at h
  exact H12Export.entry1_lt_of_le1_ne h.2.2.2.2.1 (by have := h.2.2.1; omega)

/-! ### §296 (L-TIE) 行 1 のタイは `lev` の帳簿を壊さない —— 塔の根は `Q` の根そのもの

team-lead の (L-TIE)。H12 の `tie_below_root_after_lift`（`Lift1` は錐の外＝タイの列を
置き去りにするので、持ち上げ後にタイの列は根より行 1 が真に低い）が `mTower` でも起きるか。

⟹ ✅ **段の帳簿は壊れません**。`mem_Wself_iff : M ∈ W u ↔ M ∈ Wself ∧ lev M 0 ≤ u` の
側条件は **根（添字 0）だけ**を見る。そして `mTower` のブロック 0 は `k = 0` なので
持ち上げ量 0 ⟹ **塔の根は `Q` の根そのもの**。

⚠ 20 回目の重複: **`mTower_entry{0,1,2}_root`（`L105Cap:10487 / 10632 / 13821`）が
既にこれを言っていた**（`k = 0` を代入するだけ）。以下は `lev` への言い換えのみ。

⚠ ただし **ブロック `k >= 1` の中ではタイの列が根より行 1 で低くなる**（H12 の指摘どおり）。
それは `nextrel1` の形に効くので `oper` の解析では効くが、**段 `u` の帳簿には効かない**。 -/

/-- ★★★ **段 `u` は塔で変わらない**（`mem_Wself_iff` の側条件）。 -/
theorem lev_mTower_root {Q : TrioSeq} (hQ : 0 < Q.length) (d e n : ℕ) (hn : 0 < n) :
    lev (mTower Q d e n) 0 = lev Q 0 := by
  have h1 := mTower_entry1_root (Q := Q) (d := d) (e := e) (n := n) (k := 0) hn hQ
  have h2 := mTower_entry2_root (Q := Q) (d := d) (e := e) (n := n) (k := 0) hn hQ
  simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero] at h1 h2
  unfold lev
  rw [h1, h2]

/-! ### §297 残差 B（`MTowerOrphan`）は `srow >= 1` だけ —— `srow = 0` の孤児は起きない

`L105Cap:6111` の残差 B は「`Q` の末尾列が段内で孤児（`¬ HasParentInBlock Q`）」。
`HasParentInBlock N = hasParent N (srow N (|N|-1)) (|N|-1)` なので、
`srow = 0` の孤児は「行 0 の親が無い」ことを意味する。

⟹ ⛔ **それは `hr0 Q` の下では起きない**（H12 の `hasParent0_of_hr0`:
根が祖先なので `j >= 1` の列は必ず行 0 の親を持つ）。
⟹ ★ そして残差 B は `2 <= |Q|` を仮定するので `|Q| - 1 >= 1`。
⟹ ⟹ ★★★ **残差 B は `srow >= 1` の場合だけ**に絞れる。 -/

/-- ★★★ **`hr0` ∧ `2 <= |Q|` の下では、段内の孤児は `srow >= 1` に限る**。 -/
theorem srow_ne_zero_of_orphan {Q : TrioSeq} (hbig : 2 ≤ Q.length)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (horph : ¬ L53.HasParentInBlock Q) : srow Q (Q.length - 1) ≠ 0 := by
  intro hs
  refine horph ?_
  rw [L53.HasParentInBlock, hs]
  exact H12Export.hasParent0_of_hr0 hr0 (by omega) (by omega)

/-- **残差 B を `srow >= 1` に制限した形**。 -/
def MTowerOrphan1 : Prop :=
  ∀ (u d e n : ℕ) (Q : TrioSeq), Q ∈ W u → 2 ≤ Q.length →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
    ¬ L53.HasParentInBlock Q → srow Q (Q.length - 1) ≠ 0 →
    mTower Q d e n ∈ W u

/-- ★★★ **残差 B は `srow >= 1` だけで足りる**。 -/
theorem mTowerOrphan_of_orphan1 (h : MTowerOrphan1) : L105.MTowerOrphan := by
  intro u d e n Q hQ hbig hs horph
  refine h u d e n Q hQ hbig hs horph ?_
  exact srow_ne_zero_of_orphan hbig (fun l hl0 hl => hs l (by omega) hl) horph

/-! ### §298 残差 C（`MTowerSingle`）は証明できます —— 行 2 が一定だから

`MTowerSingle`（`L105Cap:6117`）: `Q ∈ W u` ∧ `|Q| = 1` ⟹ `mTower Q d e n ∈ W u`。

`|Q| = 1` なら **`Q` の行 2 は 1 つの値 `c`** で、`shiftr01` も `Lift1` も行 2 を変えないので
**塔の全列の行 2 が `c`**。⟹ 場合分けは 2 つだけ:

    `c = 0` ⟹ **`mTower_mem_of_zeroRow2`**（`L105Cap:5781`、緑）
    `c >= 1` ⟹ **`constRow2_mem_W_aux`**（`L105Cap:2622`、緑）＋ 段は `lev_mTower_root`（§296）

⟹ ★ どちらも既に緑でした。⟹ **残差 C は閉じます**。 -/

/-- 塔は行 2 を変えない（`shiftr01` も `Lift1` も行 2 に触らない）。 -/
theorem entry2_mTower {Q : TrioSeq} (hQ1 : 0 < Q.length) (d e n i : ℕ)
    (hi : i < (mTower Q d e n).length) :
    entry (mTower Q d e n) 2 i = entry Q 2 (i % Q.length) := by
  have hlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  rw [hlen] at hi
  have hk : i / Q.length < n := by
    rw [Nat.div_lt_iff_lt_mul hQ1]; omega
  have hq : i % Q.length < Q.length := Nat.mod_lt _ hQ1
  have hidx : i = (i / Q.length) * Q.length + i % Q.length := by
    rw [Nat.div_add_mod']
  conv_lhs => rw [hidx]
  rw [mTower_entry hk hq, entry2_Lift1, entry2_shiftr01]

/-- ★★★ **塔の全列の行 2 は、`Q` の行 2 が一定ならその値**。 -/
theorem row2_const_mTower {Q : TrioSeq} {c : ℕ} (hQ1 : 0 < Q.length)
    (hc : ∀ q, q < Q.length → entry Q 2 q = c) (d e n : ℕ) :
    ∀ p ∈ mTower Q d e n, p.2.2 = c := by
  intro p hp
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  have h1 : entry (mTower Q d e n) 2 i = p.2.2 := by
    unfold entry
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hpi]
    simp
  rw [← h1, entry2_mTower hQ1 d e n i hi]
  exact hc _ (Nat.mod_lt _ hQ1)

/-- ★★★★★ **残差 C（`MTowerSingle`）は既存の 2 本で閉じる**。 -/
theorem mTowerSingle_holds : L105.MTowerSingle := by
  intro u d e n Q hQ h1
  obtain ⟨q0, rfl⟩ : ∃ q0, Q = [q0] := List.length_eq_one_iff.mp h1
  have hQ1 : 0 < ([q0] : TrioSeq).length := by simp
  have hc : ∀ q, q < ([q0] : TrioSeq).length → entry [q0] 2 q = q0.2.2 := by
    intro q hq
    have hq0 : q = 0 := by simpa using hq
    subst hq0
    simp [entry]
  have hall := row2_const_mTower (c := q0.2.2) hQ1 hc d e n
  rcases Nat.eq_zero_or_pos q0.2.2 with hz | hpos
  · refine L105.mTower_mem_of_zeroRow2 (fun p hp => ?_) hQ d e n
    have : p = q0 := by simpa using hp
    rw [this, hz]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa [mTower] using W_nil u
    · refine L105.constRow2_mem_W_aux hpos (mTower [q0] d e n).length _ u (le_refl _) hall ?_
      rw [lev_mTower_root hQ1 d e n hn]
      exact lev_root_le_of_mem_W hQ (by simp)

/-! ### §299 (L-B1) 残差 A・B は「行 2 が一定でない `Q`」だけで足りる

⚠⚠ **22 回目の重複、しかも自分のファイルの中でした**: `mTower_mem_of_constRow2`
（**`L106:936`**、私が今日の前半に書いたもの）が既に
**「`Q` の行 2 が定数 ⟹ 塔は `W u`」**を言っている。⟹ §298 はこれを使えば 3 行だった。

⟹ ★ ですから **`|Q| = 1` は本質ではなく、「行 2 が一定」が本質**だった。
⟹ ⟹ ★★★ そして **`|Q|` に依らない**ので、**残差 A・B の両方**で
「行 2 が一定」の場合が消える。
⟹ ⟹ ⟹ ★ `MTowerClosedRow2` は既に「`∃ p ∈ Q, 0 < p.2.2`」に絞っているので、
**残るのは「行 2 に 0 の列と正の列が両方ある `Q`」だけ**。 -/

/-- **残差 B を「行 2 が一定でない `Q`」に制限した形**。 -/
def MTowerOrphan2 : Prop :=
  ∀ (u d e n : ℕ) (Q : TrioSeq), Q ∈ W u → 2 ≤ Q.length →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
    ¬ L53.HasParentInBlock Q → srow Q (Q.length - 1) ≠ 0 →
    (¬ ∃ c, ∀ p ∈ Q, p.2.2 = c) →
    mTower Q d e n ∈ W u

/-- ★★★ **残差 B は「行 2 が一定でない `Q`」だけで足りる**。 -/
theorem mTowerOrphan_of_orphan2 (h : MTowerOrphan2) : L105.MTowerOrphan := by
  intro u d e n Q hQ hbig hs horph
  by_cases hconst : ∃ c, ∀ p ∈ Q, p.2.2 = c
  · obtain ⟨c, hc⟩ := hconst
    exact mTower_mem_of_constRow2 hc hQ d e n
  · exact h u d e n Q hQ hbig hs horph
      (srow_ne_zero_of_orphan hbig (fun l hl0 hl => hs l (by omega) hl) horph) hconst

/-- **残差 A を「行 2 が一定でない `Q`」に制限した形**。 -/
def MTowerStepAll2 : Prop :=
  ∀ (u d e : ℕ) (Q : TrioSeq), Q ∈ W u → 2 ≤ Q.length →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
    L53.HasParentInBlock Q →
    (¬ ∃ c, ∀ p ∈ Q, p.2.2 = c) →
    L105.MTowerStep u Q d e

/-! ⚠ **残差 A の「行 2 が一定」の場合は、まだ 1 手足りません**。
`MTowerStep u Q d e = ∀ n m, 1 <= m → mTower Q d e n ++ shiftr01 (d*n) 0 ((Lift1 Q (e*n))⟦m⟧) ∈ W u`
は**連結**なので、`mTower_mem_of_constRow2` ではなく
**`constRow2_mem_W`（`L105Cap:2686`、任意の列に効く）**を直に当てるべきである。
⟹ ★ 要るのは **「`oper` は行 2 の値を保つ」**（`oper` は行 0・行 1 しか持ち上げない）だけ。
⟹ ⚠ その補題をまだ書いていないので、ここは開けておく。 -/

/-! ### §300 `oper` は行 2 の値を変えない —— 残差 A の「行 2 が一定」の場合が閉じる

`oper` の定義（`Trio.lean:98`）の第 3 成分は **`entry M 2 j` そのまま**で、
枝は `M` ／ `Pred M` ／ `M.take j0 ++ (添字 `j ∈ [j0, j1)` の写し)` の 3 つしかない。
⟹ ★ **どの列の行 2 も `M` のどれかの列の行 2** ⟹ **一定なら一定**。 -/

/-- `M` の行 2 が定数なら、添字でも定数。 -/
theorem entry2_const_of_mem {M : TrioSeq} {c : ℕ} (h : ∀ p ∈ M, p.2.2 = c)
    {j : ℕ} (hj : j < M.length) : entry M 2 j = c := by
  have hm : M[j] ∈ M := List.getElem_mem hj
  have : entry M 2 j = (M[j]).2.2 := by
    unfold entry
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp
  rw [this]
  exact h _ hm

/-- `Pred M` の列は `M` の列（前提なし）。 -/
theorem mem_of_mem_Pred {M : TrioSeq} {p : ℕ × ℕ × ℕ} (hp : p ∈ Pred M) : p ∈ M := by
  rw [Pred] at hp
  split_ifs at hp with hle
  · exact hp
  · exact List.dropLast_subset M hp

/-- ★★★ **`oper` は行 2 の値を変えない**（前提なし）。 -/
theorem constRow2_oper {M : TrioSeq} {c : ℕ} (h : ∀ p ∈ M, p.2.2 = c) (n : ℕ) :
    ∀ p ∈ M⟦n⟧, p.2.2 = c := by
  intro p hp
  rw [oper] at hp
  simp only at hp
  split_ifs at hp
  all_goals try exact h p hp
  all_goals try exact h p (mem_of_mem_Pred hp)
  all_goals
    rcases List.mem_append.mp hp with hq | hq
    · exact h p (List.take_subset _ _ hq)
    · rw [List.mem_flatMap] at hq
      obtain ⟨k, -, hk⟩ := hq
      rw [List.mem_map] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      have hjlt : j < M.length := by
        rw [List.mem_range'] at hj
        omega
      simpa using entry2_const_of_mem h hjlt

/-! ### §301 ★★★ `MTowerClosedS` は「行 2 が一定でない `Q`」だけで出る

`mTower_mem_of_constRow2`（`L106:936`）は `|Q|` にも `HasParentInBlock` にも依らない。
⟹ ★ ですから **残差 3 本に割る前に、まず「行 2 が一定か」で割る**のが正しい。
⟹ ⟹ ★★★ **一定なら無条件に閉じる** ⟹ **残るのは一定でない `Q` だけ**。

そして `MTowerClosedRow2`（`L105Cap:5794`）は既に「`∃ p ∈ Q, 0 < p.2.2`」に絞っているので、
両方合わせると **残核は「行 2 に 0 の列と正の列が両方ある `Q`」**である。
（`z <= 1` の断片では ⟹ **`z = 0` の列と `z = 1` の列が両方ある `Q`**。） -/

/-- **`MTowerClosedS` を「行 2 が一定でない `Q`」に制限した形**。 -/
def MTowerClosedNonconst : Prop :=
  ∀ (u d e n : ℕ) (Q : TrioSeq), Q ∈ W u →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
    (¬ ∃ c, ∀ p ∈ Q, p.2.2 = c) →
    mTower Q d e n ∈ W u

/-- ★★★★★ **行 2 が一定なら無条件に閉じるので、残核は一定でない `Q` だけ**。 -/
theorem mTowerClosedS_of_nonconst (h : MTowerClosedNonconst) : L105.MTowerClosedS := by
  intro u d e n Q hQ hs
  by_cases hconst : ∃ c, ∀ p ∈ Q, p.2.2 = c
  · obtain ⟨c, hc⟩ := hconst
    exact mTower_mem_of_constRow2 hc hQ d e n
  · exact h u d e n Q hQ hs hconst

/-- ⟹ **`Final` まで通ります**（`TRIO_terminates_of_mTowerClosedS` に食わせるだけ）。 -/
theorem mTowerClosedS_holds_of_nonconst (h : MTowerClosedNonconst) :
    L105.MTowerClosedS := mTowerClosedS_of_nonconst h

/-! ### §302 (L-NC1) `z <= 1` では、行 2 の親は「`z = 0` の列」しかない

残核は「行 2 に 0 の列と 1 の列が両方ある `Q`」（§301）。そこで `srow = 2` の親がどこかを見る。

`nextrel2 M c t` は **`entry M 2 c < entry M 2 t`** を要求する。`z <= 1` の断片では
値は 0 か 1 しかないので ⟹ **`entry M 2 c = 0` かつ `entry M 2 t = 1`**。
そして最小性 `∀ j, c < j ∧ le1 M j t → entry M 2 t ≤ entry M 2 j` は
⟹ **`(c, t)` の `le1` 祖先の行 2 はすべて 1**。

⟹ ★★★ ですから **`z = 0` の列の位置が、行 2 の親の位置を完全に決めます**
（`le1` の順で `t` から遡って最初の `z = 0` の列）。 -/

/-- ★★★ **`z <= 1` なら、行 2 の親は `z = 0`、的は `z = 1`**（前提なし）。 -/
theorem row2_parent_zero_of_zle1 {M : TrioSeq} {c t : ℕ}
    (hz : ∀ j, j < M.length → entry M 2 j ≤ 1) (h : nextrel2 M c t) :
    entry M 2 c = 0 ∧ entry M 2 t = 1 := by
  have hct : entry M 2 c < entry M 2 t := h.2.2.2.1
  have ht : entry M 2 t ≤ 1 := hz t h.2.1
  exact ⟨by omega, by omega⟩

/-- ★★★ **そして間の `le1` 祖先は、すべて `z = 1`**（前提なし）。 -/
theorem row2_between_one_of_zle1 {M : TrioSeq} {c t j : ℕ}
    (hz : ∀ i, i < M.length → entry M 2 i ≤ 1) (h : nextrel2 M c t)
    (hj : c < j) (hle : le1 M j t) : entry M 2 j = 1 := by
  have hmin := h.2.2.2.2.2 j ⟨hj, hle⟩
  have h1 := (row2_parent_zero_of_zle1 hz h).2
  have hjl : entry M 2 j ≤ 1 := hz j hle.1
  omega

/-- ⟹ **`z = 0` の列が無ければ、行 2 の親は存在しない**（＝ 孤児）。 -/
theorem no_row2_parent_of_all_one {M : TrioSeq} {t : ℕ}
    (hone : ∀ j, j < M.length → entry M 2 j = 1) : ¬ ∃ c, nextrel2 M c t := by
  rintro ⟨c, h⟩
  have hz : ∀ j, j < M.length → entry M 2 j ≤ 1 := fun j hj => le_of_eq (hone j hj)
  have h0 := (row2_parent_zero_of_zle1 hz h).1
  have h1 := hone c h.1
  omega

/-- ★★★★★ **残差（行 2 の孤児）の特徴づけ**: `z <= 1` なら
「**`z = 0` の列がどれも末尾の `le1` 錐に入っていない**」⟹ **行 2 の親は無い**。 -/
theorem orphan_row2_of_zeros_outside_cone {M : TrioSeq} {t : ℕ}
    (hz : ∀ j, j < M.length → entry M 2 j ≤ 1)
    (h : ∀ c, c < M.length → entry M 2 c = 0 → ¬ le1 M c t) :
    ¬ hasParent M 2 t := by
  rintro ⟨c, hc, -⟩
  rw [nextR, if_neg (by decide), if_neg (by decide)] at hc
  exact h c hc.1 (row2_parent_zero_of_zle1 hz hc).1 hc.2.2.2.2.1

/-! ### §303 (L-NC1 続) `z <= 1` では、行 2 の親の有無は「錐の中の `z = 0` の列」で決まる

§302 の逆向き。`z <= 1` かつ `entry M 2 t = 1` のとき

    **`hasParent M 2 t`  <=>  `∃ c < t, entry M 2 c = 0 ∧ le1 M c t`**

が成り立つ。⟸ は **`le1` 錐の中の `z = 0` の列のうち、いちばん右のもの**を取れば
最小性が自動的に通る（それより右の `le1` 祖先は `z = 1` しかないので）。
一意性も同じ理由で出る（2 つあれば、左のものの最小性が右のもので破れる）。

⟹ ★★★ **残差（行 2 の孤児）⟺ 錐の中に `z = 0` の列が 1 本も無い**。 -/

/-- `nextR M 2 = nextrel2 M`（前提なし）。 -/
theorem nextR_two (M : TrioSeq) (a b : ℕ) : nextR M 2 a b = nextrel2 M a b := by
  simp [nextR]

/-- `le1` の鎖は添字を増やさない向き（`j <= t`）。 -/
theorem le1_index_le {M : TrioSeq} {j t : ℕ} (h : le1 M j t) : j ≤ t := by
  refine Relation.ReflTransGen.head_induction_on h.2.2 (le_refl _) ?_
  intro a b hab _ ih
  have := hab.2.2.1
  omega

/-- `nextrel2` の始点は一意（`z <= 1` の下で、`z = 0` の列は高々 1 本しか候補にならない）。 -/
theorem nextrel2_unique_of_zle1 {M : TrioSeq} {t c c' : ℕ}
    (hz : ∀ j, j < M.length → entry M 2 j ≤ 1)
    (h : nextrel2 M c t) (h' : nextrel2 M c' t) : c = c' := by
  by_contra hne
  have hz0 := (row2_parent_zero_of_zle1 hz h).1
  have hz0' := (row2_parent_zero_of_zle1 hz h').1
  rcases Nat.lt_or_ge c c' with hlt | hge
  · have := row2_between_one_of_zle1 hz h hlt h'.2.2.2.2.1
    omega
  · have hlt' : c' < c := by omega
    have := row2_between_one_of_zle1 hz h' hlt' h.2.2.2.2.1
    omega

/-- ★★★★★ **行 2 の親があること ⟺ 錐の中に `z = 0` の列があること**（`z <= 1`）。 -/
theorem hasParent2_iff_zero_in_cone {M : TrioSeq} {t : ℕ}
    (hz : ∀ j, j < M.length → entry M 2 j ≤ 1) (ht : t < M.length)
    (ht1 : entry M 2 t = 1) :
    hasParent M 2 t ↔ ∃ c, c < t ∧ entry M 2 c = 0 ∧ le1 M c t := by
  classical
  constructor
  · rintro ⟨c, hc, -⟩
    rw [nextR_two] at hc
    exact ⟨c, hc.2.2.1, (row2_parent_zero_of_zle1 hz hc).1, hc.2.2.2.2.1⟩
  · rintro ⟨c0, hc0t, hc0z, hc0le⟩
    set P : ℕ → Prop := fun c => entry M 2 c = 0 ∧ le1 M c t with hP
    have hPc0 : P c0 := ⟨hc0z, hc0le⟩
    set g : ℕ := Nat.findGreatest P t with hg
    have hgP : P g := Nat.findGreatest_spec (le_of_lt hc0t) hPc0
    have hgt : g < t := by
      rcases Nat.lt_or_ge g t with h | h
      · exact h
      · exfalso
        have hgt' : g = t := le_antisymm (Nat.findGreatest_le t) h
        rw [hgt'] at hgP
        have := hgP.1
        omega
    have hkey : nextrel2 M g t := by
      refine ⟨hgP.2.1, ht, hgt, by rw [hgP.1]; omega, hgP.2, ?_⟩
      intro j hj
      have hjt : j ≤ t := le1_index_le hj.2
      rcases Nat.eq_or_lt_of_le hjt with rfl | hjlt
      · omega
      · have hnP : ¬ P j := Nat.findGreatest_is_greatest hj.1 (le_of_lt hjlt)
        have hjz : entry M 2 j ≤ 1 := hz j hj.2.1
        have hj0 : entry M 2 j ≠ 0 := by
          intro h0
          exact hnP ⟨h0, hj.2⟩
        omega
    refine ⟨g, by show nextR M 2 g t; rw [nextR_two]; exact hkey, ?_⟩
    intro c' hc'
    have hc'' : nextrel2 M c' t := by
      have : nextR M 2 c' t := hc'
      rwa [nextR_two] at this
    exact nextrel2_unique_of_zle1 hz hc'' hkey

/-! ### §304 `z <= 1` は塔で保たれる —— §302 / §303 を塔に持ち込むための接着剤

§302 / §303 は `∀ j < |M|, entry M 2 j <= 1` を前提にしている。
塔は行 2 を変えない（§298 `entry2_mTower`）ので、この前提は塔でもそのまま成り立つ。
⟹ ★ ですから **残核の `Q` に対して、`mTower Q d e n` にも §302 / §303 が使える**。 -/

/-- ★★★ **`z <= 1` は塔で保たれる**（前提なし）。 -/
theorem zle1_mTower {Q : TrioSeq} (hQ1 : 0 < Q.length)
    (hz : ∀ j, j < Q.length → entry Q 2 j ≤ 1) (d e n : ℕ) :
    ∀ j, j < (mTower Q d e n).length → entry (mTower Q d e n) 2 j ≤ 1 := by
  intro j hj
  rw [entry2_mTower hQ1 d e n j hj]
  exact hz _ (Nat.mod_lt _ hQ1)

/-- ⟹ **塔の中でも「行 2 の親 ⟺ 錐の中の `z = 0` の列」**（`z <= 1`）。 -/
theorem hasParent2_mTower_iff {Q : TrioSeq} {t : ℕ} (hQ1 : 0 < Q.length)
    (hz : ∀ j, j < Q.length → entry Q 2 j ≤ 1) (d e n : ℕ)
    (ht : t < (mTower Q d e n).length) (ht1 : entry (mTower Q d e n) 2 t = 1) :
    hasParent (mTower Q d e n) 2 t ↔
      ∃ c, c < t ∧ entry (mTower Q d e n) 2 c = 0 ∧ le1 (mTower Q d e n) c t :=
  hasParent2_iff_zero_in_cone (zle1_mTower hQ1 hz d e n) ht ht1

/-- ⟹ **塔の中の `z = 0` の位置は、`Q` の中の `z = 0` の位置で決まる**（周期）。 -/
theorem row2_zero_mTower_iff {Q : TrioSeq} (hQ1 : 0 < Q.length) (d e n c : ℕ)
    (hc : c < (mTower Q d e n).length) :
    entry (mTower Q d e n) 2 c = 0 ↔ entry Q 2 (c % Q.length) = 0 := by
  rw [entry2_mTower hQ1 d e n c hc]

/-! ### §305 「一度も親を持たない塔」は無料 —— `n` の帰納は既に書かれていた

⚠⚠ **24 回目の「既にありました」**: `prefixTowerClosed_of_snocStepPar`（`L105Cap:11859`）が
**snoc 鎖の `n` の帰納をすでに回しており、孤児は `snoc_orphan_W` で片づいている**。
⟹ ★ 残っているのは **「足す列が親を持つ」場合だけ**。

⟹ ★★★ ですから **「塔のどの snoc でも親が無い」なら、`hstep` は空虚に満たされ、無料**である。
（(L-MIN4) の実測では、`srow = 1` の残核 8,424 手すべてがこの形だった。） -/

/-- ★★★★★ **一度も親を持たない塔は無料**（`hstep` が空虚）。 -/
theorem mTower_mem_of_never_parent {u : ℕ} {A Q : TrioSeq} {d e : ℕ} (hA : A ∈ W u)
    (hnp : ∀ (n j : ℕ), j < Q.length →
      ¬ hasParent (A ++ mTower Q d e n
            ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
          (srow (A ++ mTower Q d e n
            ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
            (A ++ mTower Q d e n
              ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length)
          (A ++ mTower Q d e n
            ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length)
    (hAne : A ≠ []) :
    ∀ n, A ++ mTower Q d e n ∈ W u := by
  refine L105.prefixTowerClosed_of_snocStepPar hA ?_
  intro n j hj hpar _
  refine absurd (hpar.resolve_right ?_) (hnp n j hj)
  intro hnil
  have h1 : A = [] := by
    have := congrArg List.length hnil
    simp only [List.length_append, List.length_nil] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  exact hAne h1

/-! ### §306 (L-A1) `MTowerStep` は「`Q` の塔 ＋ `Q⟦m⟧` の 1 ブロック」

```lean
def MTowerStep (a) (Q) (d e) : Prop :=
  ∀ n m, 1 <= m → mTower Q d e n ++ **shiftr01 (d*n) 0 ((Lift1 Q (e*n))⟦m⟧)** ∈ W a
```

⟹ ★ **`(Lift1 X t)⟦m⟧ = Lift1 (X⟦m⟧) t`**（`Lift1` は `oper` と可換）を仮定すると、
`Lift1_shiftr01`（`L105Cap:3873`、緑）と合わせて末尾が

    **`Lift1 (shiftr01 (d*n) 0 (Q⟦m⟧)) (e*n)`**

になる。⟹ ⟹ ★★★ これは **`Q⟦m⟧` を生成元とする塔の第 `n` ブロックそのもの**。
⟹ ★ ですから `MTowerStep` は **「`Q` の塔 `n` 個 ＋ `Q⟦m⟧` の第 `n` ブロック 1 個」**である。

⚠ 可換性 `LiftOperComm` は H12 が (W66)/(W69) で詰めている。ここでは仮定として置き、
**それが来たときに何が言えるか**だけを書く（重複しない）。 -/

/-- ⚠⚠ **訂正（R2 の実測 (R-C1)）**: **一様版 `∀ M t n, (Lift1 M t)⟦n⟧ = Lift1 (M⟦n⟧) t` は偽**。
最小反例は **`M = (0,0,0)(1,0,0)`、`t = 1`、`n = 2`**
（左辺 `(0,1,0)(0,1,0)` ／ 右辺 `(0,1,0)(0,0,0)`）で、**悪根が根そのもの**の場合。
分ける軸は「**親が根かどうか**」1 本（`parent ≠ 0` なら 3 母集団すべてで 100%）。
⟹ ★ ですから **点ごとの版**にし、使う場所で `M` を指定する。
⟹ ★★ `parent ≠ 0` の枝は H12 の `lift_oper_comm_of_hr0`（緑）、
`parent = 0` の枝は `Wset.oper_Lift1_root`（`Wset:3384`、右辺は `glift`）。 -/
def LiftOperCommAt (M : TrioSeq) : Prop := ∀ (t n : ℕ), (Lift1 M t)⟦n⟧ = Lift1 (M⟦n⟧) t

/-- ★★★★★ **可換性の下で、`MTowerStep` は「塔 ＋ `Q⟦m⟧` の 1 ブロック」に書き換わる**。 -/
theorem mTowerStep_iff_of_comm {Q : TrioSeq} (h : LiftOperCommAt Q) (a : ℕ) (d e : ℕ) :
    L105.MTowerStep a Q d e ↔
      ∀ n m : ℕ, 1 ≤ m →
        mTower Q d e n ++ Lift1 (shiftr01 (d * n) 0 (Q⟦m⟧)) (e * n) ∈ W a := by
  unfold L105.MTowerStep
  constructor <;> intro hh n m hm
  · have := hh n m hm
    rwa [h (e * n) m, ← L105.Lift1_shiftr01] at this
  · have := hh n m hm
    rwa [h (e * n) m, ← L105.Lift1_shiftr01]

/-- ⟹ **`n = 0` は「`Q⟦m⟧` そのもの」**（塔が空、持ち上げ 0）。 -/
theorem mTowerStep_zero_of_comm {Q : TrioSeq} (h : LiftOperCommAt Q) {a : ℕ} {d e : ℕ}
    (hst : L105.MTowerStep a Q d e) (m : ℕ) (hm : 1 ≤ m) :
    Lift1 (shiftr01 0 0 (Q⟦m⟧)) 0 ∈ W a := by
  have := (mTowerStep_iff_of_comm h a d e).mp hst 0 m hm
  simpa [mTower] using this

/-! ### §307 (L-A2) `MTowerClosedS` は「塔に 1 列足す」1 本に落ちる（`B = []` から始める）

team-lead の助言どおり **`B = []` から 1 列ずつ**足す。それはちょうど
`prefixTowerClosed_of_snocStepPar`（`L105Cap:11859`）を **`A = []`** で使うこと。
⟹ ★ 孤児は `snoc_orphan_W` が片づけるので、残るのは **「足す列が親を持つ」1 本**。 -/

/-- **塔に 1 列足す**（親を持つ場合だけ）。⟹ これ 1 本で `MTowerClosedS` が出る。 -/
def TowerSnocStep : Prop :=
  ∀ (u : ℕ) (Q : TrioSeq) (d e n j : ℕ), Q ∈ W u →
    (∀ l, 1 ≤ l → l < Q.length → entry Q 0 0 < entry Q 0 l) → j < Q.length →
    (hasParent (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (srow (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length)
      (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length
      ∨ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j = []) →
    mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j ∈ W u →
    mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1) ∈ W u

/-- ★★★★★ **`TowerSnocStep` 1 本から `MTowerClosedS` が出る**（`A = []` で流す）。 -/
theorem mTowerClosedS_of_towerSnocStep (h : TowerSnocStep) : L105.MTowerClosedS := by
  intro u d e n Q hQ hs
  have hkey := L105.prefixTowerClosed_of_snocStepPar (A := []) (Q := Q) (d := d) (e := e)
    (u := u) (by simpa using W_nil u) ?_ n
  · simpa using hkey
  · intro n' j hj hpar hmem
    simp only [List.nil_append] at hpar hmem ⊢
    exact h u Q d e n' j hQ hs hj hpar hmem

/-! ### §308 `Based` 版の `TowerSnocStep`

`L105Cap §77.5`（私の追記）で `MTowerClosedBased` が `Final` まで通ったので、
§307 の `Based` 版を用意する。⟹ ★ `entry Q 0 0 = 0` を持ち回るだけ。 -/

/-- **塔に 1 列足す**（`based` 版）。 -/
def TowerSnocStepBased : Prop :=
  ∀ (u : ℕ) (Q : TrioSeq) (d e n j : ℕ), Q ∈ W u →
    (∀ l, 1 ≤ l → l < Q.length → entry Q 0 0 < entry Q 0 l) → entry Q 0 0 = 0 →
    j < Q.length →
    (hasParent (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (srow (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length)
      (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length
      ∨ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j = []) →
    mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j ∈ W u →
    mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1) ∈ W u

/-- ★★★★★★★★ **`TowerSnocStepBased` 1 本から `MTowerClosedBased` が出る**。
⟹ `L105Cap.wstar2s_closed_of_mTowerClosedBased` に食わせれば `Final` まで届く。 -/
theorem mTowerClosedBased_of_towerSnocStepBased (h : TowerSnocStepBased) :
    L105.MTowerClosedBased := by
  intro u d e n Q hQ hs hb
  have hkey := L105.prefixTowerClosed_of_snocStepPar (A := []) (Q := Q) (d := d) (e := e)
    (u := u) (by simpa using W_nil u) ?_ n
  · simpa using hkey
  · intro n' j hj hpar hmem
    simp only [List.nil_append] at hpar hmem ⊢
    exact h u Q d e n' j hQ hs hb hj hpar hmem

/-! ### §309 「末尾が最浅なら、どの行でも孤児」—— 輪が切れる機構

`d <= 段差` の枝は「`Q` の末尾列が `Q` の中で（弱く）最浅」と同値（team-lead の (W80) 経由の導出）。
そして **最浅なら `nextrel0` が張れず、`nextrel1` / `nextrel2` も `le0` を含むので張れない**。
⟹ ★★★ **どの行でも孤児** ⟹ **`oper = Pred`** ⟹ **`snoc_orphan_W` で無料**。

⟹ ★ R2 の実測「鎖は 3 段以内に必ず孤児で終わる」（4 母集団、約 14.5 万鎖、破れ 0）の機構が、これ。 -/

/-- ★★★★★ **的が（弱く）最浅なら、どの行でも親を持たない**（前提なし）。 -/
theorem no_parent_of_shallowest {M : TrioSeq} {t : ℕ}
    (hmin : ∀ c, c < t → entry M 0 t ≤ entry M 0 c) (i : ℕ) :
    ¬ hasParent M i t := by
  rintro ⟨c, hc, -⟩
  have hlt : entry M 0 c < entry M 0 t ∧ c < t := by
    rw [nextR] at hc
    by_cases h0 : i = 0
    · rw [if_pos h0] at hc
      exact ⟨hc.2.2.2.1, hc.2.2.1⟩
    · rw [if_neg h0] at hc
      by_cases h1 : i = 1
      · rw [if_pos h1] at hc
        exact ⟨entry0_lt_of_le0_ne hc.2.2.2.2.1 (by have := hc.2.2.1; omega), hc.2.2.1⟩
      · rw [if_neg h1] at hc
        exact ⟨entry0_lt_of_le0_ne (le0_of_le1' hc.2.2.2.2.1)
          (by have := hc.2.2.1; omega), hc.2.2.1⟩
  have := hmin c hlt.2
  omega

/-- ⟹ **`srow <= 1` なら `oper` の新しい `e`（＝ `d1`）は 0**（定義から直接）。 -/
theorem oper_d1_eq_zero_of_srow_le_one {M : TrioSeq} {t : ℕ} (h : srow M t ≤ 1) :
    (if 1 < srow M t then entry M 1 t - entry M 1 (parent M (srow M t) t) else 0) = 0 := by
  rw [if_neg (by omega)]

/-! ### §310 行 1 / 行 2 の「最小なら孤児」—— §309 の各行版

§309（行 0 で最浅なら全行で孤児）の、行 1 / 行 2 だけの版。
`nextrel1` / `nextrel2` はそれぞれ行 1 / 行 2 の**狭義**増加を要求するので、
**的がその行で（弱く）最小なら、その行の親は無い**。

⟹ ★ 使い道: **`e = 0` の塔では、行 1 の値はどのブロックでも `Q` の値のまま**なので、
**`Q` の根が行 1 で最小なら、ブロック根は行 1 の孤児**。
実測（`e = 0`、ブロック根、`srow = 1`、分母 7,656）:

    孤児 ∧ `Q` に根より行 1 の低い列なし … 4,776（62.38%）  ← ★ この補題が捕まえる
    孤児 ∧ 低い列あり ………………………… 2,184（28.53%）  （`le0` が届かない場合）
    親あり ∧ 低い列あり ……………………… 696（9.09%）
    ⛔ **親あり ∧ 低い列なし … 0 件** ⟹ ★ **必要条件は 100% 成立** -/

/-- ★★★ **行 1 で（弱く）最小なら、行 1 の親は無い**（前提なし）。 -/
theorem no_parent1_of_row1_min {M : TrioSeq} {t : ℕ}
    (hmin : ∀ c, c < t → entry M 1 t ≤ entry M 1 c) : ¬ hasParent M 1 t := by
  rintro ⟨c, hc, -⟩
  rw [nextR, if_neg (by decide), if_pos rfl] at hc
  have h1 := hmin c hc.2.2.1
  have h2 := hc.2.2.2.1
  omega

/-- ★★★ **行 2 で（弱く）最小なら、行 2 の親は無い**（前提なし）。 -/
theorem no_parent2_of_row2_min {M : TrioSeq} {t : ℕ}
    (hmin : ∀ c, c < t → entry M 2 t ≤ entry M 2 c) : ¬ hasParent M 2 t := by
  rintro ⟨c, hc, -⟩
  rw [nextR_two] at hc
  have h1 := hmin c hc.2.2.1
  have h2 := hc.2.2.2.1
  omega

/-- ⟹ **`srow` が何であれ、その行で最小なら孤児**（`HasParentInBlock` を潰す形）。 -/
theorem no_parent_of_srow_min {M : TrioSeq} {t : ℕ}
    (hmin : ∀ c, c < t → entry M (srow M t) t ≤ entry M (srow M t) c) :
    ¬ hasParent M (srow M t) t := by
  rcases Nat.lt_or_ge (srow M t) 1 with h0 | h1
  · have hz : srow M t = 0 := by omega
    rw [hz] at hmin ⊢
    exact no_parent_of_shallowest hmin 0
  · rcases Nat.lt_or_ge (srow M t) 2 with h1' | h2
    · have ho : srow M t = 1 := by omega
      rw [ho] at hmin ⊢
      exact no_parent1_of_row1_min hmin
    · have ht : srow M t = 2 := by
        have hle : srow M t ≤ 2 := by
          unfold srow
          split_ifs <;> omega
        omega
      rw [ht] at hmin ⊢
      exact no_parent2_of_row2_min hmin

/-! ### §311 測度 `(e, d)` の 2 部品目 —— `srow = 0` なら新しい `d` は 0

R2 の (R-C10)（41,376 遷移、破れ 0）が見つけた測度は **`(e, d)` の辞書式**。
その部品は 4 つで、機構は `Trio.lean:106-114` の `if` 2 つだけ:

    `d' := if **0 < sr** then entry T 0 t - entry T 0 c else 0
    `e' := if **1 < sr** then entry T 1 t - entry T 1 c else 0

⟹ ★ **`sr <= 1` ⟹ `e' = 0`**（§309 の 2 本目、緑）
⟹ ★ **`sr = 0` ⟹ `d' = 0`**（下、同じ形）
⟹ ★ **`d = 0` ⟹ ブロック根は孤児**（H12 の `no_nextrel0_blockRoot_of_d_zero`、緑）
⟹ ⚠ **`sr = 2` の枝は `d <= 段差` に来ない**（R2 の実測、型はまだ）

⟹ ⟹ ★★★ **`e` は `sr <= 1` で 0 に落ち、そのあと `d` が `sr = 0` で 0 に落ち、
そこで孤児になって終わる** ⟹ **鎖長 3 の説明**。 -/

/-- ★★★ **`srow = 0` なら `oper` の新しい `d` は 0**（定義から直接）。 -/
theorem oper_d0_eq_zero_of_srow_zero {M : TrioSeq} {t j0 : ℕ} (h : srow M t = 0) :
    (if 0 < srow M t then entry M 0 t - entry M 0 j0 else 0) = 0 := by
  rw [if_neg (by omega)]

/-- ⟹ **`srow <= 1` なら `(d', e')` の第 2 成分は 0**、
**`srow = 0` なら両方 0**（測度 `(e, d)` が狭義に減る根拠）。 -/
theorem oper_de_of_srow_zero {M : TrioSeq} {t j0 : ℕ} (h : srow M t = 0) :
    (if 0 < srow M t then entry M 0 t - entry M 0 j0 else 0) = 0 ∧
    (if 1 < srow M t then entry M 1 t - entry M 1 j0 else 0) = 0 :=
  ⟨oper_d0_eq_zero_of_srow_zero h, by rw [if_neg (by omega)]⟩

/-! ### §312 行 1 で最小なら、行 2 の親も無い —— §303 と §310 の合流

`nextrel2` は `le1 c t`（`c < t`）を含み、`le1` の鎖では行 1 が狭義に増える。
⟹ ★ ですから **的が行 1 で（弱く）最小なら、`le1` 錐に自分より前の列が 1 つも無い**
⟹ ⟹ ★★ **§303（行 2 の親 ⟺ 錐の中の `z = 0` の列）の右辺が空** ⟹ **行 2 の親も無い**。

⟹ ★★★ **部品 4（`d <= 段差` ∧ `srow = 2` ⟹ 孤児）は、
「ブロック根が塔の中で行 1 最小」に帰着します**。 -/

/-- ★★★★★ **行 1 で（弱く）最小なら、行 2 の親も無い**（前提なし）。 -/
theorem no_parent2_of_row1_min {M : TrioSeq} {t : ℕ}
    (hmin : ∀ c, c < t → entry M 1 t ≤ entry M 1 c) : ¬ hasParent M 2 t := by
  rintro ⟨c, hc, -⟩
  rw [nextR_two] at hc
  have hlt : entry M 1 c < entry M 1 t :=
    H12Export.entry1_lt_of_le1_ne hc.2.2.2.2.1 (by have := hc.2.2.1; omega)
  have := hmin c hc.2.2.1
  omega

/-- ⟹ **行 1 で最小なら、行 1 でも行 2 でも孤児**（`srow >= 1` の枝が全部落ちる）。 -/
theorem no_parent_ge_one_of_row1_min {M : TrioSeq} {t i : ℕ} (hi : 1 ≤ i)
    (hmin : ∀ c, c < t → entry M 1 t ≤ entry M 1 c) : ¬ hasParent M i t := by
  rcases Nat.lt_or_ge i 2 with h1 | h2
  · have : i = 1 := by omega
    rw [this]
    exact no_parent1_of_row1_min hmin
  · rintro ⟨c, hc, -⟩
    rw [nextR, if_neg (by omega), if_neg (by omega)] at hc
    have hlt : entry M 1 c < entry M 1 t :=
      H12Export.entry1_lt_of_le1_ne hc.2.2.2.2.1 (by have := hc.2.2.1; omega)
    have := hmin c hc.2.2.1
    omega

/-! ### §313 `d <= 段差` の枝の 5 通りを 1 本に —— 「孤児か、`e' = 0` か」

今日の表（実測、分母 56,214、例外 0）:

    `srow = 0`、`e = 0`  … 親あり、`d' = 0`、`e' = 0`   7,830  ⟹ §311 ＋ H12 (W79)(c)
    `srow = 1`、`e = 0`  … **孤児（無料）**              5,454  ⟹ H12 (W88)
    `srow = 1`、`e > 0`  … 親あり、`d' = d`、`e' = 0`   26,568  ⟹ §309
    `srow = 2`、`e = 0`  … **孤児（無料）**              5,454  ⟹ H12 (W87)
    `srow = 2`、`e > 0`  … **孤児（無料）**             10,908  ⟹ H12 (W87)

⟹ ★★★ **`srow = 2` は（`d <= 段差` の下で）常に孤児**、**`srow <= 1` は `e' = 0`**。
⟹ ⟹ ★★★★★ ですから **枝は「孤児」か「`e' = 0`」の 2 択**にまとまる。 -/

/-- ★★★★★ **`d <= 段差` の枝の 2 択**: **孤児**（＝ `snoc_orphan_W` で無料）か、
**`oper` の新しい `e` が 0**（＝ 測度 `(e, d)` の第 1 成分が落ちる）か。

`hgap2` は H12 の (W87)（`no_nextrel2_blockRoot_of_gap`）が供給する。 -/
theorem orphan_or_e_zero_of_gap {M : TrioSeq} {t j0 : ℕ}
    (hgap2 : srow M t = 2 → ¬ hasParent M 2 t) :
    ¬ hasParent M (srow M t) t ∨
      (if 1 < srow M t then entry M 1 t - entry M 1 j0 else 0) = 0 := by
  rcases Nat.lt_or_ge (srow M t) 2 with h | h2
  · exact Or.inr (by rw [if_neg (by omega)])
  · have ht : srow M t = 2 := by
      have hle : srow M t ≤ 2 := by
        unfold srow
        split_ifs <;> omega
      omega
    refine Or.inl ?_
    rw [ht]
    exact hgap2 ht

/-- ⟹ **さらに `srow = 0` なら `d` も落ちる**（測度の第 2 成分）。 -/
theorem orphan_or_meas_drop_of_gap {M : TrioSeq} {t j0 : ℕ}
    (hgap2 : srow M t = 2 → ¬ hasParent M 2 t) :
    ¬ hasParent M (srow M t) t ∨
      ((if 1 < srow M t then entry M 1 t - entry M 1 j0 else 0) = 0 ∧
        (srow M t = 0 →
          (if 0 < srow M t then entry M 0 t - entry M 0 j0 else 0) = 0)) := by
  rcases orphan_or_e_zero_of_gap (M := M) (t := t) (j0 := j0) hgap2 with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, fun h0 => oper_d0_eq_zero_of_srow_zero h0⟩

/-! ### §314 測度 `(|Q|, e, d)` の整礎帰納 —— `TowerSnocStepBased` の骨

全枝の場合分け（今日、私と H12 と R2 で確定）:

    `j > 0`                  … 孤児 or **`|V| < |Q|`** ⟹ 第 1 成分（⚠ `srow = 2` の前提だけ未確定）
    `j = 0`, `d <= 段差`      … §313（孤児 or `e' = 0`、`srow = 0` なら `d' = 0` も）
    `j = 0`, `d > 段差`, `e = 0` … 孤児 or **窓 < `|Q|`**（R2: 算術、機構不要）
    `j = 0`, `d > 段差`, `e > 0` … 孤児 or 窓 < `|Q|` or **等号 ⟹ `srow = 1` ⟹ `e' = 0`**（§309）

⟹ ★ ですから **測度 `(|Q|, e, d)` の辞書式**で回る。ここではその**整礎帰納の骨**を置く。
⟹ ⚠ 枝の中身は仮定（`hstep`）に置く ⟹ **§305 の失敗（骨の形が違った）を踏まえた形**。 -/

/-- 測度: `(|Q|, e, d)` の辞書式。 -/
def lexMeas (Q : TrioSeq) (e d : ℕ) : ℕ × ℕ × ℕ := (Q.length, e, d)

/-- 辞書式の順序（`Prod.Lex` の 3 段）。 -/
def LexLt : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

theorem lexLt_wf : WellFounded LexLt := by
  unfold LexLt
  exact WellFounded.prod_lex Nat.lt_wfRel.wf (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)

/-- 第 1 成分が減れば辞書式で減る。 -/
theorem lexLt_of_fst {a a' b b' c c' : ℕ} (h : a' < a) : LexLt (a', b', c') (a, b, c) :=
  Prod.Lex.left _ _ h

/-- 第 1 成分が同じで第 2 成分が減れば辞書式で減る。 -/
theorem lexLt_of_snd {a b b' c c' : ℕ} (h : b' < b) : LexLt (a, b', c') (a, b, c) :=
  Prod.Lex.right _ (Prod.Lex.left _ _ h)

/-- 第 1・第 2 が同じで第 3 が減れば辞書式で減る。 -/
theorem lexLt_of_trd {a b c c' : ℕ} (h : c' < c) : LexLt (a, b, c') (a, b, c) :=
  Prod.Lex.right _ (Prod.Lex.right _ h)

/-- ★★★★★ **`(|Q|, e, d)` の辞書式で回す整礎帰納**（骨）。
`hstep` に「その測度より小さい全部で成り立つなら、自分でも成り立つ」を渡す。 -/
theorem mTowerClosedBased_of_lex
    (P : TrioSeq → ℕ → ℕ → Prop)
    (hstep : ∀ Q e d, (∀ Q' e' d', LexLt (lexMeas Q' e' d') (lexMeas Q e d) → P Q' e' d') →
      P Q e d) : ∀ Q e d, P Q e d := by
  have hwf := lexLt_wf
  intro Q e d
  have key : ∀ m : ℕ × ℕ × ℕ, ∀ Q' e' d', lexMeas Q' e' d' = m → P Q' e' d' := by
    intro m
    induction m using WellFounded.induction (r := LexLt) hwf with
    | _ m ih =>
      intro Q' e' d' hm
      refine hstep Q' e' d' (fun Q'' e'' d'' hlt => ?_)
      exact ih (lexMeas Q'' e'' d'') (by rw [hm] at hlt; exact hlt) Q'' e'' d'' rfl
  exact key (lexMeas Q e d) Q e d rfl

/-! ### §315 表の 1・2 行を測度の減少に変換 —— 配線の部品

6 行の表（team-lead ＋ H12 ＋ R2 ＋ 私で確定）のうち、
**1 行（`srow = 0`）と 2 行（`srow = 1` ∧ `e > 0`）**は、
`oper` の `if` の定義だけで **測度 `(|Q|, e, d)` の減少**になる。ここではその変換を置く。

    0 行 `d = 0`                … 孤児（H12 `no_nextrel0_blockRoot_of_d_zero`）⟹ 無料
    1 行 `srow = 0`             … **`d' = 0 < d`**（§311）＋ `e' = 0 ≤ e` ⟹ ★ 本節
    2 行 `srow = 1` ∧ `e > 0`   … **`e' = 0 < e`**（§309）        ⟹ ★ 本節
    3 行 `srow = 1` ∧ `e = 0`   … 窓 < `|Q|`（`d > 段差`、R2 の算術）
    4 行 `srow = 2`             … 孤児（(W87)、`d <= 段差` or `e = 0`）⟹ 無料
    5 行 `srow = 2` ∧ `e > 0` ∧ `d > 段差` … ⛔ 唯一の残り -/

/-- 測度の減少を作る組み合わせ（前提なし）。 -/
theorem lexLt_of_cases {Q V : TrioSeq} {e d e' d' : ℕ}
    (h : V.length < Q.length ∨
      (V.length = Q.length ∧ (e' < e ∨ (e' = e ∧ d' < d)))) :
    LexLt (lexMeas V e' d') (lexMeas Q e d) := by
  unfold lexMeas
  rcases h with h | ⟨hlen, h⟩
  · exact lexLt_of_fst h
  · rw [hlen]
    rcases h with h | ⟨he, hd⟩
    · exact lexLt_of_snd h
    · rw [he]
      exact lexLt_of_trd hd

/-- ★★★★★ **表の 1 行**: `srow = 0` なら `(e', d') = (0, 0)` で、`d > 0` なら測度が減る。 -/
theorem lexLt_of_srow_zero {Q V : TrioSeq} {t j0 e d : ℕ}
    (hlen : V.length = Q.length) (hs : srow Q t = 0) (hd : 0 < d) :
    LexLt (lexMeas V (if 1 < srow Q t then entry Q 1 t - entry Q 1 j0 else 0)
                     (if 0 < srow Q t then entry Q 0 t - entry Q 0 j0 else 0))
          (lexMeas Q e d) := by
  rw [if_neg (by omega), if_neg (by omega)]
  refine lexLt_of_cases (Or.inr ⟨hlen, ?_⟩)
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact Or.inr ⟨rfl, hd⟩
  · exact Or.inl he

/-- ★★★★★ **表の 2 行**: `srow = 1` ∧ `e > 0` なら `e' = 0 < e` で測度が減る。 -/
theorem lexLt_of_srow_one {Q V : TrioSeq} {t j0 e d d' : ℕ}
    (hlen : V.length = Q.length) (hs : srow Q t = 1) (he : 0 < e) :
    LexLt (lexMeas V (if 1 < srow Q t then entry Q 1 t - entry Q 1 j0 else 0) d')
          (lexMeas Q e d) := by
  rw [if_neg (by omega)]
  exact lexLt_of_cases (Or.inr ⟨hlen, Or.inl he⟩)

/-- ★★★ **表の 3 行の形**: 窓が真に短ければ、`(e', d')` が何であれ測度は減る。 -/
theorem lexLt_of_window {Q V : TrioSeq} {e d e' d' : ℕ} (h : V.length < Q.length) :
    LexLt (lexMeas V e' d') (lexMeas Q e d) :=
  lexLt_of_cases (Or.inl h)

end L106
end TRIO
