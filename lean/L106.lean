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

end L106
end TRIO
