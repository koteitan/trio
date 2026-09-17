/-
W5.lean: R2 測度誘導の「前提 h2cone(V) の遺伝」((w5), L105Cap §197)を詰める作業ファイル。

背景（notes 追記652-655）:
- R2 測度誘導は各 oper 段で窓 V を IH に渡す。その前提 `H2cone V`
  （V の錐内で行 2 が正の列は行 2 の親を持つ）が遺伝するかが §197 の唯一の open point。
- 実測（trio.py, z<2 fragment）: 実際の oper 由来対象では H2cone は常に成立し oper で保存。
  40887 到達列で違反 0、bad window 65128 で違反 0。
- 構造分解: `oper_eq_mTower`（悪根=根）で oper 結果は full mTower。その根の行 2 で場合分け:
    root 行2 = 0 → hz0 で `h2_cone`（下 `H2cone_mTower_of_hz0`, 無条件で ∀ d e）。
    root 行2 = 1 → fact B（下 `factB`）で srow(末尾)≤1 ⟹ oper の行1リフト e' = 0
                  ⟹ e=0 塔では in-cone 行2>0 列が block 0 に限局（confinement, 実測 54400/0）
                  ⟹ `H2cone(mTower Q d 0 n) ⟸ H2cone(Q)`（未 Lean、残り）。

本ファイルは非 root の作業ファイル（L106/H12H2 と同様）。全定理 0 sorry。
-/
import L105Cap
namespace TRIO
namespace W5
open Wset L105

/-- The h2cone premise (§197.3): `h2` restricted to the cone. Fed to the R2-measure IH. -/
def H2cone (V : TrioSeq) : Prop :=
  ∀ j, 1 ≤ j → j < V.length → le1 V 0 j → 0 < entry V 2 j →
    hasParent (V.take (j + 1)) 2 j

/-- **★ root 行2 = 0（hz0 半分）: `H2cone` は塔全体で成立**（無条件で `∀ d e`）。
    多数派の場合。`mTower_entry2_root` で `entry (mTower) 2 0 = entry Q 2 0 = 0`、あとは `h2_cone`。 -/
theorem H2cone_mTower_of_hz0 {Q : TrioSeq} (hQ1 : 0 < Q.length)
    (hz0 : entry Q 2 0 = 0) (d e n : ℕ) : H2cone (mTower Q d e n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro j hj1 hjl _ _
    rw [mTower_zero] at hjl
    simp at hjl
  · have hroot : entry (mTower Q d e n) 2 0 = 0 := by
      have := mTower_entry2_root (Q := Q) (d := d) (e := e) (n := n) (k := 0) hn hQ1
      simpa using this.trans hz0
    intro j hj1 hjl hcone hpos
    exact h2_cone hroot j hj1 hjl hpos hcone

/-- **★ fact B**: 悪根＝根の展開場面で、fragment のとき根の行 2 が 1 なら
    末尾列の `srow ≤ 1`（＝ `oper` の行 1 リフト `d1 = 0`）。
    `srow = 2` なら親（＝根 0）は `nextrel2` の始点 ⟹ fragment で `entry M 2 0 = 0` となり矛盾。 -/
theorem factB {M : TrioSeq} (hMne : M ≠ [])
    (hz : ∀ j, j < M.length → entry M 2 j ≤ 1)
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hj0 : parent M (srow M (M.length - 1)) (M.length - 1) = 0)
    (hroot2 : entry M 2 0 = 1) :
    srow M (M.length - 1) ≤ 1 := by
  by_contra hc
  have hlen : 0 < M.length := List.length_pos_of_ne_nil hMne
  have hlast : M.length - 1 < M.length := by omega
  have hsr2 : srow M (M.length - 1) = 2 := by
    have hle : srow M (M.length - 1) ≤ 2 := by unfold srow; split_ifs <;> omega
    omega
  have hnr : nextR M 2 0 (M.length - 1) := by
    have h := parent_nextR hp
    rw [hsr2] at h hj0
    rw [hj0] at h
    exact h
  have hn2 : nextrel2 M 0 (M.length - 1) := by
    rwa [nextR, if_neg (by decide), if_neg (by decide)] at hnr
  have hlt : entry M 2 0 < entry M 2 (M.length - 1) := hn2.2.2.2.1
  have hb : entry M 2 (M.length - 1) ≤ 1 := hz _ hlast
  omega

end W5
end TRIO
