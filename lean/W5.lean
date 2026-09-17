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
                  ⟹ e=0 塔では in-cone 行2>0 列が block 0 に限局（下 `confinement`, GREEN）
                  ⟹ `H2cone(mTower Q d 0 n) ⟸ H2cone(Q)`（残り: block 0 還元の plumbing）。

本ファイルは非 root の作業ファイル（L106/H12H2 と同様）。全定理 0 sorry。
-/
import L105Cap
import H12Export
namespace TRIO
namespace W5
open Wset L105 H12Export

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

/-- **★ confinement (e=0)**: `e = 0` の塔で、根の行 1 錐に入る列は block 0 の中だけ。
    le1 の chain の各段は同ブロック内（`nextrel1_mTower_src_ge_block_of_witness`）。
    孤児ケースは `hr0`（根が le0 で全列の祖先, `le0_root_of_shallow`）で排除:
    `le1 T 0 j` は `entry Q 1 0 < entry Q 1 i` を強制し、根 0 が候補になるので i は必ず行1親を持つ。 -/
theorem confinement {Q : TrioSeq} {d n : ℕ} (hQ1 : 0 < Q.length) (hn : 0 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) :
    ∀ j, Relation.ReflTransGen (nextrel1 (mTower Q d 0 n)) 0 j → j < Q.length := by
  have hTlen : (mTower Q d 0 n).length = n * Q.length := mTower_length Q d 0 n
  have hT0 : 0 < (mTower Q d 0 n).length := by rw [hTlen]; exact Nat.mul_pos hn hQ1
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hrt
    rcases Relation.ReflTransGen.cases_tail hrt with heq | ⟨c, hrtc, hcj⟩
    · omega
    · have hcjlt : c < j := hcj.2.2.1
      have hjT : j < (mTower Q d 0 n).length := hcj.2.1
      have hcQ : c < Q.length := ih c hcjlt hrtc
      by_contra hjge
      rw [Nat.not_lt] at hjge
      have hi : j % Q.length < Q.length := Nat.mod_lt _ hQ1
      have hji : j = (j / Q.length) * Q.length + j % Q.length := by
        rw [Nat.mul_comm]; exact (Nat.div_add_mod j Q.length).symm
      have hk1 : 1 ≤ j / Q.length := (Nat.one_le_div_iff hQ1).mpr hjge
      have hkn : j / Q.length < n := by
        refine Nat.div_lt_of_lt_mul ?_
        rw [Nat.mul_comm]; rw [hTlen] at hjT; exact hjT
      have hle1 : le1 (mTower Q d 0 n) 0 j := ⟨hT0, hjT, hrt⟩
      have hlt1 : entry (mTower Q d 0 n) 1 0 < entry (mTower Q d 0 n) 1 j :=
        entry1_lt_of_le1_ne hle1 (by omega)
      have he0 : entry (mTower Q d 0 n) 1 0 = entry Q 1 0 := by
        have := entry1_mTower_block_e_zero Q d n 0 0 hn hQ1
        simpa using this
      have hej : entry (mTower Q d 0 n) 1 j = entry Q 1 (j % Q.length) := by
        conv_lhs => rw [hji]
        exact entry1_mTower_block_e_zero Q d n (j / Q.length) (j % Q.length) hkn hi
      rw [he0, hej] at hlt1
      have hipos : 0 < j % Q.length := by
        by_contra hi0
        have : j % Q.length = 0 := by omega
        rw [this] at hlt1; omega
      have hle0 : le0 Q 0 (j % Q.length) := le0_root_of_shallow hQ1 hr0 (j % Q.length) hipos hi
      have hpar : hasParent Q 1 (j % Q.length) := hasParent_one_of hi hipos hle0 hlt1
      obtain ⟨y, hy, -⟩ := hpar
      have hyn : nextrel1 Q y (j % Q.length) := by
        rw [nextR, if_neg (by decide), if_pos rfl] at hy; exact hy
      have hcj' : nextrel1 (mTower Q d 0 n) c ((j / Q.length) * Q.length + j % Q.length) := by
        rw [← hji]; exact hcj
      have hge : (j / Q.length) * Q.length ≤ c :=
        nextrel1_mTower_src_ge_block_of_witness Q hkn hi hyn hcj'
      have hkQ : Q.length ≤ (j / Q.length) * Q.length := by
        calc Q.length = 1 * Q.length := (one_mul _).symm
          _ ≤ (j / Q.length) * Q.length := Nat.mul_le_mul_right _ hk1
      omega

/-- **★ e=0 半分**: `H2cone(Q)` ∧ 根が狭義最浅 ⟹ `H2cone(mTower Q d 0 n)`。
    confinement で in-cone 列は block 0(=Q)に限局 → H2cone(Q) に帰着。 -/
theorem H2cone_mTower_e0 {Q : TrioSeq} {d n : ℕ} (hQ1 : 0 < Q.length) (hn : 0 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hQcone : H2cone Q) : H2cone (mTower Q d 0 n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro j hj1 hjl hcone hpos
  have hjQ : j < Q.length := confinement hQ1 hn hr0 j hcone.2.2
  have hdecomp : mTower Q d 0 (m + 1) = Q ++ (List.range m).flatMap fun k =>
      Lift1 (shiftr01 (d * (k + 1)) 0 Q) (0 * (k + 1)) := mTower_cons Q d 0 m
  have htake : (mTower Q d 0 (m + 1)).take (j + 1) = Q.take (j + 1) := by
    rw [hdecomp]; exact List.take_append_of_le_length (by omega)
  have hcQ : le1 Q 0 j := by
    have h := hcone; rw [hdecomp] at h; exact (le1_append_left hjQ).mp h
  have hposQ : 0 < entry Q 2 j := by
    have h := hpos; rw [hdecomp, entry_append_left _ _ hjQ] at h; exact h
  rw [htake]
  exact hQcone j hj1 hjQ hcQ hposQ

/-- **★★ premise 遺伝（CLAIM 1）**: `H2cone(Q)` を担いでいれば、
    `e = 0` または根の行 2 が 0 のとき `H2cone(mTower Q d e n)`。
    R2 測度誘導で IH に渡す oper 由来の塔はこの条件を満たす
    （根 row2=0 → 直接、根 row2=1 → `factB` で oper の行1リフト e=0）。 -/
theorem H2cone_mTower {Q : TrioSeq} {d e n : ℕ} (hQ1 : 0 < Q.length) (hn : 0 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hQcone : H2cone Q) (hcase : e = 0 ∨ entry Q 2 0 = 0) :
    H2cone (mTower Q d e n) := by
  rcases hcase with rfl | hz0
  · exact H2cone_mTower_e0 hQ1 hn hr0 hQcone
  · exact H2cone_mTower_of_hz0 hQ1 hz0 d e n

/-- **★★★ hz0 を H2cone(Q) に置換した塔閉包**。
    `mTowerClosed_of_snocStepCone`(L105Cap:11624)の証明と同一で、唯一の hz0 使用
    （Q-level h2cone を作る 1 箇所）を `H2cone Q` で差し替えたもの。
    ⟹ `z = 1`（根の行 2 が正）でも塔が閉じる。前提遺伝の統合点。 -/
theorem mTowerClosed_of_snocStepCone_h2cone {u : ℕ} {Q : TrioSeq} {d e : ℕ}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hQcone : H2cone Q)
    (hstep : ∀ (n j : ℕ), j < Q.length →
      (hasParent (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
          (srow (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
            (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length)
          (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length
        ∨ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j = []) →
      (0 < j → le1 Q 0 j → n * Q.length ≤
        parent (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
          (srow (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
            (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length)
          (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length) →
      mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j ∈ W u →
      mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1) ∈ W u) :
    ∀ n, mTower Q d e n ∈ W u := by
  refine mTowerClosed_of_snocStepPar ?_
  intro n j hj hpar0 hC
  set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
  have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
  have hTlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have hClen : (mTower Q d e n ++ B.take j).length = n * Q.length + j := by
    rw [List.length_append, hTlen, List.length_take, hBlen,
      Nat.min_eq_left (by omega)]
  have hC1len : (mTower Q d e n ++ B.take (j + 1)).length
      = n * Q.length + (j + 1) := by
    rw [List.length_append, hTlen, List.length_take, hBlen,
      Nat.min_eq_left (by omega)]
  have hsrow : srow (mTower Q d e n ++ B.take (j + 1))
      (n * Q.length + j) = srow (B.take (j + 1)) j := by
    unfold srow
    rw [show n * Q.length + j = (mTower Q d e n).length + j from by rw [hTlen],
      entry_append_right _ _ 2 j, entry_append_right _ _ 1 j]
  refine hstep n j hj hpar0 (fun hj1 hcone => ?_) hC
  have hloc : hasParent (B.take (j + 1)) (srow (B.take (j + 1)) j) j :=
    block_blockParent_all_cone hj hj1 hr0 hcone
      (fun hpos => hQcone j hj1 hj hcone hpos)
  have hpar : hasParent (mTower Q d e n ++ B.take (j + 1))
      (srow (B.take (j + 1)) j)
      ((mTower Q d e n ++ B.take (j + 1)).length - 1) := by
    rw [hC1len, show n * Q.length + (j + 1) - 1 = (mTower Q d e n).length + j from by
      rw [hTlen]; omega]
    exact hasParent_append_right_of _ _ hloc
  have hres := snocStep_parent_sameBlock (d := d) (e := e) (n := n)
    (i := srow (B.take (j + 1)) j) hj hloc hpar
  rw [hC1len, show n * Q.length + (j + 1) - 1 = n * Q.length + j from by omega] at hres
  rw [hClen, hsrow]
  exact hres

/-- 塔に 1 列足す step（`mTowerClosed_of_snocStepCone_h2cone` の hstep 前提）。 -/
def HstepFor (u : ℕ) (Q : TrioSeq) (d e : ℕ) : Prop :=
  ∀ (n j : ℕ), j < Q.length →
    (hasParent (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        (srow (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
          (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length)
        (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length
      ∨ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j = []) →
    (0 < j → le1 Q 0 j → n * Q.length ≤
      parent (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        (srow (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
          (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length)
        (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length) →
    mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j ∈ W u →
    mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1) ∈ W u

/-- **★★★★ 残余を明示化**: `MTowerClosedRow2`(Final の残核)は
    **(A) H2cone 不変量** ＋ **(B) hstep** の 2 本に帰着する。
    (A) は well-formed Q で成り立ち塔で遺伝（`H2cone_mTower`）、
    (B) は §138 窓測度（復活は H2cone が排除、追記659）で閉じる見通し。 -/
theorem mTowerClosedRow2_of_h2cone_hstep
    (hH2 : ∀ (u d e : ℕ) (Q : TrioSeq), Q ∈ W u →
      (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
      (∃ p ∈ Q, 0 < p.2.2) → H2cone Q)
    (hHstep : ∀ (u d e : ℕ) (Q : TrioSeq), Q ∈ W u →
      (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
      (∃ p ∈ Q, 0 < p.2.2) → HstepFor u Q d e) :
    L105.MTowerClosedRow2 := by
  intro u d e n Q hQ hs hz2
  exact mTowerClosed_of_snocStepCone_h2cone hs (hH2 u d e Q hQ hs hz2)
    (hHstep u d e Q hQ hs hz2) n

end W5
end TRIO
