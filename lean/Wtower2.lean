/-
Wtower2.lean: **行 2 塔をリフト無し `Wstar` のまま解く** — (WL) を法として。

`towerGraft2_holds`（Wset.lean）は塔の帰納を「すべてのリフト量 `s` について」
強めて回している。そのために `Wstar2`（リフト閉）が要り、そこから `GraftAll`
→ `GX` → `CoreCap` の全体が生えた。

しかし塔が実際に消費するのは **1 つの具体的なリフト `d1 = 行1(末尾) - v`** だけ
であり、段の勘定は

```
prev ∈ W (2v+z)  --(WL)-->  Lift1 prev d1 ∈ W (2v+z+2*d1) = W (2w+z) ⊆ W m
                              （w = 行1(末尾), z < 行2(末尾) ⟹ 2w+z ≤ m）
```

でちょうど閉じる。したがって **(WL) さえあれば `Wstar`（リフト無し）のままで
`TowerGraft2` が証明でき、`Wstar2` / `GX` / `CoreCap` は不要**になる。

(WL) は `tools/probe_lift.py` で 18300 例すべて**等号**で成立
（`minstage (Lift1 X d) = minstage X + 2d`）。階段リフト版
（`Wslift.slift_mem_W_tight` / `mlift_mem_W`）は核なしで証明済み。
-/
import Wset
import Wslift
import Xbar
import Pair.Bridge

namespace TRIO

open Wset
open Classical

/-- **(WL)**: the ambient root lift costs exactly `2 * d` stages.  Measured with
equality on 18300 instances (`tools/probe_lift.py`); the staircase-lift version
is proved (`Wslift.mlift_mem_W`). -/
def LiftStage : Prop :=
  ∀ (m d : ℕ) (X : TrioSeq), X ∈ W m → Lift1 X d ∈ W (m + 2 * d)

/-! ## (WL) の**タイのない**場合は無料

BM4 が行 1 に施すリフトのマスクは `A_xy` ＝ 悪い根の**添字**の子孫錐
（`Lift1` の `le1 X 0 ·`）である。一方、証明済みのリフト法則
（`Wslift.slift_mem_W` / `mlift_mem_W`）のマスクは `amin`（行 0 祖先鎖上の行 1
最小値）という**値**で決まる上方集合 `coneV` である。この違いが本質的なのは

* `amin` は `oper` で不変（`amin_oper_mir`）なので `slift` は展開と可換
  （`slift_oper`）だが、
* **添字**で決まる錐はコピーで壊れる（コピー `k` は自分自身の錐を持つ）ので
  `Lift1` は展開と可換でない

からである（計測 `tools/probe_lift1_mask.py` 系: 孤児枝は 210204 例すべて可換、
親あり枝は 192996 例中 47718 例で不可換）。

2 つのマスクの差はちょうど**行 1 のタイ**（根と行 1 の値が等しい列）だけで、
`le1` 錐 ⊆ `amin` 錐は**無条件**（下の `coneV_of_le1`。計測 64808 例 0 例外）。
したがって逆包含（`TieFree`）が成り立てば (WL) はその場で無料になる。 -/

/-- 行 1 のタイが無い: `amin` 錐が `le1` 錐に収まる（逆は `coneV_of_le1`）。 -/
def TieFree (X : TrioSeq) : Prop :=
  ∀ j, coneV X (entry X 1 0 - 1) j → le1 X 0 j

/-- **`le1` 錐 ⊆ `amin` 錐**（無条件）。根の行 1 錐に入る列は、行 0 祖先すべてが
根以上の行 1 値を持つ（`le1_chain_window`）。 -/
theorem coneV_of_le1 {X : TrioSeq} (hv : 1 ≤ entry X 1 0) {j : ℕ}
    (h : le1 X 0 j) : coneV X (entry X 1 0 - 1) j := by
  intro y hyj
  have h0j : Relation.ReflTransGen (nextrel0 X) 0 j := rtg1_to_rtg0 h.2.2
  have h0y : Relation.ReflTransGen (nextrel0 X) 0 y :=
    rtg0_comparable h0j hyj (Nat.zero_le y)
  by_cases hy0 : y = 0
  · subst hy0; omega
  · have := le1_chain_window h.2.2 y h0y hyj (fun hh => hy0 hh)
    omega

/-- タイが無ければ根リフトは**証明済みの**マスクリフトそのもの。 -/
theorem Lift1_eq_mlift_of_tieFree {X : TrioSeq} (hv : 1 ≤ entry X 1 0)
    (h : TieFree X) (d : ℕ) :
    Lift1 X d = mlift X (entry X 1 0 - 1) d := by
  unfold Lift1 mlift
  refine List.map_congr_left ?_
  intro j _
  have hif : (if le1 X 0 j then d else 0)
      = (if coneV X (entry X 1 0 - 1) j then d else 0) := by
    by_cases hc : le1 X 0 j
    · rw [if_pos hc, if_pos (coneV_of_le1 hv hc)]
    · rw [if_neg hc, if_neg (fun hcc => hc (h j hcc))]
  rw [hif]

/-- **★ (WL) はタイのない根の上では核なしで成り立つ。**  `mlift_mem_W` は
`slift_oper` 経由で証明済みなので、この場合の (WL) は完全に無料。 -/
theorem liftStage_of_tieFree {m d : ℕ} {X : TrioSeq} (hX : X ∈ W m)
    (hv : 1 ≤ entry X 1 0) (h : TieFree X) : Lift1 X d ∈ W (m + 2 * d) := by
  rw [Lift1_eq_mlift_of_tieFree hv h d]
  exact mlift_mem_W X hX

/-! ### `v0 = 0` も込みの版: 行 1 の**窓**があれば錐は全体

`TieFree` は `mlift` の閾値が `v0 - 1` なので `v0 = 0` では原理的に届かない。
だが根が行 1 でも**狭義最小**なら（＝悪い部分が行 1 の窓）、`le1_zero_iff` より
根の錐は**全体**になり、`Lift1` は一様シフト `shiftr01 0 d` そのものになる。
そして一様シフトは `Wslift.ulift_mem_W` で**核なしに証明済み**（`Stair.zero` を
使わない）。実 ST_TS では行 2 崩壊の悪い部分の 53634/53642 がこの窓を満たす
（破れる 8 例はすべて `v0 = 0`、`tools/probe_tiefree_stts.py` の姉妹計測）。 -/

/-- 根が行 0 で狭義最浅かつ行 1 でも狭義最小なら `Lift1` は一様シフト。 -/
theorem Lift1_eq_shiftr1_of_window {X : TrioSeq}
    (hr : ∀ l, 0 < l → l < X.length → entry X 0 0 < entry X 0 l)
    (hw : ∀ l, 0 < l → l < X.length → entry X 1 0 < entry X 1 l) (d : ℕ) :
    Lift1 X d = shiftr01 0 d X := by
  have hlenL : (Lift1 X d).length = X.length := Lift1_length X d
  have hlenS : (shiftr01 0 d X).length = X.length := shiftr01_length 0 d X
  refine List.ext_getElem (by rw [hlenL, hlenS]) ?_
  intro i hi1 _
  rw [hlenL] at hi1
  rw [← entry_triple (X := Lift1 X d) (by rw [hlenL]; exact hi1),
    ← entry_triple (X := shiftr01 0 d X) (by rw [hlenS]; exact hi1)]
  have hcone : le1 X 0 i := by
    rw [le1_zero_iff hr hi1]
    intro y hyj hy0
    have hylt : y < X.length := by
      have := nextrel0_rtrancl_index_le hyj
      omega
    exact hw y (by omega) hylt
  rw [entry0_Lift1, entry2_Lift1, entry1_Lift1 hi1, if_pos hcone,
    entry0_shiftr1, entry1_shiftr1 hi1, entry2_shiftr01]

/-- **★★ (WL) は「根が行 1 でも狭義最小」なら核なしで成立**（`v0 = 0` でも可）。 -/
theorem liftStage_of_window {m d : ℕ} {X : TrioSeq} (hX : X ∈ W m)
    (hr : ∀ l, 0 < l → l < X.length → entry X 0 0 < entry X 0 l)
    (hw : ∀ l, 0 < l → l < X.length → entry X 1 0 < entry X 1 l) :
    Lift1 X d ∈ W (m + 2 * d) := by
  rw [Lift1_eq_shiftr1_of_window hr hw d]
  exact ulift_mem_W X hX

/-! ### ★★★ マスクを完全に迂回する: 行 1 の単調性 `(ROW1MONO)`

上の 2 つはどちらも「マスクが一致する」十分条件で、その仮定は ST_TS 到達可能性の
強さを持つ（PROOF-STATUS 5.7）。ところが **マスクを比較する必要は無い**:

```
Lift1 X d  =  shiftr01 0 d X  の行 1 を、錐の外の列でだけ d 下げたもの
```

であり、一様シフトの方は `(ULIFT)` で**証明済み**。したがって `W` が行 1 の
**引き下げ**で閉じてさえいれば、`(WL)` はマスクの一致を一切使わずに出る。
これで「添字マスク vs 値マスク」の障害は迂回できる。

計測 `tools/probe_row1mono.py`: 多列同時 369068 例 0 違反、単列 106763 例 0 違反。 -/

/-- **(ROW1MONO)**: `W a` は行 1 の引き下げで閉じている（行 0・行 2 は不変）。 -/
def Row1Mono : Prop :=
  ∀ (a : ℕ) (M M' : TrioSeq), M ∈ W a → M'.length = M.length →
    (∀ j, entry M' 0 j = entry M 0 j) → (∀ j, entry M' 2 j = entry M 2 j) →
    (∀ j, entry M' 1 j ≤ entry M 1 j) → M' ∈ W a

theorem entry1_out {Y : TrioSeq} {j : ℕ} (hj : Y.length ≤ j) : entry Y 1 j = 0 := by
  show (Y.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)).2.1 = 0
  rw [getD_out hj]

/-! ### ⚠ 行 0 の側は**やってはいけない**: 定理そのものと同値

行 1 で効いた「証明済みの上界 ＋ 単調性」を行 0 でやると**同値**になってしまう。
深さを全部 0 に潰した列は `nextrel0` が空なので全列が孤児で、展開は
`dropLast` に潰れる ⟹ 根のレベルさえ収まれば**無条件に `W a`**（`flat_mem_W`）。
したがって

```
(ROW0FREE) 行 1・行 2 が同じなら行 0 は `W` 所属に効かない  ⟺  trio 停止性
```

（`mem_W_of_row0free` / `Final.TRIO_terminates_of_row0free`）。計測でも行 0 の
任意の上げ下げは 0 違反（RAISE 390293 / LOWER 337510）だが、それは定理を測って
いるだけ。⛔ **行 0 の単調性・(DEPTHORD) を「補題」として使おうとしないこと。** -/

/-- 深さが全部 0 の列には親が無い（`nextrel0` が空なので `le0` は反射のみ）。 -/
theorem no_hasParent_of_flat {M : TrioSeq} (h0 : ∀ j, entry M 0 j = 0) (i j : ℕ) :
    ¬ hasParent M i j := by
  have hn0 : ∀ a b, ¬ nextrel0 M a b := by
    rintro a b ⟨-, -, -, hlt, -⟩
    rw [h0 a, h0 b] at hlt; omega
  have hr0 : ∀ {a b}, Relation.ReflTransGen (nextrel0 M) a b → a = b := by
    intro a b hab
    induction hab with
    | refl => rfl
    | @tail y z _ hyz _ => exact absurd hyz (hn0 y z)
  have hn1 : ∀ a b, ¬ nextrel1 M a b := by
    rintro a b ⟨-, -, hab, -, hle0, -⟩
    have := hr0 hle0.2.2
    omega
  have hr1 : ∀ {a b}, Relation.ReflTransGen (nextrel1 M) a b → a = b := by
    intro a b hab
    induction hab with
    | refl => rfl
    | @tail y z _ hyz _ => exact absurd hyz (hn1 y z)
  have hn2 : ∀ a b, ¬ nextrel2 M a b := by
    rintro a b ⟨-, -, hab, -, hle1, -⟩
    have := hr1 hle1.2.2
    omega
  rintro ⟨j0, hj0, -⟩
  unfold nextR at hj0
  split at hj0
  · exact hn0 _ _ hj0
  · split at hj0
    · exact hn1 _ _ hj0
    · exact hn2 _ _ hj0

theorem entry_out {Y : TrioSeq} {i j : ℕ} (hj : Y.length ≤ j) : entry Y i j = 0 := by
  unfold entry
  rw [getD_out hj]
  split_ifs <;> rfl

theorem flat_mem_W_aux : ∀ (N : ℕ) (M : TrioSeq) (a : ℕ), M.length ≤ N →
    (∀ j, entry M 0 j = 0) → lev M 0 ≤ a → M ∈ W a := by
  intro N
  induction N with
  | zero =>
      intro M a hN _ _
      have hnil : M = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil; exact W_nil a
  | succ N ih =>
      intro M a hN h0 hlev
      rcases Nat.lt_or_ge M.length 2 with hsm | hbig
      · rcases Nat.eq_zero_or_pos M.length with h | h
        · have hnil : M = [] := List.eq_nil_of_length_eq_zero h
          subst hnil; exact W_nil a
        · obtain ⟨p, rfl⟩ : ∃ p, M = [p] :=
            List.length_eq_one_iff.mp (by omega)
          have hb : 2 * p.2.1 + p.2.2 ≤ a := by
            unfold lev entry at hlev
            simpa using hlev
          exact singleton_mem_W hb
      · refine mem_of_oper_mem (fun n hn => ?_)
        have hL : M.length - 1 ≠ 0 := by omega
        have hp := no_hasParent_of_flat h0 (srow M (M.length - 1)) (M.length - 1)
        have hop : M⟦n⟧ = Pred M := by
          by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
              entry M 2 (M.length - 1) = 0
          · exact oper_eq_pred_of_zero n hL hz
          · exact oper_eq_pred_of_noParent n hL hz hp
        have hdl : M.dropLast = M.take (M.length - 1) := List.dropLast_eq_take
        rw [hop]
        unfold Pred
        rw [if_neg (by omega)]
        refine ih M.dropLast a (by rw [List.length_dropLast]; omega) ?_ ?_
        · intro j
          rcases Nat.lt_or_ge j (M.length - 1) with hj | hj
          · rw [hdl, Wset.entry_take hj]; exact h0 j
          · exact entry_out (by rw [List.length_dropLast]; omega)
        · have e1 : entry M.dropLast 1 0 = entry M 1 0 := by
            rw [hdl]; exact Wset.entry_take (by omega)
          have e2 : entry M.dropLast 2 0 = entry M 2 0 := by
            rw [hdl]; exact Wset.entry_take (by omega)
          unfold lev at hlev ⊢
          rw [e1, e2]; exact hlev

/-- **深さを全部 0 に潰した列は無条件に `W a`**（根のレベルが収まれば）。 -/
theorem flat_mem_W {M : TrioSeq} {a : ℕ} (h0 : ∀ j, entry M 0 j = 0)
    (hlev : lev M 0 ≤ a) : M ∈ W a :=
  flat_mem_W_aux M.length M a le_rfl h0 hlev

/-- **(ROW0FREE)**: 行 1・行 2 が同じなら行 0 は `W` 所属に効かない。 -/
def Row0Free : Prop :=
  ∀ (a : ℕ) (M M' : TrioSeq), M ∈ W a → M'.length = M.length →
    (∀ j, entry M' 1 j = entry M 1 j) → (∀ j, entry M' 2 j = entry M 2 j) →
      M' ∈ W a

/-- **⚠ `(ROW0FREE)` は定理そのもの**: 深さを潰した相手が無条件に `W` なので、
これを仮定すると**すべての**列が `Wself` に入ってしまう。 -/
theorem mem_W_of_row0free (h : Row0Free) (M : TrioSeq) : M ∈ W (lev M 0) := by
  set F : TrioSeq := M.map (fun p => ((0, p.2.1, p.2.2) : ℕ × ℕ × ℕ)) with hF
  have hlen : F.length = M.length := by rw [hF, List.length_map]
  have hget : ∀ j, j < M.length →
      F.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)
        = ((0, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ) := by
    intro j hj
    rw [hF, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [List.length_map]; exact hj)]
    simp only [List.getElem_map, Option.getD_some]
    unfold entry
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  have he1 : ∀ j, entry F 1 j = entry M 1 j := by
    intro j
    rcases Nat.lt_or_ge j M.length with hj | hj
    · show (F.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)).2.1 = entry M 1 j
      rw [hget j hj]
    · rw [entry_out (by rw [hlen]; exact hj), entry_out hj]
  have he2 : ∀ j, entry F 2 j = entry M 2 j := by
    intro j
    rcases Nat.lt_or_ge j M.length with hj | hj
    · show (F.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)).2.2 = entry M 2 j
      rw [hget j hj]
    · rw [entry_out (by rw [hlen]; exact hj), entry_out hj]
  have h0 : ∀ j, entry F 0 j = 0 := by
    intro j
    rcases Nat.lt_or_ge j M.length with hj | hj
    · show (F.getD j ((0, 0, 0) : ℕ × ℕ × ℕ)).1 = 0
      rw [hget j hj]
    · exact entry_out (by rw [hlen]; exact hj)
  have hlevF : lev F 0 = lev M 0 := by
    unfold lev; rw [he1 0, he2 0]
  exact h (lev M 0) F M (flat_mem_W h0 (by rw [hlevF])) hlen.symm
    (fun j => (he1 j).symm) (fun j => (he2 j).symm)

/-- **★★★ (WL) はマスク一致を使わずに `(ROW1MONO)` から出る。** -/
theorem liftStage_of_row1mono (h : Row1Mono) : LiftStage := by
  intro m d X hX
  refine h (m + 2 * d) (shiftr01 0 d X) (Lift1 X d) (ulift_mem_W X hX)
    ?_ ?_ ?_ ?_
  · rw [Lift1_length, shiftr01_length]
  · intro j; rw [entry0_Lift1, entry0_shiftr1]
  · intro j; rw [entry2_Lift1, entry2_shiftr01]
  · intro j
    rcases Nat.lt_or_ge j X.length with hj | hj
    · rw [entry1_Lift1 hj, entry1_shiftr1 hj]
      split <;> omega
    · rw [entry1_out (by rw [Lift1_length]; exact hj),
        entry1_out (by rw [shiftr01_length]; exact hj)]

/-! ## (WL) を「親のある場合」だけに縮める

`oper` の `Pred` 分岐（末尾列が全零、または親なし）は根リフトと**可換**である:
`Lift1` は行 2 を動かさず、行 1 も錐の列しか動かさないので `srow` を保ち
（`srow_Lift1`）、`hasParent` も保つ（`hasParent_Lift1`）。したがって
`Aop` の節 3（`domT` ⟹ 親なし）と節 2 の親なし枝は自動で流れ、(WL) は
**末尾列に親がある場合**だけに縮む。 -/

theorem Lift1_of_length_one {X : TrioSeq} (h1 : X.length = 1) (d : ℕ) :
    Lift1 X d = [((entry X 0 0, entry X 1 0 + d, entry X 2 0) : ℕ × ℕ × ℕ)] := by
  have hle : le1 X 0 0 := le1_refl (by omega)
  unfold Lift1
  rw [h1, show List.range 1 = [0] from rfl]
  simp only [List.map_cons, List.map_nil, if_pos hle]

/-- **The `Pred` branches commute with the root lift.** -/
theorem lift_oper_of_noParent {X : TrioSeq} {d n : ℕ} (h2 : 2 ≤ X.length)
    (hnp : ¬ hasParent X (srow X (X.length - 1)) (X.length - 1)) :
    (Lift1 X d)⟦n⟧ = Lift1 (X⟦n⟧) d := by
  classical
  have hlen : (Lift1 X d).length = X.length := Lift1_length X d
  have hL : X.length - 1 ≠ 0 := by omega
  have hnp' : ¬ hasParent (Lift1 X d) (srow (Lift1 X d) ((Lift1 X d).length - 1))
      ((Lift1 X d).length - 1) := by
    rw [hlen, srow_Lift1 hL, hasParent_Lift1]
    exact hnp
  have hpredX : X⟦n⟧ = Pred X := by
    by_cases hz : entry X 0 (X.length - 1) = 0 ∧ entry X 1 (X.length - 1) = 0 ∧
        entry X 2 (X.length - 1) = 0
    · exact oper_eq_pred_of_zero n hL hz
    · exact oper_eq_pred_of_noParent n hL hz hnp
  have hpredL : (Lift1 X d)⟦n⟧ = Pred (Lift1 X d) := by
    by_cases hz : entry (Lift1 X d) 0 ((Lift1 X d).length - 1) = 0 ∧
        entry (Lift1 X d) 1 ((Lift1 X d).length - 1) = 0 ∧
        entry (Lift1 X d) 2 ((Lift1 X d).length - 1) = 0
    · exact oper_eq_pred_of_zero n (by rw [hlen]; exact hL) hz
    · exact oper_eq_pred_of_noParent n (by rw [hlen]; exact hL) hz hnp'
  rw [hpredX, hpredL]
  unfold Pred
  rw [if_neg (by rw [hlen]; omega), if_neg (by omega), Lift1_dropLast]

/-- **(WL), parented residue**: the only case the lift law still needs. -/
def LiftStageParented : Prop :=
  ∀ (m d : ℕ) (X : TrioSeq), 2 ≤ X.length →
    hasParent X (srow X (X.length - 1)) (X.length - 1) →
    (∀ n, 1 ≤ n → Lift1 (X⟦n⟧) d ∈ W (m + 2 * d)) →
    ∀ n, 1 ≤ n → (Lift1 X d)⟦n⟧ ∈ W (m + 2 * d)

/-- **(WL) reduces to the parented case.**  Clause 1 and the one-column roots
are stage arithmetic, clause 3 forces `¬ hasParent` (`domT`), and the parentless
branch of clause 2 commutes by `lift_oper_of_noParent`. -/
theorem liftStage_of_parented (h : LiftStageParented) : LiftStage := by
  intro m d
  have hsub : W m ⊆ {X : TrioSeq | Lift1 X d ∈ W (m + 2 * d)} := by
    refine A2' ?_
    rintro X (⟨hl, hlev⟩ | hop | ⟨m', hm', hdom, hgr⟩)
    · rcases Nat.eq_zero_or_pos X.length with h0 | hpos
      · have hnil : X = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        show Lift1 ([] : TrioSeq) d ∈ W (m + 2 * d)
        simpa using W_nil (m + 2 * d)
      · have h1 : X.length = 1 := by omega
        show Lift1 X d ∈ W (m + 2 * d)
        rw [Lift1_of_length_one h1 d]
        have hbc : entry X 1 0 = 0 ∧ entry X 2 0 = 0 := by
          unfold lev at hlev; omega
        rw [hbc.1, hbc.2]
        exact singleton_mem_W (by omega)
    · rcases Nat.lt_or_ge X.length 2 with hsm | hbig
      · have hres := hop 1 le_rfl
        rwa [oper_eq_self_of_short 1 (by omega)] at hres
      · show Lift1 X d ∈ W (m + 2 * d)
        by_cases hp : hasParent X (srow X (X.length - 1)) (X.length - 1)
        · exact mem_of_oper_mem (h m d X hbig hp (fun n hn => hop n hn))
        · refine mem_of_oper_mem (fun n hn => ?_)
          rw [lift_oper_of_noParent hbig hp]
          exact hop n hn
    · rcases Nat.lt_or_ge X.length 2 with hsm | hbig
      · have hXne : X ≠ [] := by
          intro hc
          rw [hc] at hdom
          exact not_domT_nil m' hdom
        have h1 : X.length = 1 := by
          have : 0 < X.length := List.length_pos_iff.mpr hXne
          omega
        have hlv := hdom.1
        rw [show X.length - 1 = 0 from by omega] at hlv
        unfold lev at hlv
        show Lift1 X d ∈ W (m + 2 * d)
        rw [Lift1_of_length_one h1 d]
        exact singleton_mem_W (by omega)
      · show Lift1 X d ∈ W (m + 2 * d)
        refine mem_of_oper_mem (fun n hn => ?_)
        rw [lift_oper_of_noParent hbig hdom.2]
        exact aop_clause3_to_clause2 hbig hdom hgr n hn
  exact fun X hX => hsub hX

/-! ## 親ありの残差の 4 分割

計測（`GRAFTALL-PLAN` §1.9.51）では `Lift1` と `oper` の非可換は
**バッドルートの親 `j0` が `0` かつ崩壊行 `i1 ≤ 1`** の場合だけであった。
以下はその場合分けを Lean 側で固定するもので、各枝を個別に埋めれば
`LiftStageParented`、したがって (WL) が得られる。 -/

/-- The parented residue restricted to a class `C` of sequences. -/
def LSPOn (C : TrioSeq → Prop) : Prop :=
  ∀ (m d : ℕ) (X : TrioSeq), 2 ≤ X.length →
    hasParent X (srow X (X.length - 1)) (X.length - 1) → C X →
    (∀ n, 1 ≤ n → Lift1 (X⟦n⟧) d ∈ W (m + 2 * d)) →
    ∀ n, 1 ≤ n → (Lift1 X d)⟦n⟧ ∈ W (m + 2 * d)

theorem srow_cases (X : TrioSeq) (j : ℕ) :
    srow X j = 0 ∨ srow X j = 1 ∨ srow X j = 2 := by
  unfold srow
  split
  · exact Or.inr (Or.inr rfl)
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl

/-- The bad root's parent index of `X`. -/
noncomputable def badPar (X : TrioSeq) : ℕ :=
  parent X (srow X (X.length - 1)) (X.length - 1)

/-- **The four branches cover the parented residue.**  `1 ≤ badPar X` (the
window misses the head) and `badPar X = 0` with each of the three collapse rows.
Measurement says the first two branches commute with the lift; the open ones are
`badPar X = 0` with `srow ≤ 1`. -/
theorem liftStageParented_of_cases
    (hpos : LSPOn (fun X => 1 ≤ badPar X))
    (hs2 : LSPOn (fun X => badPar X = 0 ∧ srow X (X.length - 1) = 2))
    (hs0 : LSPOn (fun X => badPar X = 0 ∧ srow X (X.length - 1) = 0))
    (hs1 : LSPOn (fun X => badPar X = 0 ∧ srow X (X.length - 1) = 1)) :
    LiftStageParented := by
  intro m d X h2 hp hop n hn
  rcases Nat.eq_zero_or_pos (badPar X) with h0 | hposX
  · rcases srow_cases X (X.length - 1) with hsr | hsr | hsr
    · exact hs0 m d X h2 hp ⟨h0, hsr⟩ hop n hn
    · exact hs1 m d X h2 hp ⟨h0, hsr⟩ hop n hn
    · exact hs2 m d X h2 hp ⟨h0, hsr⟩ hop n hn
  · exact hpos m d X h2 hp hposX hop n hn

/-! ### 枝 `badPar = 0, i1 = 0`: コピーが同一なので可換性が要らない

`i1 = 0` では `d0 = d1 = 0` なので `oper` のコピーは**完全に同一**であり、
`X⟦n⟧` は `X.dropLast` を `n` 個並べたもの、`(Lift1 X d)⟦n⟧` は
`Lift1 (X.dropLast) d = Lift1 (X⟦1⟧) d` を `n` 個並べたものになる。よって
`W_flatMap_copies` がそのまま効く（`rsum` 条件は `nextrel0` の no-dip 節から）。 -/

theorem gcopy_flat (M : TrioSeq) (r L k : ℕ) : gcopy M r L 0 0 k = seg M r L := by
  unfold gcopy seg
  refine List.map_congr_left ?_
  intro j _
  simp

theorem gcopies_flat (M : TrioSeq) (r L n : ℕ) :
    gcopies M r L 0 0 n = (List.range n).flatMap fun _ => seg M r L := by
  unfold gcopies
  refine List.flatMap_congr ?_
  intro k _
  exact gcopy_flat M r L k

open Classical in
/-- The expansion of a length-`≥ 2` block whose bad root sits in row 0 with the
head as its parent: `n` literal copies of the peel. -/
theorem oper_of_srow0_par0 {X : TrioSeq} (h2 : 2 ≤ X.length)
    (hp : hasParent X (srow X (X.length - 1)) (X.length - 1))
    (hbp : parent X (srow X (X.length - 1)) (X.length - 1) = 0)
    (hsr : srow X (X.length - 1) = 0) (n : ℕ) :
    X⟦n⟧ = (List.range n).flatMap fun _ => X.dropLast := by
  have hnr := parent_nextR hp
  rw [hbp, hsr] at hnr
  have hn0 : nextrel0 X 0 (X.length - 1) := by
    unfold nextR at hnr
    rw [if_pos rfl] at hnr
    exact hnr
  have hpos : 0 < entry X 0 (X.length - 1) := by
    have := hn0.2.2.2.1
    omega
  have hz : ¬ (entry X 0 (X.length - 1) = 0 ∧ entry X 1 (X.length - 1) = 0 ∧
      entry X 2 (X.length - 1) = 0) := by
    rintro ⟨h0, -, -⟩; omega
  have hseg : seg X 0 (X.length - 1) = X.dropLast := by
    rw [seg_zero_eq_take X (show X.length - 1 ≤ X.length by omega),
      ← List.dropLast_eq_take]
  rw [oper_gcopies n (by omega) hz hp, hbp, hsr]
  rw [if_neg (by omega), if_neg (by omega), List.take_zero, Nat.sub_zero,
    gcopies_flat, List.nil_append, hseg]

open Classical in
/-- **Branch `badPar = 0`, collapse row `0`.** -/
theorem lspOn_srow0 :
    LSPOn (fun X => badPar X = 0 ∧ srow X (X.length - 1) = 0) := by
  classical
  rintro m d X h2 hp ⟨hbp, hsr⟩ hop n hn
  unfold badPar at hbp
  -- the peel is a `W`-member at the bumped stage
  have hQ : Lift1 X.dropLast d ∈ W (m + 2 * d) := by
    have h1 := hop 1 le_rfl
    rwa [oper_of_srow0_par0 h2 hp hbp hsr 1, show
      ((List.range 1).flatMap fun _ => X.dropLast) = X.dropLast from by simp] at h1
  -- the head is the shallowest column of the peel
  have hnr := parent_nextR hp
  rw [hbp, hsr] at hnr
  have hn0 : nextrel0 X 0 (X.length - 1) := by
    unfold nextR at hnr
    rw [if_pos rfl] at hnr
    exact hnr
  have hdeep : ∀ i, i < X.length - 1 → entry X 0 0 ≤ entry X 0 i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · exact le_rfl
    · have := hn0.2.2.2.2 i ⟨hipos, hi⟩
      have hlt := hn0.2.2.2.1
      omega
  have hhead : entry (Lift1 X.dropLast d) 0 0 = entry X 0 0 := by
    rw [entry0_Lift1, List.dropLast_eq_take,
      Wset.entry_take (show (0 : ℕ) < X.length - 1 by omega)]
  have hQr : ∀ p ∈ Lift1 X.dropLast d,
      entry (Lift1 X.dropLast d) 0 0 ≤ p.1 := by
    intro p hpm
    rw [hhead]
    unfold Lift1 at hpm
    rw [List.mem_map] at hpm
    obtain ⟨i, hi, rfl⟩ := hpm
    rw [List.mem_range, List.length_dropLast] at hi
    show entry X 0 0 ≤ entry X.dropLast 0 i
    rw [List.dropLast_eq_take, Wset.entry_take (show i < X.length - 1 by omega)]
    exact hdeep i (by omega)
  -- the lifted block expands to `n` copies of the lifted peel
  have hsrL : srow (Lift1 X d) ((Lift1 X d).length - 1) = 0 := by
    rw [Lift1_length, srow_Lift1 (by omega)]
    exact hsr
  have hpL : hasParent (Lift1 X d) (srow (Lift1 X d) ((Lift1 X d).length - 1))
      ((Lift1 X d).length - 1) := by
    rw [Lift1_length, srow_Lift1 (by omega), hasParent_Lift1]
    exact hp
  have hbpL : parent (Lift1 X d) (srow (Lift1 X d) ((Lift1 X d).length - 1))
      ((Lift1 X d).length - 1) = 0 := by
    rw [Lift1_length, srow_Lift1 (by omega), parent_Lift1]
    exact hbp
  rw [oper_of_srow0_par0 (by rw [Lift1_length]; omega) hpL hbpL hsrL n,
    Lift1_dropLast]
  exact W_flatMap_copies hQ hQr n

/-! ### 枝 `i1 = 2`: リフトはコピー塊の周期マスクになる

`gexp` の成分は `gexp_getD_mir` で明示的に書けるので、`Lift1` を先にかけた
コピー塊は「コピー塊に周期マスク `glift` をかけたもの」に一致する。これは
`D0`、`D1` を固定した**純粋な計算**で、`i1` にも親の位置にも依らない。 -/

theorem getElem_eq_getD' {l : TrioSeq} {i : ℕ} (h : i < l.length) :
    l[i] = l.getD i ((0, 0, 0) : ℕ × ℕ × ℕ) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

open Classical in
/-- **The root lift of a copies block is the block's periodic mask lift.** -/
theorem gexp_lift_eq_glift (X : TrioSeq) (L D0 D1 n d : ℕ)
    (hlen : 0 + L + 1 = X.length) (hLpos : 0 < L) :
    gexp (Lift1 X d) 0 L D0 D1 n = glift X L 0 d (gexp X 0 L D0 D1 n) := by
  classical
  have hlenL : 0 + L + 1 = (Lift1 X d).length := by rw [Lift1_length]; exact hlen
  have hlenA : (gexp (Lift1 X d) 0 L D0 D1 n).length = 0 + n * L :=
    gexp_length hlenL
  have hlenB : (glift X L 0 d (gexp X 0 L D0 D1 n)).length = 0 + n * L := by
    rw [glift_length]; exact gexp_length hlen
  refine List.ext_getElem (by rw [hlenA, hlenB]) ?_
  intro i h1 h2
  rw [hlenA] at h1
  obtain ⟨k, q, hk, hq, rfl⟩ := index_decomp hLpos (show i < n * L by omega)
  have hqL : q < X.length := by omega
  have hidx : (k * L + q) % L = q := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hq
  have hA := gexp_getD_mir (M := Lift1 X d) (j0 := 0) (Lb := L) (d0 := D0)
    (d1 := D1) (n := n) hlenL hk hq
  have hB := gexp_getD_mir (M := X) (j0 := 0) (Lb := L) (d0 := D0)
    (d1 := D1) (n := n) hlen hk hq
  rw [Nat.zero_add, Nat.zero_add] at hA hB
  have hiff : (le1 (Lift1 X d) 0 q) = (le1 X 0 q) := propext le1_Lift1
  have hgetA : (gexp (Lift1 X d) 0 L D0 D1 n)[k * L + q]
      = (entry X 0 q + k * D0,
         entry X 1 q + (if le1 X 0 q then d else 0)
           + (if le1 X 0 q then k * D1 else 0),
         entry X 2 q) := by
    rw [getElem_eq_getD' (by omega), hA, entry0_Lift1, entry2_Lift1,
      entry1_Lift1 hqL, hiff]
  have e0 : entry (gexp X 0 L D0 D1 n) 0 (k * L + q) = entry X 0 q + k * D0 := by
    show ((gexp X 0 L D0 D1 n).getD (k * L + q) ((0, 0, 0) : ℕ × ℕ × ℕ)).1 = _
    rw [hB]
  have e1 : entry (gexp X 0 L D0 D1 n) 1 (k * L + q)
      = entry X 1 q + (if le1 X 0 q then k * D1 else 0) := by
    show ((gexp X 0 L D0 D1 n).getD (k * L + q) ((0, 0, 0) : ℕ × ℕ × ℕ)).2.1 = _
    rw [hB]
  have e2 : entry (gexp X 0 L D0 D1 n) 2 (k * L + q) = entry X 2 q := by
    show ((gexp X 0 L D0 D1 n).getD (k * L + q) ((0, 0, 0) : ℕ × ℕ × ℕ)).2.2 = _
    rw [hB]
  have hgetB : (glift X L 0 d (gexp X 0 L D0 D1 n))[k * L + q]
      = (entry X 0 q + k * D0 + 0,
         entry X 1 q + (if le1 X 0 q then k * D1 else 0)
           + (if le1 X 0 q then d else 0),
         entry X 2 q) := by
    unfold glift
    rw [List.getElem_map, List.getElem_range, hidx, e0, e1, e2]
  rw [hgetA, hgetB]
  refine Prod.ext (by dsimp only; omega) (Prod.ext (by dsimp only; omega) rfl)

open Classical in
/-- **Branch `badPar = 0`, collapse row `2`**: here the lift commutes with the
expansion.  `gexp_lift_eq_glift` turns the lifted expansion into the periodic
mask lift, and `glift_eq_Lift1` identifies that mask with the intrinsic cone
(this is where `0 < d0` and `0 < d1`, i.e. the row-2 collapse, are used). -/
theorem lspOn_srow2 :
    LSPOn (fun X => badPar X = 0 ∧ srow X (X.length - 1) = 2) := by
  classical
  rintro m d X h2 hp ⟨hbp, hsr⟩ hop n hn
  unfold badPar at hbp
  set L : ℕ := X.length - 1 with hLdef
  have hLpos : 0 < L := by omega
  have hlen : 0 + L + 1 = X.length := by omega
  have hnr := parent_nextR hp
  rw [hbp, hsr] at hnr
  have hn2 : nextrel2 X 0 L := by
    unfold nextR at hnr
    rw [if_neg (by omega), if_neg (by omega)] at hnr
    exact hnr
  have hcone : le1 X 0 L := hn2.2.2.2.2.1
  have hup : ∀ l, 0 < l → l ≤ L → entry X 0 0 < entry X 0 l :=
    window_of_rtg0 (rtg0_of_rtg1 hcone.2.2) (by omega)
  have hlt0 : entry X 0 0 < entry X 0 L := hup L hLpos le_rfl
  set D0 : ℕ := entry X 0 L - entry X 0 0 with hD0
  set D1 : ℕ := entry X 1 L - entry X 1 0 with hD1
  have hd0pos : 0 < D0 := by omega
  have hd0e : entry X 0 L = entry X 0 0 + D0 := by omega
  have hd1pos : 0 < D1 := by
    have := le1_entry1_lt hcone (by omega)
    omega
  have hz : ¬ (entry X 0 L = 0 ∧ entry X 1 L = 0 ∧ entry X 2 L = 0) := by
    rintro ⟨h0, -, -⟩; omega
  have hgexpX : X⟦n⟧ = gexp X 0 L D0 D1 n := by
    have h := oper_eq_gexp (M := X) n (by omega) hz hp hbp
    rw [hsr, if_pos (by omega : 0 < 2), if_pos (by omega : 1 < 2)] at h
    exact h
  -- the same data for the lifted block
  have hlenL : (Lift1 X d).length = X.length := Lift1_length X d
  have hsrL : srow (Lift1 X d) ((Lift1 X d).length - 1) = 2 := by
    rw [hlenL, srow_Lift1 (by omega)]; exact hsr
  have hpL : hasParent (Lift1 X d) (srow (Lift1 X d) ((Lift1 X d).length - 1))
      ((Lift1 X d).length - 1) := by
    rw [hlenL, srow_Lift1 (by omega), hasParent_Lift1]; exact hp
  have hbpL : parent (Lift1 X d) (srow (Lift1 X d) ((Lift1 X d).length - 1))
      ((Lift1 X d).length - 1) = 0 := by
    rw [hlenL, srow_Lift1 (by omega), parent_Lift1]; exact hbp
  have hzL : ¬ (entry (Lift1 X d) 0 ((Lift1 X d).length - 1) = 0 ∧
      entry (Lift1 X d) 1 ((Lift1 X d).length - 1) = 0 ∧
      entry (Lift1 X d) 2 ((Lift1 X d).length - 1) = 0) := by
    rw [hlenL, ← hLdef, entry0_Lift1]
    rintro ⟨h0, -, -⟩; omega
  have hE1L : entry (Lift1 X d) 1 L = entry X 1 L + d := by
    rw [entry1_Lift1 (by omega), if_pos hcone]
  have hE10 : entry (Lift1 X d) 1 0 = entry X 1 0 + d := by
    rw [entry1_Lift1 (by omega), if_pos (le1_refl (by omega))]
  have hD0eq : entry (Lift1 X d) 0 L - entry (Lift1 X d) 0 0 = D0 := by
    rw [entry0_Lift1, entry0_Lift1, hD0]
  have hD1eq : entry (Lift1 X d) 1 L - entry (Lift1 X d) 1 0 = D1 := by
    rw [hE1L, hE10, hD1]; omega
  have hgexpL : (Lift1 X d)⟦n⟧ = gexp (Lift1 X d) 0 L D0 D1 n := by
    have h := oper_eq_gexp (M := Lift1 X d) n (by rw [hlenL]; omega) hzL hpL hbpL
    rw [hsrL, if_pos (by omega : 0 < 2), if_pos (by omega : 1 < 2), hlenL,
      ← hLdef, hD0eq, hD1eq] at h
    exact h
  rw [hgexpL, gexp_lift_eq_glift X L D0 D1 n d hlen hLpos, ← hgexpX,
    glift_eq_Lift1 (by omega) hgexpX hup hd0pos hd0e hd1pos hcone]
  exact hop n hn

/-! ### 枝 `1 ≤ badPar` に向けて: 錐輸送の易しい半分

`1 ≤ badPar` の可換性に要るのは「`X⟦n⟧` の**添字 0 からの**錐」であり、
`gexp_guard_transport` が運ぶ「`j0` からの錐」とは `j0 ≥ 1` では一致しない
（§1.9.60）。頭 `M.take j0` の部分だけは前置局所性（`le1_take`）で片付く。 -/

theorem le1_gexp_low {M : TrioSeq} {j0 Lb d0 d1 n p : ℕ}
    (hj0 : j0 ≤ M.length) (hp : p < j0) :
    le1 (gexp M j0 Lb d0 d1 n) 0 p ↔ le1 M 0 p := by
  have hlent : (M.take j0).length = j0 := by rw [List.length_take]; omega
  have htake : (gexp M j0 Lb d0 d1 n).take j0 = M.take j0 := by
    unfold gexp
    exact List.take_left' hlent
  have hj0len : j0 ≤ (gexp M j0 Lb d0 d1 n).length := by
    unfold gexp
    rw [List.length_append, hlent]
    omega
  rw [← le1_take hj0len hp, htake, le1_take hj0 hp]

/-- **The row-2 tower falls to (WL) over the LIFT-FREE `Wstar`.**  The tower's
induction only ever needs the single lift `d1`, so the `∀ s` strengthening (and
with it `Wstar2`, `GraftAll`, `GX`) is unnecessary once the stage law is
available. -/
theorem towerGraft2_of_liftStage (hWL : LiftStage) : Wset.TowerGraft2 := by
  classical
  intro v z m a R hR hRne hz1 hva hd hi1 hgr hpM n _
  set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
  set M : TrioSeq := p0 :: R with hMdef
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hMlen : M.length - 1 = R.length := by rw [hMdef]; simp
  have hE : ∀ i, entry M i R.length = entry R i (R.length - 1) :=
    fun i => entry_cons_last hRne i
  have hxpos : 0 < entry R 0 (R.length - 1) :=
    hR _ (entry_pair_mem (B := R) (by omega))
  have hL : M.length - 1 ≠ 0 := by rw [hMlen]; omega
  have hzz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0) := by
    rw [hMlen]; rintro ⟨h1, -, -⟩; rw [hE 0] at h1; omega
  have hsrM : srow M (M.length - 1) = 2 := by
    rw [hMlen, hMdef, srow_cons_last hRne, hi1]
  have hpM' : hasParent M (srow M (M.length - 1)) (M.length - 1) := by
    rw [hsrM, hMlen, hMdef, ← hi1]; exact hpM
  have hpar0 : parent M (srow M (M.length - 1)) (M.length - 1) = 0 := by
    rw [hsrM, hMlen]
    have := parent_cons_eq_zero (v := v) (z := z) hRne hd hpM
    rwa [hi1] at this
  have hroot1 : entry M 1 0 = v := by rw [hMdef]; simp [entry, hp0]
  have hroot2 : entry M 2 0 = z := by rw [hMdef]; simp [entry, hp0]
  have hnr := parent_nextR hpM'
  rw [hpar0, hsrM] at hnr
  have hn2 : nextrel2 M 0 (M.length - 1) := by
    unfold nextR at hnr
    rw [if_neg (by omega), if_neg (by omega)] at hnr
    exact hnr
  have hle1lp : le1 M 0 (M.length - 1) := hn2.2.2.2.2.1
  have hwv : v < entry R 1 (R.length - 1) := by
    have := le1_entry1_lt hle1lp (by omega)
    rw [hroot1, hMlen, hE 1] at this
    exact this
  have hz2 : z < entry R 2 (R.length - 1) := by
    have := hn2.2.2.2.1
    rw [hroot2, hMlen, hE 2] at this
    exact this
  set d1 : ℕ := entry R 1 (R.length - 1) - v with hd1
  have hlev := hd.1
  unfold lev at hlev
  have hbound : 2 * v + z + 2 * d1 ≤ m := by rw [hd1]; omega
  have hM0 : M⟦0⟧ = [] := by
    rw [oper_bad_unfold 0 hL hzz hpM', hpar0]
    simp
  have hstep : ∀ j, M⟦j + 1⟧ = p0 :: graft R (Lift1 (M⟦j⟧) d1) := by
    intro j
    rw [hd1]
    exact oper_cons_tower2 hR hRne hd hi1 hpM
  have hbased : ∀ j, based (M⟦j⟧) := by
    intro j
    cases j with
    | zero => rw [hM0]; exact based_nil
    | succ j => rw [hstep j]; exact based_cons v z _
  have key : ∀ j : ℕ, M⟦j⟧ ∈ W (2 * v + z) := by
    intro j
    induction j with
    | zero => rw [hM0]; exact W_nil _
    | succ j ih =>
        have hmem : Lift1 (M⟦j⟧) d1 ∈ W (2 * v + z + 2 * d1) := hWL _ _ _ ih
        have hmem' : Lift1 (M⟦j⟧) d1 ∈ W m := W_mono hbound hmem
        have hb : based (Lift1 (M⟦j⟧) d1) := based_Lift1 _ (hbased j)
        rw [hstep j]
        exact hgr _ hmem' hb (argOK_graft hRne hR _) v z (2 * v + z) hz1
          (le_refl _)
  exact W_mono hva (key n)

/-! ### 添字 0 からの錐輸送（`d0 > 0` の枝）

`1 ≤ badPar` の可換性 `(Lift1 X d)⟦n⟧ = Lift1 (X⟦n⟧) d` を列ごとに開くと、
頭の部分は `le1_gexp_low` で片付き、コピー領域には

```
(T0)   le1 (gexp M j0 Lb d0 d1 n) 0 (j0 + (k*Lb + q))  ↔  le1 M 0 (j0 + q)
```

だけが残る。`gexp_guard_transport` が運ぶのは `j0` からの錐なので、`j0 ≥ 1` では
これとは別物である（§1.9.60）。計測 `tools/probe_cone0.py`: 1812 ホスト・
85680 例で違反 0。

証明の骨格は次の切断である。窓 `(j0, j0+Lb]` の行 0 値はすべて `entry M 0 j0`
より真に大きい（`hup`）ので、**行 0 の鎖は窓に入る前に必ず `j0` を通る**。
切断の下側は接頭辞局所性（`le1_gexp_le`）でホストに戻り、上側は
`gexp_chain_inversion` で鏡映に分解する。ガードが立った位置では
`le1 M j0 ·` から行 1 値がすでに `entry M 1 j0` を超えているので、乗るリフト
`k*d1` は不等式を壊さない。 -/

/-- **A row-0 edge cannot jump over `j0`.**  If every column of `(j0, B]` sits
strictly above `j0` in row 0, then a `nextrel0` chain starting at or below `j0`
and ending inside the window factors through `j0` itself. -/
theorem rtg0_split_at {A : TrioSeq} {j0 B : ℕ}
    (hgt : ∀ l, j0 < l → l ≤ B → entry A 0 j0 < entry A 0 l)
    {a p : ℕ} (h : Relation.ReflTransGen (nextrel0 A) a p) (ha : a ≤ j0) :
    j0 ≤ p → p ≤ B →
      Relation.ReflTransGen (nextrel0 A) a j0 ∧
        Relation.ReflTransGen (nextrel0 A) j0 p := by
  induction h with
  | refl =>
      intro hp0 _
      have hj : a = j0 := by omega
      subst hj
      exact ⟨.refl, .refl⟩
  | @tail c p' hac hcp ih =>
      intro hp0 hp1
      have hclt : c < p' := hcp.2.2.1
      rcases Nat.lt_or_ge c j0 with hcj | hcj
      · rcases Nat.eq_or_lt_of_le hp0 with hj | hj
        · have hp'j : p' = j0 := by omega
          subst hp'j
          exact ⟨hac.tail hcp, .refl⟩
        · exfalso
          have hnodip := hcp.2.2.2.2 j0 ⟨hcj, hj⟩
          have := hgt p' hj hp1
          omega
      · obtain ⟨h1, h2⟩ := ih hcj (by omega)
        exact ⟨h1, h2.tail hcp⟩

/-- The copy-`0` root of the expansion is the host's bad root verbatim. -/
theorem gexp_getD_root {M : TrioSeq} {j0 Lb d0 d1 n : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hn : 0 < n) :
    (gexp M j0 Lb d0 d1 n).getD j0 (0, 0, 0) = M.getD j0 (0, 0, 0) := by
  have h := gexp_getD_mir (M := M) (j0 := j0) (Lb := Lb) (d0 := d0) (d1 := d1)
    (n := n) (k := 0) (q := 0) hlen hn hLb
  simp only [Nat.zero_mul, Nat.add_zero, ite_self] at h
  rw [h, getD_eq_entries]

/-- The expansion agrees with the host on the closed prefix `[0, j0]`. -/
theorem gexp_take_succ {M : TrioSeq} {j0 Lb d0 d1 n : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hn : 0 < n) :
    (gexp M j0 Lb d0 d1 n).take (j0 + 1) = M.take (j0 + 1) := by
  have hlenG : (gexp M j0 Lb d0 d1 n).length = j0 + n * Lb := gexp_length hlen
  have hnL : Lb ≤ n * Lb := Nat.le_mul_of_pos_left _ hn
  refine List.ext_getElem ?_ ?_
  · rw [List.length_take, List.length_take, hlenG]; omega
  · intro i hi1 hi2
    rw [List.length_take, hlenG] at hi1
    rw [List.getElem_take, List.getElem_take,
      getElem_eq_getD' (by omega), getElem_eq_getD' (by omega)]
    rcases Nat.lt_or_ge i j0 with h | h
    · exact gexp_getD_low hlen h
    · have hij : i = j0 := by omega
      subst hij
      exact gexp_getD_root hlen hLb hn

/-- **Closed-prefix locality of the `0`-cone** (the `p ≤ j0` strengthening of
`le1_gexp_low`; the bad root itself is included). -/
theorem le1_gexp_le {M : TrioSeq} {j0 Lb d0 d1 n p : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hn : 0 < n) (hp : p ≤ j0) :
    le1 (gexp M j0 Lb d0 d1 n) 0 p ↔ le1 M 0 p := by
  have hlenG : (gexp M j0 Lb d0 d1 n).length = j0 + n * Lb := gexp_length hlen
  have hnL : Lb ≤ n * Lb := Nat.le_mul_of_pos_left _ hn
  rw [← le1_take (X := gexp M j0 Lb d0 d1 n) (l := j0 + 1) (by omega) (by omega),
    gexp_take_succ hlen hLb hn,
    le1_take (X := M) (l := j0 + 1) (by omega) (by omega)]

/-- The row-0 profile of the copies region stays strictly above the bad root. -/
theorem gexp_entry0_gt_root {M : TrioSeq} {j0 Lb d0 d1 n : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hn : 0 < n)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hd0pos : 0 < d0) :
    ∀ l, j0 < l → l ≤ j0 + n * Lb - 1 →
      entry (gexp M j0 Lb d0 d1 n) 0 j0 < entry (gexp M j0 Lb d0 d1 n) 0 l := by
  have hnL : Lb ≤ n * Lb := Nat.le_mul_of_pos_left _ hn
  intro l hl0 hl1
  rw [gexp_entry_root hlen hn hLb]
  exact gexp_entry0_gt hlen hLb hup hd0pos l hl0 (by omega)

/-- **Cone-from-`0` transport** (probe `tools/probe_cone0.py`: 1812 hosts,
85680 instances, 0 violations).  For an ascending window (`d0 > 0`) the cone of
the sequence's own root is mirrored by the expansion — the companion of
`gexp_guard_transport`, which mirrors the cone of the bad root `j0`. -/
theorem gexp_cone0_transport {M : TrioSeq} {j0 Lb d0 d1 n k q : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hj0 : 0 < j0) (hLb : 0 < Lb)
    (hk : k < n) (hq : q < Lb)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hd0pos : 0 < d0) (hd0e : entry M 0 (j0 + Lb) = entry M 0 j0 + d0)
    (hcone : le1 M j0 (j0 + Lb)) :
    le1 (gexp M j0 Lb d0 d1 n) 0 (j0 + (k * Lb + q)) ↔ le1 M 0 (j0 + q) := by
  classical
  have hn : 0 < n := by omega
  have hnL : Lb ≤ n * Lb := Nat.le_mul_of_pos_left _ hn
  have hlenG : (gexp M j0 Lb d0 d1 n).length = j0 + n * Lb := gexp_length hlen
  have hbnd : k * Lb + q < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hgtG := gexp_entry0_gt_root (d1 := d1) hlen hLb hn hup hd0pos
  have hE10 : entry (gexp M j0 Lb d0 d1 n) 1 0 = entry M 1 0 := by
    show ((gexp M j0 Lb d0 d1 n).getD 0 (0, 0, 0)).2.1 = _
    rw [gexp_getD_low hlen hj0, getD_eq_entries]
  -- the row-0 chains that both sides ride on
  have hrtgM : ∀ r : ℕ, r < Lb → Relation.ReflTransGen (nextrel0 M) j0 (j0 + r) :=
    fun r hr => rtg0_of_window (by omega) (by omega)
      (fun l hl0 hl1 => hup l hl0 (by omega))
  have hrtgG : ∀ r : ℕ, r < n * Lb →
      Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n)) j0 (j0 + r) :=
    fun r hr => gexp_rtg0_root hlen hn hLb hup hd0pos _ (by omega) (by omega)
  constructor
  · -- `G`-side cone ⟹ `M`-side cone
    intro h
    obtain ⟨hsp1, hsp2⟩ :=
      rtg0_split_at hgtG (rtg0_of_rtg1 h.2.2) (Nat.zero_le _) (by omega) (by omega)
    have hG0j0 : le1 (gexp M j0 Lb d0 d1 n) 0 j0 :=
      (le1_iff_chain_window (by omega) hsp1).2
        (fun x hx1 hx2 hne => le1_chain_window h.2.2 x hx1 (hx2.trans hsp2) hne)
    have hM0j0 : le1 M 0 j0 := (le1_gexp_le hlen hLb hn le_rfl).1 hG0j0
    have hlt0 : entry M 1 0 < entry M 1 j0 := le1_entry1_lt hM0j0 (by omega)
    refine (le1_iff_chain_window (by omega)
      ((rtg0_of_rtg1 hM0j0.2.2).trans (hrtgM q hq))).2 ?_
    intro x hx1 hx2 hne
    rcases Nat.lt_or_ge x (j0 + 1) with hxl | hxg
    · obtain ⟨hs1, -⟩ := rtg0_split_at hup hx2 (by omega) (by omega) (by omega)
      exact le1_chain_window hM0j0.2.2 x hx1 hs1 hne
    · -- a window position: read it off the `k`-th mirror
      have hxle : x ≤ j0 + q := nextrel0_rtrancl_index_le hx2
      set q' : ℕ := x - j0 with hq'def
      have hxe : x = j0 + q' := by omega
      have hq'lt : q' < Lb := by omega
      have hx'2 : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n))
          (j0 + (k * Lb + q')) (j0 + (k * Lb + q)) :=
        gexp_rtg0_mir hlen hk (by rw [← hxe]; exact hx2) q rfl hq
      have hx'1 : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n)) 0
          (j0 + (k * Lb + q')) :=
        (rtg0_of_rtg1 hG0j0.2.2).trans (hrtgG _ (by omega))
      have hwin := le1_chain_window h.2.2 (j0 + (k * Lb + q')) hx'1 hx'2
        (by omega)
      rw [hE10] at hwin
      have hval : entry (gexp M j0 Lb d0 d1 n) 1 (j0 + (k * Lb + q'))
          = entry M 1 (j0 + q')
            + (if le1 M j0 (j0 + q') then k * d1 else 0) := by
        show ((gexp M j0 Lb d0 d1 n).getD (j0 + (k * Lb + q')) (0, 0, 0)).2.1 = _
        rw [gexp_getD_mir hlen hk hq'lt]
      rw [hval] at hwin
      rw [hxe]
      by_cases hg : le1 M j0 (j0 + q')
      · have := le1_entry1_lt hg (by omega)
        omega
      · rw [if_neg hg] at hwin
        omega
  · -- `M`-side cone ⟹ `G`-side cone
    intro h
    obtain ⟨hsp1, hsp2⟩ :=
      rtg0_split_at hup (rtg0_of_rtg1 h.2.2) (Nat.zero_le _) (by omega) (by omega)
    have hM0j0 : le1 M 0 j0 :=
      (le1_iff_chain_window (by omega) hsp1).2
        (fun x hx1 hx2 hne => le1_chain_window h.2.2 x hx1 (hx2.trans hsp2) hne)
    have hlt0 : entry M 1 0 < entry M 1 j0 := le1_entry1_lt hM0j0 (by omega)
    have hG0j0 : le1 (gexp M j0 Lb d0 d1 n) 0 j0 :=
      (le1_gexp_le hlen hLb hn le_rfl).2 hM0j0
    refine (le1_iff_chain_window (by omega)
      ((rtg0_of_rtg1 hG0j0.2.2).trans (hrtgG _ hbnd))).2 ?_
    intro x hx1 hx2 hne
    rcases Nat.lt_or_ge x (j0 + 1) with hxl | hxg
    · obtain ⟨hs1, -⟩ := rtg0_split_at hgtG hx2 (by omega) (by omega) (by omega)
      exact le1_chain_window hG0j0.2.2 x hx1 hs1 hne
    · obtain ⟨k', q', hk', hq', rfl, hcase⟩ :=
        gexp_chain_inversion hlen hk hq hup hd0e x hx2 (by omega)
      rw [hE10]
      have hval : entry (gexp M j0 Lb d0 d1 n) 1 (j0 + (k' * Lb + q'))
          = entry M 1 (j0 + q')
            + (if le1 M j0 (j0 + q') then k' * d1 else 0) := by
        show ((gexp M j0 Lb d0 d1 n).getD (j0 + (k' * Lb + q')) (0, 0, 0)).2.1 = _
        rw [gexp_getD_mir hlen (by omega) hq']
      rw [hval]
      rcases Nat.eq_zero_or_pos q' with rfl | hq'pos
      · -- a copy root: it carries the bad root's row 1, possibly lifted
        rw [Nat.add_zero]
        split_ifs <;> omega
      · have hM0q' : Relation.ReflTransGen (nextrel0 M) 0 (j0 + q') :=
          (rtg0_of_rtg1 hM0j0.2.2).trans (hrtgM _ hq')
        rcases hcase with ⟨-, hM⟩ | ⟨-, hM⟩
        · have := le1_chain_window h.2.2 (j0 + q') hM0q' hM (by omega)
          split_ifs <;> omega
        · have := le1_chain_window hcone.2.2 (j0 + q') (hrtgM _ hq') hM (by omega)
          split_ifs <;> omega

/-- **The root lift commutes with an expansion whose bad root is not the
sequence's own root.**  The two masks are cones of *different* roots — the lift
rides on `le1 X 0 ·`, the copies on `le1 X j0 ·` — so they simply add up on each
mirror, as soon as the `0`-cone is mirrored (`htr`). -/
theorem gexp_Lift1_comm_of_transport {X : TrioSeq} {j0 Lb D0 D1 n d : ℕ}
    (hlen : j0 + Lb + 1 = X.length) (hLb : 0 < Lb) (hn : 0 < n)
    (htr : ∀ k q, k < n → q < Lb →
      (le1 (gexp X j0 Lb D0 D1 n) 0 (j0 + (k * Lb + q)) ↔ le1 X 0 (j0 + q))) :
    gexp (Lift1 X d) j0 Lb D0 D1 n = Lift1 (gexp X j0 Lb D0 D1 n) d := by
  classical
  have hlenLX : (Lift1 X d).length = X.length := Lift1_length X d
  have hlenL' : j0 + Lb + 1 = (Lift1 X d).length := by rw [hlenLX]; exact hlen
  have hlenG : (gexp X j0 Lb D0 D1 n).length = j0 + n * Lb := gexp_length hlen
  have hlenGL : (gexp (Lift1 X d) j0 Lb D0 D1 n).length = j0 + n * Lb :=
    gexp_length hlenL'
  have hnL : Lb ≤ n * Lb := Nat.le_mul_of_pos_left _ hn
  refine List.ext_getElem (by rw [hlenGL, Lift1_length, hlenG]) ?_
  intro i hia hib
  rw [hlenGL] at hia
  rw [getElem_eq_getD' (by omega), getElem_eq_getD' (by rw [Lift1_length]; omega),
    Lift1_getD (by omega)]
  rcases Nat.lt_or_ge i j0 with hlow | hhigh
  · -- head: both sides read the host verbatim
    have hlowX : (gexp X j0 Lb D0 D1 n).getD i (0, 0, 0) = X.getD i (0, 0, 0) :=
      gexp_getD_low hlen hlow
    have hE : ∀ y, entry (gexp X j0 Lb D0 D1 n) y i = entry X y i := by
      intro y; unfold entry; rw [hlowX]
    rw [gexp_getD_low hlenL' hlow, Lift1_getD (by omega), hE 0, hE 1, hE 2,
      le1_gexp_low (by omega) hlow]
  · -- copies: the two masks add up
    obtain ⟨k, q, hk, hq, rfl⟩ := gexp_pos_decomp hLb hhigh (by omega)
    have hmir : (gexp X j0 Lb D0 D1 n).getD (j0 + (k * Lb + q)) (0, 0, 0)
        = (entry X 0 (j0 + q) + k * D0,
           entry X 1 (j0 + q) + (if le1 X j0 (j0 + q) then k * D1 else 0),
           entry X 2 (j0 + q)) := gexp_getD_mir hlen hk hq
    have hE0 : entry (gexp X j0 Lb D0 D1 n) 0 (j0 + (k * Lb + q))
        = entry X 0 (j0 + q) + k * D0 := by
      show ((gexp X j0 Lb D0 D1 n).getD (j0 + (k * Lb + q)) (0, 0, 0)).1 = _
      rw [hmir]
    have hE1 : entry (gexp X j0 Lb D0 D1 n) 1 (j0 + (k * Lb + q))
        = entry X 1 (j0 + q) + (if le1 X j0 (j0 + q) then k * D1 else 0) := by
      show ((gexp X j0 Lb D0 D1 n).getD (j0 + (k * Lb + q)) (0, 0, 0)).2.1 = _
      rw [hmir]
    have hE2 : entry (gexp X j0 Lb D0 D1 n) 2 (j0 + (k * Lb + q))
        = entry X 2 (j0 + q) := by
      show ((gexp X j0 Lb D0 D1 n).getD (j0 + (k * Lb + q)) (0, 0, 0)).2.2 = _
      rw [hmir]
    rw [gexp_getD_mir hlenL' hk hq, hE0, hE1, hE2, entry0_Lift1, entry2_Lift1,
      entry1_Lift1 (by omega)]
    simp only [le1_Lift1, htr k q hk hq]
    rw [Nat.add_right_comm]

/-- The ascending instance of `gexp_Lift1_comm_of_transport`. -/
theorem gexp_Lift1_comm {X : TrioSeq} {j0 Lb D0 D1 n d : ℕ}
    (hlen : j0 + Lb + 1 = X.length) (hj0 : 0 < j0) (hLb : 0 < Lb) (hn : 0 < n)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry X 0 j0 < entry X 0 l)
    (hd0pos : 0 < D0) (hd0e : entry X 0 (j0 + Lb) = entry X 0 j0 + D0)
    (hcone : le1 X j0 (j0 + Lb)) :
    gexp (Lift1 X d) j0 Lb D0 D1 n = Lift1 (gexp X j0 Lb D0 D1 n) d :=
  gexp_Lift1_comm_of_transport hlen hLb hn
    (fun _ _ hk hq => gexp_cone0_transport hlen hj0 hLb hk hq hup hd0pos hd0e hcone)

/-! ### 添字 0 からの錐輸送（平坦な枝 `i1 = 0`）

`Lcone.lean` の平坦版（`nextrel0_flat_root` / `gexp_flat_chain_inversion` /
`gexp_flat_rtg0_low`）は「根が厳密に最浅」`hr0` を仮定した
`gexp_cone_mir_flat` にしか使われていないが、`LSPOn` は **`W` の任意の元**に
対する主張なので `hr0` は使えない。切断補題 `rtg0_split_at`（切断点はコピー
`k` の根）で `hr0` を外した版を作る。 -/

/-- In a flat expansion every row-0 predecessor of a copy root sits below `j0`
(the copy roots all carry the host root's depth). -/
theorem gexp_flat_pred_low {M : TrioSeq} {j0 Lb n k a : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hk : k < n)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (h : nextrel0 (gexp M j0 Lb 0 0 n) a (j0 + k * Lb)) : a < j0 := by
  by_contra hcon
  have halt : a < j0 + n * Lb := by
    have h1 := h.1
    rw [gexp_length hlen] at h1
    exact h1
  have hge := gexp_flat_ge (n := n) hlen hLb hup a (by omega) halt
  have hlt := h.2.2.2.1
  rw [gexp_flat_root_entry hlen hk hLb] at hlt
  omega

/-- Hence a row-0 ancestor of a copy root is either the root itself or below
`j0`: the copy roots do not chain to each other. -/
theorem gexp_flat_anc_root {M : TrioSeq} {j0 Lb n k a : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hk : k < n)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (h : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb 0 0 n)) a (j0 + k * Lb)) :
    a = j0 + k * Lb ∨ a < j0 := by
  rcases h.cases_tail with heq | ⟨c, hac, hc⟩
  · exact Or.inl heq.symm
  · have hcl := gexp_flat_pred_low hlen hLb hk hup hc
    have := nextrel0_rtrancl_index_le hac
    exact Or.inr (by omega)

/-- **Every copy root carries the host root's `0`-cone.** -/
theorem le1_gexp_flat_root {M : TrioSeq} {j0 Lb n k : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hj0 : 0 < j0) (hLb : 0 < Lb) (hk : k < n)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l) :
    le1 (gexp M j0 Lb 0 0 n) 0 (j0 + k * Lb) ↔ le1 M 0 j0 := by
  have hn : 0 < n := by omega
  have hbnd : k * Lb < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hlenG : (gexp M j0 Lb 0 0 n).length = j0 + n * Lb := gexp_length hlen
  have hE10 : entry (gexp M j0 Lb 0 0 n) 1 0 = entry M 1 0 :=
    gexp_entry_low hlen hj0
  have hEr : ∀ y, entry (gexp M j0 Lb 0 0 n) y (j0 + k * Lb) = entry M y j0 :=
    fun y => gexp_flat_root_entry hlen hk hLb
  have hchain : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb 0 0 n)) 0
      (j0 + k * Lb) ↔ Relation.ReflTransGen (nextrel0 M) 0 j0 := by
    constructor
    · intro h
      rcases h.cases_tail with heq | ⟨c, hac, hc⟩
      · exact absurd heq.symm (by omega)
      · have hcl := gexp_flat_pred_low hlen hLb hk hup hc
        exact ((gexp_flat_rtg0_low hlen hLb hn hcl).1 hac).tail
          ((nextrel0_flat_root hlen hLb hk hcl hup).1 hc)
    · intro h
      rcases h.cases_tail with heq | ⟨c, hac, hc⟩
      · exact absurd heq.symm (by omega)
      · have hcl : c < j0 := hc.2.2.1
        exact ((gexp_flat_rtg0_low hlen hLb hn hcl).2 hac).tail
          ((nextrel0_flat_root hlen hLb hk hcl hup).2 hc)
  constructor
  · intro h
    have hlt0 : entry M 1 0 < entry M 1 j0 := by
      have := le1_entry1_lt h (by omega)
      rwa [hE10, hEr 1] at this
    refine (le1_iff_chain_window (by omega) (hchain.1 (rtg0_of_rtg1 h.2.2))).2 ?_
    intro x hx1 hx2 hne
    have hxj : x ≤ j0 := nextrel0_rtrancl_index_le hx2
    rcases Nat.eq_or_lt_of_le hxj with hxe | hxl
    · rw [hxe]; exact hlt0
    · have hGx1 := (gexp_flat_rtg0_low hlen hLb hn hxl).2 hx1
      have hGx2 : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb 0 0 n)) x
          (j0 + k * Lb) := by
        rcases hx2.cases_tail with heq | ⟨c, hac, hc⟩
        · exact absurd heq (by omega)
        · have hcl : c < j0 := hc.2.2.1
          exact ((gexp_flat_rtg0_low hlen hLb hn hcl).2 hac).tail
            ((nextrel0_flat_root hlen hLb hk hcl hup).2 hc)
      have := le1_chain_window h.2.2 x hGx1 hGx2 hne
      rwa [hE10, gexp_entry_low hlen hxl] at this
  · intro h
    have hlt0 : entry M 1 0 < entry M 1 j0 := le1_entry1_lt h (by omega)
    refine (le1_iff_chain_window (by omega) (hchain.2 (rtg0_of_rtg1 h.2.2))).2 ?_
    intro x hx1 hx2 hne
    rcases gexp_flat_anc_root hlen hLb hk hup hx2 with hxe | hxl
    · rw [hxe, hE10, hEr 1]; exact hlt0
    · have hMx1 := (gexp_flat_rtg0_low hlen hLb hn hxl).1 hx1
      have hMx2 : Relation.ReflTransGen (nextrel0 M) x j0 := by
        rcases hx2.cases_tail with heq | ⟨c, hac, hc⟩
        · exact absurd heq (by omega)
        · have hcl := gexp_flat_pred_low hlen hLb hk hup hc
          exact ((gexp_flat_rtg0_low hlen hLb hn hcl).1 hac).tail
            ((nextrel0_flat_root hlen hLb hk hcl hup).1 hc)
      have := le1_chain_window h.2.2 x hMx1 hMx2 hne
      rwa [hE10, gexp_entry_low hlen hxl]

/-- **Cone-from-`0` transport, flat case** — the `hr0`-free form of
`Lcone.gexp_cone_mir_flat`, split at the copy root instead of at `j0`. -/
theorem gexp_cone0_flat {M : TrioSeq} {j0 Lb n k q : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hj0 : 0 < j0) (hLb : 0 < Lb)
    (hk : k < n) (hq : q < Lb)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l) :
    le1 (gexp M j0 Lb 0 0 n) 0 (j0 + (k * Lb + q)) ↔ le1 M 0 (j0 + q) := by
  have hn : 0 < n := by omega
  have hbnd : k * Lb + q < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hlenG : (gexp M j0 Lb 0 0 n).length = j0 + n * Lb := gexp_length hlen
  have hE10 : entry (gexp M j0 Lb 0 0 n) 1 0 = entry M 1 0 :=
    gexp_entry_low hlen hj0
  have hrtgM : ∀ r : ℕ, r < Lb → Relation.ReflTransGen (nextrel0 M) j0 (j0 + r) :=
    fun r hr => rtg0_of_window (by omega) (by omega)
      (fun l hl0 hl1 => hup l hl0 (by omega))
  have hrtgGk := gexp_flat_rtg0_root (M := M) (n := n) hlen hLb hk hq hn hup
  -- the split point is the copy root, not `j0`
  have hgtk : ∀ l, j0 + k * Lb < l → l ≤ j0 + (k * Lb + q) →
      entry (gexp M j0 Lb 0 0 n) 0 (j0 + k * Lb)
        < entry (gexp M j0 Lb 0 0 n) 0 l := by
    intro l hl0 hl1
    obtain ⟨q', hq'0, hq'1, rfl⟩ :
        ∃ q', 0 < q' ∧ q' ≤ q ∧ l = j0 + (k * Lb + q') :=
      ⟨l - j0 - k * Lb, by omega, by omega, by omega⟩
    rw [gexp_flat_root_entry hlen hk hLb, gexp_flat_entry hlen hk (by omega)]
    exact hup (j0 + q') (by omega) (by omega)
  constructor
  · intro h
    obtain ⟨hsp1, hsp2⟩ :=
      rtg0_split_at hgtk (rtg0_of_rtg1 h.2.2) (Nat.zero_le _) (by omega) le_rfl
    have hGr : le1 (gexp M j0 Lb 0 0 n) 0 (j0 + k * Lb) :=
      (le1_iff_chain_window (by omega) hsp1).2
        (fun x hx1 hx2 hne => le1_chain_window h.2.2 x hx1 (hx2.trans hsp2) hne)
    have hMj0 : le1 M 0 j0 := (le1_gexp_flat_root hlen hj0 hLb hk hup).1 hGr
    refine (le1_iff_chain_window (by omega)
      ((rtg0_of_rtg1 hMj0.2.2).trans (hrtgM q hq))).2 ?_
    intro x hx1 hx2 hne
    rcases Nat.lt_or_ge x (j0 + 1) with hxl | hxg
    · obtain ⟨hs1, -⟩ := rtg0_split_at hup hx2 (by omega) (by omega) (by omega)
      exact le1_chain_window hMj0.2.2 x hx1 hs1 hne
    · have hxle : x ≤ j0 + q := nextrel0_rtrancl_index_le hx2
      obtain ⟨q', hq'0, hq'1, rfl⟩ : ∃ q', 0 < q' ∧ q' ≤ q ∧ x = j0 + q' :=
        ⟨x - j0, by omega, by omega, by omega⟩
      have hx'1 : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb 0 0 n)) 0
          (j0 + (k * Lb + q')) :=
        ((rtg0_of_rtg1 hGr.2.2).trans
          (gexp_flat_rtg0_root (M := M) (n := n) hlen hLb hk (by omega) hn hup))
      have hx'2 : Relation.ReflTransGen (nextrel0 (gexp M j0 Lb 0 0 n))
          (j0 + (k * Lb + q')) (j0 + (k * Lb + q)) :=
        gexp_rtg0_mir hlen hk hx2 q rfl hq
      have hwin := le1_chain_window h.2.2 _ hx'1 hx'2 (by omega)
      rwa [hE10, gexp_flat_entry hlen hk (by omega)] at hwin
  · intro h
    obtain ⟨hsp1, hsp2⟩ :=
      rtg0_split_at hup (rtg0_of_rtg1 h.2.2) (Nat.zero_le _) (by omega) (by omega)
    have hMj0 : le1 M 0 j0 :=
      (le1_iff_chain_window (by omega) hsp1).2
        (fun x hx1 hx2 hne => le1_chain_window h.2.2 x hx1 (hx2.trans hsp2) hne)
    have hlt0 : entry M 1 0 < entry M 1 j0 := le1_entry1_lt hMj0 (by omega)
    have hGr : le1 (gexp M j0 Lb 0 0 n) 0 (j0 + k * Lb) :=
      (le1_gexp_flat_root hlen hj0 hLb hk hup).2 hMj0
    refine (le1_iff_chain_window (by omega)
      ((rtg0_of_rtg1 hGr.2.2).trans hrtgGk)).2 ?_
    intro x hx1 hx2 hne
    rcases Nat.lt_or_ge x j0 with hxl | hxg
    · obtain ⟨hs1, -⟩ := rtg0_split_at hgtk hx2 (by omega) (by omega) le_rfl
      exact le1_chain_window hGr.2.2 x hx1 hs1 hne
    · obtain ⟨q', hq', rfl, hM⟩ :=
        gexp_flat_chain_inversion hlen hLb hk hq hup x hx2 hxg
      rw [hE10, gexp_flat_entry hlen hk hq']
      rcases Nat.eq_zero_or_pos q' with rfl | hq'pos
      · rw [Nat.add_zero]; exact hlt0
      · have hM0q' : Relation.ReflTransGen (nextrel0 M) 0 (j0 + q') :=
          (rtg0_of_rtg1 hMj0.2.2).trans (hrtgM _ hq')
        exact le1_chain_window h.2.2 (j0 + q') hM0q' hM (by omega)

/-- The flat instance of `gexp_Lift1_comm_of_transport`. -/
theorem gexp_Lift1_comm_flat {X : TrioSeq} {j0 Lb n d : ℕ}
    (hlen : j0 + Lb + 1 = X.length) (hj0 : 0 < j0) (hLb : 0 < Lb) (hn : 0 < n)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry X 0 j0 < entry X 0 l) :
    gexp (Lift1 X d) j0 Lb 0 0 n = Lift1 (gexp X j0 Lb 0 0 n) d :=
  gexp_Lift1_comm_of_transport hlen hLb hn
    (fun _ _ hk hq => gexp_cone0_flat hlen hj0 hLb hk hq hup)

/-- A collapse row above `0` means the last column is nonzero in that row. -/
theorem entry_pos_of_srow {X : TrioSeq} {j : ℕ} (h : 1 ≤ srow X j) :
    0 < entry X 1 j ∨ 0 < entry X 2 j := by
  unfold srow at h
  split at h
  · exact Or.inr (by assumption)
  · split at h
    · exact Or.inl (by assumption)
    · omega

/-- The collapse row `i1 ≥ 1` puts the bad root in the row-1 cone of the last
column, which is what makes the two lift masks nest. -/
theorem le1_parent_of_srow_pos {X : TrioSeq} {i1 j0 j1 : ℕ} (hi1 : 1 ≤ i1)
    (hnr : nextR X i1 j0 j1) : le1 X j0 j1 := by
  unfold nextR at hnr
  rw [if_neg (by omega)] at hnr
  rcases Nat.lt_or_ge i1 2 with h | h
  · rw [if_pos (by omega)] at hnr
    exact ⟨hnr.1, hnr.2.1, Relation.ReflTransGen.single hnr⟩
  · rw [if_neg (by omega)] at hnr
    exact hnr.2.2.2.2.1

/-- **The branch `1 ≤ badPar`, ascending collapse (`i1 ≥ 1`)**: `oper` commutes
with the root lift.  All the expansion data (`j0`, `Lb`, `D0`, `D1`) is
transported verbatim by `Lift1`; the row-1 datum `D1` survives because the bad
root and the last column lie in the *same* `0`-cone (`le1_of_le1_le1`), so the
lift cancels in the difference. -/
theorem lift_oper_comm_of_parent {X : TrioSeq} {d n : ℕ} (h2 : 2 ≤ X.length)
    (hp : hasParent X (srow X (X.length - 1)) (X.length - 1))
    (hjpos : 0 < parent X (srow X (X.length - 1)) (X.length - 1))
    (hi1 : 1 ≤ srow X (X.length - 1)) (hn : 0 < n) :
    (Lift1 X d)⟦n⟧ = Lift1 (X⟦n⟧) d := by
  classical
  have hlenL : (Lift1 X d).length = X.length := Lift1_length X d
  have hnr := parent_nextR hp
  have hlt : parent X (srow X (X.length - 1)) (X.length - 1) < X.length - 1 :=
    nextR_index_lt hnr
  have hch0 := nextR_chain0 hnr
  have hj1ne : X.length - 1 ≠ 0 := by omega
  set j1 : ℕ := X.length - 1 with hj1def
  set i1 : ℕ := srow X j1 with hi1def
  set j0 : ℕ := parent X i1 j1 with hj0def
  set Lb : ℕ := j1 - j0 with hLbdef
  have hlen : j0 + Lb + 1 = X.length := by omega
  have hLb : 0 < Lb := by omega
  have hj1e : j0 + Lb = j1 := by omega
  have hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry X 0 j0 < entry X 0 l := by
    have hw := window_of_rtg0 hch0 (by omega)
    intro l hl0 hl1
    exact hw l hl0 (by omega)
  have hcone : le1 X j0 (j0 + Lb) := by rw [hj1e]; exact le1_parent_of_srow_pos hi1 hnr
  set D0 : ℕ := if 0 < i1 then entry X 0 j1 - entry X 0 j0 else 0 with hD0def
  set D1 : ℕ := if 1 < i1 then entry X 1 j1 - entry X 1 j0 else 0 with hD1def
  have hd0pos : 0 < D0 := by
    rw [hD0def, if_pos (by omega)]
    have := hup j1 (by omega) (by omega)
    omega
  have hd0e : entry X 0 (j0 + Lb) = entry X 0 j0 + D0 := by
    rw [hj1e, hD0def, if_pos (by omega)]
    have := hup j1 (by omega) (by omega)
    omega
  -- the two `oper` presentations, sharing the same data
  have hpos1 : 0 < entry X 1 j1 ∨ 0 < entry X 2 j1 := entry_pos_of_srow hi1
  have hz : ¬ (entry X 0 j1 = 0 ∧ entry X 1 j1 = 0 ∧ entry X 2 j1 = 0) := by
    rintro ⟨-, ha, hb⟩; omega
  have hgX : X⟦n⟧ = gexp X j0 Lb D0 D1 n := by
    have h := oper_gcopies (M := X) n hj1ne hz hp
    rw [← hj1def, ← hi1def, ← hj0def, ← hLbdef, ← hD0def, ← hD1def] at h
    unfold gexp
    exact h
  -- the lifted side: every datum transports
  have hlenL1 : (Lift1 X d).length - 1 = j1 := by rw [hlenL]
  have hsrL : srow (Lift1 X d) j1 = i1 := srow_Lift1 hj1ne
  have hpL : hasParent (Lift1 X d) (srow (Lift1 X d) ((Lift1 X d).length - 1))
      ((Lift1 X d).length - 1) := by
    rw [hlenL1, hsrL, hasParent_Lift1]; exact hp
  have hzL : ¬ (entry (Lift1 X d) 0 ((Lift1 X d).length - 1) = 0 ∧
      entry (Lift1 X d) 1 ((Lift1 X d).length - 1) = 0 ∧
      entry (Lift1 X d) 2 ((Lift1 X d).length - 1) = 0) := by
    rw [hlenL1, entry0_Lift1, entry2_Lift1, entry1_Lift1 (by omega)]
    rintro ⟨-, ha, hb⟩
    omega
  -- the row-1 datum: the bad root and the last column share the `0`-cone
  have hg01 : le1 X 0 j0 ↔ le1 X 0 j1 := by
    constructor
    · intro h; rw [← hj1e]; exact le1_trans h hcone
    · intro h; exact le1_of_le1_le1 h (by rw [← hj1e]; exact hcone) (by omega)
  have hD1L : (if 1 < i1 then entry (Lift1 X d) 1 j1
        - entry (Lift1 X d) 1 j0 else 0) = D1 := by
    rw [entry1_Lift1 (by omega), entry1_Lift1 (by omega), hD1def]
    by_cases hc : le1 X 0 j0
    · rw [if_pos hc, if_pos (hg01.1 hc)]
      split_ifs <;> omega
    · rw [if_neg hc, if_neg (fun hcon => hc (hg01.2 hcon))]
      split_ifs <;> omega
  have hgL : (Lift1 X d)⟦n⟧ = gexp (Lift1 X d) j0 Lb D0 D1 n := by
    have h := oper_gcopies (M := Lift1 X d) n (by rw [hlenL1]; exact hj1ne) hzL hpL
    rw [hlenL1, hsrL, parent_Lift1, ← hj0def, entry0_Lift1, entry0_Lift1,
      hD1L] at h
    rw [show j1 - j0 = Lb from hLbdef.symm, ← hD0def] at h
    unfold gexp
    exact h
  rw [hgL, hgX, gexp_Lift1_comm hlen hjpos hLb hn hup hd0pos hd0e hcone]

/-- Splitting the `1 ≤ badPar` residue by the collapse row. -/
theorem lspOn_pos_of
    (h0 : LSPOn (fun X => 1 ≤ badPar X ∧ srow X (X.length - 1) = 0))
    (hhi : LSPOn (fun X => 1 ≤ badPar X ∧ 1 ≤ srow X (X.length - 1))) :
    LSPOn (fun X => 1 ≤ badPar X) := by
  intro m d X h2 hp hpos hop n hn
  rcases Nat.eq_zero_or_pos (srow X (X.length - 1)) with hs | hs
  · exact h0 m d X h2 hp ⟨hpos, hs⟩ hop n hn
  · exact hhi m d X h2 hp ⟨hpos, hs⟩ hop n hn

/-- **Branch `1 ≤ badPar`, `i1 ≥ 1`** — commutation, so the stage is inherited
straight from the hypothesis on `X⟦n⟧`. -/
theorem lspOn_pos_hi :
    LSPOn (fun X => 1 ≤ badPar X ∧ 1 ≤ srow X (X.length - 1)) := by
  rintro m d X h2 hp ⟨hjpos, hi1⟩ hop n hn
  rw [lift_oper_comm_of_parent h2 hp hjpos hi1 (by omega)]
  exact hop n hn

/-- **The branch `1 ≤ badPar`, flat collapse (`i1 = 0`)**: `D0 = D1 = 0`, so the
copies are literal duplicates and only the `0`-cone has to be transported. -/
theorem lift_oper_comm_of_parent_flat {X : TrioSeq} {d n : ℕ} (h2 : 2 ≤ X.length)
    (hp : hasParent X (srow X (X.length - 1)) (X.length - 1))
    (hjpos : 0 < parent X (srow X (X.length - 1)) (X.length - 1))
    (hi1 : srow X (X.length - 1) = 0) (hn : 0 < n) :
    (Lift1 X d)⟦n⟧ = Lift1 (X⟦n⟧) d := by
  classical
  have hlenL : (Lift1 X d).length = X.length := Lift1_length X d
  have hnr := parent_nextR hp
  have hlt : parent X (srow X (X.length - 1)) (X.length - 1) < X.length - 1 :=
    nextR_index_lt hnr
  have hch0 := nextR_chain0 hnr
  have hj1ne : X.length - 1 ≠ 0 := by omega
  set j1 : ℕ := X.length - 1 with hj1def
  set i1 : ℕ := srow X j1 with hi1def
  set j0 : ℕ := parent X i1 j1 with hj0def
  set Lb : ℕ := j1 - j0 with hLbdef
  have hlen : j0 + Lb + 1 = X.length := by omega
  have hLb : 0 < Lb := by omega
  have hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry X 0 j0 < entry X 0 l := by
    have hw := window_of_rtg0 hch0 (by omega)
    intro l hl0 hl1
    exact hw l hl0 (by omega)
  have hdeep : entry X 0 j0 < entry X 0 j1 := hup j1 (by omega) (by omega)
  have hz : ¬ (entry X 0 j1 = 0 ∧ entry X 1 j1 = 0 ∧ entry X 2 j1 = 0) := by
    rintro ⟨h0, -, -⟩; omega
  have hgX : X⟦n⟧ = gexp X j0 Lb 0 0 n := by
    have h := oper_gcopies (M := X) n hj1ne hz hp
    rw [← hj1def, ← hi1def, ← hj0def, ← hLbdef,
      if_neg (show ¬ (0 < i1) by omega), if_neg (show ¬ (1 < i1) by omega)] at h
    unfold gexp
    exact h
  have hlenL1 : (Lift1 X d).length - 1 = j1 := by rw [hlenL]
  have hsrL : srow (Lift1 X d) j1 = i1 := srow_Lift1 hj1ne
  have hpL : hasParent (Lift1 X d) (srow (Lift1 X d) ((Lift1 X d).length - 1))
      ((Lift1 X d).length - 1) := by
    rw [hlenL1, hsrL, hasParent_Lift1]; exact hp
  have hzL : ¬ (entry (Lift1 X d) 0 ((Lift1 X d).length - 1) = 0 ∧
      entry (Lift1 X d) 1 ((Lift1 X d).length - 1) = 0 ∧
      entry (Lift1 X d) 2 ((Lift1 X d).length - 1) = 0) := by
    rw [hlenL1, entry0_Lift1]
    rintro ⟨h0, -, -⟩; omega
  have hgL : (Lift1 X d)⟦n⟧ = gexp (Lift1 X d) j0 Lb 0 0 n := by
    have h := oper_gcopies (M := Lift1 X d) n (by rw [hlenL1]; exact hj1ne) hzL hpL
    rw [hlenL1, hsrL, parent_Lift1, ← hj0def,
      if_neg (show ¬ (0 < i1) by omega), if_neg (show ¬ (1 < i1) by omega),
      show j1 - j0 = Lb from hLbdef.symm] at h
    unfold gexp
    exact h
  rw [hgL, hgX, gexp_Lift1_comm_flat hlen hjpos hLb hn hup]

/-- **Branch `1 ≤ badPar`, `i1 = 0`.** -/
theorem lspOn_pos_lo :
    LSPOn (fun X => 1 ≤ badPar X ∧ srow X (X.length - 1) = 0) := by
  rintro m d X h2 hp ⟨hjpos, hi1⟩ hop n hn
  rw [lift_oper_comm_of_parent_flat h2 hp hjpos hi1 (by omega)]
  exact hop n hn

/-- **The whole branch `1 ≤ badPar` is closed.** -/
theorem lspOn_pos : LSPOn (fun X => 1 ≤ badPar X) :=
  lspOn_pos_of lspOn_pos_lo lspOn_pos_hi

/-- **(WL) now rests on the two `badPar = 0` collapse rows `0` and `1`** — and
row `0` is `lspOn_srow0`, so the sole open branch is the row-1 graft tower. -/
theorem liftStageParented_of_srow1
    (hs1 : LSPOn (fun X => badPar X = 0 ∧ srow X (X.length - 1) = 1)) :
    LiftStageParented :=
  liftStageParented_of_cases lspOn_pos lspOn_srow2 lspOn_srow0 hs1

/-! ### 最後の枝 `badPar = 0, i1 = 1` を**行 0 ずらしコピー塔**に還元する

`i1 = 1` では `d1 = 0`、`d0 = entry X 0 j1 - entry X 0 0 > 0` なので、展開は
`X.dropLast` の行 0 ずらしコピー塔そのものである:

```
X⟦n⟧ = shTower X.dropLast d0 n = ⧺_{k<n} shiftr01 (k*d0) 0 X.dropLast
```

`Lift1` は行 0 を動かさないので同じ `d0` で `(Lift1 X d)⟦n⟧ = shTower Q d0 n`
（`Q = Lift1 X.dropLast d`）。ここで仮定 `hop` は **`n = 1` でだけ**使えば足りる:
`X⟦1⟧ = X.dropLast` なので `hop 1` がそのまま `Q ∈ W (m+2d)` を与える。
したがってこの枝は

```
(TOW)   Q ∈ W u → （根が最浅） → shTower Q e n ∈ W u
```

という**リフトを一切含まない純粋な `W` の閉包**に還元される。計測
`tools/probe_core1.py` (C): 6244 例で違反 0、しかも `minstage` は**等号**
（塔は段を一切上げない）。 -/

/-- The row-0-shifted copy tower: `n` copies of `Q`, the `k`-th sunk by `k * e`. -/
def shTower (Q : TrioSeq) (e n : ℕ) : TrioSeq :=
  (List.range n).flatMap fun k => shiftr01 (k * e) 0 Q

@[simp] theorem shTower_zero (Q : TrioSeq) (e : ℕ) : shTower Q e 0 = [] := rfl

@[simp] theorem shTower_one (Q : TrioSeq) (e : ℕ) : shTower Q e 1 = Q := by
  unfold shTower
  simp

open Classical in
theorem gcopy_shift0 (M : TrioSeq) (L d0 k : ℕ) :
    gcopy M 0 L d0 0 k = shiftr01 (k * d0) 0 (seg M 0 L) := by
  unfold gcopy seg shiftr01
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro j _
  simp

/-- **★ Each guarded copy is a row-0 shift of a row-1 lift of the window.**
This is the form `(SUBST)` consumes: copy `k` is rooted at the diagonal column
`(k*d0, v + k*d1, z)` and, by `(WL)`, sits in `W` of exactly that column's
level (GRAFTALL-PLAN 4.15). -/
theorem gcopy_eq_shift_lift {M : TrioSeq} (L d0 d1 k : ℕ) (hL : L ≤ M.length) :
    gcopy M 0 L d0 d1 k = shiftr01 (k * d0) 0 (Lift1 (M.take L) (k * d1)) := by
  classical
  have hlen : (M.take L).length = L := by rw [List.length_take]; omega
  unfold gcopy shiftr01 Lift1
  rw [hlen, List.map_map, ← List.range_eq_range']
  refine List.map_congr_left ?_
  intro j hj
  have hjl : j < L := List.mem_range.mp hj
  simp only [Function.comp_apply, entry_take hjl, le1_take hL hjl, Nat.add_zero]

/-- The whole copy block, as the tower of shifted lifts of the window. -/
theorem gcopies_eq_tower {M : TrioSeq} (L d0 d1 n : ℕ) (hL : L ≤ M.length) :
    gcopies M 0 L d0 d1 n
      = (List.range n).flatMap
          fun k => shiftr01 (k * d0) 0 (Lift1 (M.take L) (k * d1)) := by
  unfold gcopies
  refine List.flatMap_congr ?_
  intro k _
  exact gcopy_eq_shift_lift L d0 d1 k hL

open Classical in
/-- **The row-1 collapse at the root expands to a shifted copy tower.** -/
theorem oper_of_srow1_par0 {X : TrioSeq} (h2 : 2 ≤ X.length)
    (hp : hasParent X (srow X (X.length - 1)) (X.length - 1))
    (hbp : parent X (srow X (X.length - 1)) (X.length - 1) = 0)
    (hsr : srow X (X.length - 1) = 1) (n : ℕ) :
    X⟦n⟧ = shTower X.dropLast (entry X 0 (X.length - 1) - entry X 0 0) n := by
  have hnr := parent_nextR hp
  rw [hbp, hsr] at hnr
  have hn1 : nextrel1 X 0 (X.length - 1) := by
    unfold nextR at hnr
    rw [if_neg (by omega), if_pos rfl] at hnr
    exact hnr
  have hpos : 0 < entry X 1 (X.length - 1) := by
    have := hn1.2.2.2.1; omega
  have hz : ¬ (entry X 0 (X.length - 1) = 0 ∧ entry X 1 (X.length - 1) = 0 ∧
      entry X 2 (X.length - 1) = 0) := by
    rintro ⟨-, h1, -⟩; omega
  have hseg : seg X 0 (X.length - 1) = X.dropLast := by
    rw [seg_zero_eq_take X (show X.length - 1 ≤ X.length by omega),
      ← List.dropLast_eq_take]
  rw [oper_gcopies n (by omega) hz hp, hbp, hsr,
    if_pos (by omega : (0 : ℕ) < 1), if_neg (by omega : ¬ (1 : ℕ) < 1),
    List.take_zero, Nat.sub_zero, List.nil_append]
  unfold gcopies shTower
  refine List.flatMap_congr ?_
  intro k _
  rw [gcopy_shift0, hseg]

/-- **(TOW)**: a row-0-shifted copy tower over a `W`-member whose root is its
shallowest column stays in the same stage.  Probe `tools/probe_core1.py` (C):
6244 instances, 0 violations, and `minstage` is *equal*, not just bounded. -/
def ShiftTowerClosed : Prop :=
  ∀ (u e n : ℕ) (Q : TrioSeq), Q ∈ W u → (∀ p ∈ Q, entry Q 0 0 ≤ p.1) →
    shTower Q e n ∈ W u

/-- **(TOW) with the root STRICTLY shallowest.**  Every consumer of `(TOW)`
supplies this stronger form (`argOK` for the peel of a planted root, the row-0
window `window_of_rtg0` for the lifted peel), and it is what `(SUBST)` can
discharge: a block hung under a host column must be strictly deeper than it. -/
def ShiftTowerClosedS : Prop :=
  ∀ (u e n : ℕ) (Q : TrioSeq), Q ∈ W u →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
    shTower Q e n ∈ W u

theorem shiftTowerClosedS_of_closed (h : ShiftTowerClosed) : ShiftTowerClosedS := by
  intro u e n Q hQ hs
  refine h u e n Q hQ (fun p hpm => ?_)
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hpm
  have hval : entry Q 0 j = Q[j].1 := by
    unfold entry
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp
  rcases Nat.eq_zero_or_pos j with rfl | hjp
  · exact le_of_eq (by rw [← hval])
  · exact le_of_lt (by rw [← hval]; exact hs j hjp hj)

open Classical in
/-- **The last `(WL)` branch reduces to `(TOW)`** — a statement with no lift in
it at all.  The clause-2 hypothesis is consumed only at `n = 1`. -/
theorem lspOn_srow1_of_tower (htow : ShiftTowerClosedS) :
    LSPOn (fun X => badPar X = 0 ∧ srow X (X.length - 1) = 1) := by
  classical
  rintro m d X h2 hp ⟨hbp, hsr⟩ hop n hn
  unfold badPar at hbp
  have hnr := parent_nextR hp
  rw [hbp, hsr] at hnr
  have hj1pos : 0 < X.length - 1 := nextR_index_lt hnr
  have hj1ne : X.length - 1 ≠ 0 := by omega
  have hn1 : nextrel1 X 0 (X.length - 1) := by
    unfold nextR at hnr
    rw [if_neg (by omega), if_pos rfl] at hnr
    exact hnr
  have hwin : ∀ l, 0 < l → l ≤ X.length - 1 → entry X 0 0 < entry X 0 l :=
    window_of_rtg0 hn1.2.2.2.2.1.2.2 (by omega)
  -- the peel is a `W`-member, straight from the hypothesis at `n = 1`
  have hQ : Lift1 X.dropLast d ∈ W (m + 2 * d) := by
    have h1 := hop 1 le_rfl
    rwa [oper_of_srow1_par0 h2 hp hbp hsr 1, shTower_one] at h1
  -- and its root is its shallowest column
  have hhead : entry (Lift1 X.dropLast d) 0 0 = entry X 0 0 := by
    rw [entry0_Lift1, List.dropLast_eq_take,
      Wset.entry_take (show (0 : ℕ) < X.length - 1 by omega)]
  have hQr : ∀ j, 1 ≤ j → j < (Lift1 X.dropLast d).length →
      entry (Lift1 X.dropLast d) 0 0 < entry (Lift1 X.dropLast d) 0 j := by
    intro j hj1 hjl
    rw [Lift1_length, List.length_dropLast] at hjl
    rw [hhead, entry0_Lift1, List.dropLast_eq_take,
      Wset.entry_take (show j < X.length - 1 by omega)]
    exact hwin j (by omega) (by omega)
  -- the lifted expansion is the same tower, over the lifted peel
  have hsrL : srow (Lift1 X d) ((Lift1 X d).length - 1) = 1 := by
    rw [Lift1_length, srow_Lift1 hj1ne]; exact hsr
  have hpL : hasParent (Lift1 X d) (srow (Lift1 X d) ((Lift1 X d).length - 1))
      ((Lift1 X d).length - 1) := by
    rw [Lift1_length, srow_Lift1 hj1ne, hasParent_Lift1]; exact hp
  have hbpL : parent (Lift1 X d) (srow (Lift1 X d) ((Lift1 X d).length - 1))
      ((Lift1 X d).length - 1) = 0 := by
    rw [Lift1_length, srow_Lift1 hj1ne, parent_Lift1]; exact hbp
  rw [oper_of_srow1_par0 (by rw [Lift1_length]; omega) hpL hbpL hsrL n,
    Lift1_dropLast]
  exact htow _ _ _ _ hQ hQr

/-- **(WL) rests on `(TOW)` alone.** -/
theorem liftStageParented_of_tower (htow : ShiftTowerClosedS) :
    LiftStageParented :=
  liftStageParented_of_srow1 (lspOn_srow1_of_tower htow)

/-! ### `TowerExp` の行 1 部分も同じ `(TOW)` に落ちる

`TowerExp` は「節 2 経由で来た死んだ孤児が根 `(0,v,z)` の下で復活する」塔である。
`domT R m` から `R` の末尾列は自分の行の孤児なので `R⟦n⟧ = Pred R = R.dropLast`
（長さ 1 なら `R⟦n⟧ = R`）。したがって節 2 のデータは `n = 1` だけで
`M.dropLast ∈ W a`（`M = (0,v,z) :: R`）を与える。崩壊行が 1 なら
`oper_of_srow1_par0` により `M⟦n⟧` は `M.dropLast` の行 0 ずらしコピー塔なので、
`(TOW)` がそのまま効く。根は `(0,v,z)` で深さ 0 なので「根が最浅」は自明。

行 2 の部分（`d1 > 0`、コピーごとに行 1 が上がる保護付き塔）は `(TOW)` の形では
ないので、別核として残る。 -/

/-- `TowerExp` restricted to a row-1 collapse. -/
def TowerExp1 : Prop :=
  ∀ (v z m a : ℕ) (R : TrioSeq), argOK R → R ≠ [] → z ≤ 1 → 2 * v + z ≤ a →
    domT R m → (∀ n, 1 ≤ n → R⟦n⟧ ∈ Wstar) → srow R (R.length - 1) = 1 →
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length →
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a

/-- `TowerExp` restricted to a row-2 collapse. -/
def TowerExp2 : Prop :=
  ∀ (v z m a : ℕ) (R : TrioSeq), argOK R → R ≠ [] → z ≤ 1 → 2 * v + z ≤ a →
    domT R m → (∀ n, 1 ≤ n → R⟦n⟧ ∈ Wstar) → srow R (R.length - 1) = 2 →
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length →
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a

theorem towerExp_of_rows (h1 : TowerExp1) (h2 : TowerExp2) : Wset.TowerExp := by
  intro v z m a R hR hRne hz1 hva hd hop hpM n hn
  have hlevpos : 0 < lev R (R.length - 1) := by rw [hd.1]; omega
  unfold lev at hlevpos
  rcases srow_cases R (R.length - 1) with hsr | hsr | hsr
  · exfalso
    unfold srow at hsr
    split at hsr
    · omega
    · split at hsr
      · omega
      · omega
  · exact h1 v z m a R hR hRne hz1 hva hd hop hsr hpM n hn
  · exact h2 v z m a R hR hRne hz1 hva hd hop hsr hpM n hn

open Classical in
/-- **The row-1 half of `TowerExp` reduces to `(TOW)` as well.** -/
theorem towerExp1_of_tower (htow : ShiftTowerClosedS) : TowerExp1 := by
  classical
  intro v z m a R hR hRne hz1 hva hd hop hsr hpM n hn
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hMlen : (((0, v, z) : ℕ × ℕ × ℕ) :: R).length - 1 = R.length := by simp
  have hM2 : 2 ≤ (((0, v, z) : ℕ × ℕ × ℕ) :: R).length := by simp; omega
  have hsrM : srow (((0, v, z) : ℕ × ℕ × ℕ) :: R)
      ((((0, v, z) : ℕ × ℕ × ℕ) :: R).length - 1) = 1 := by
    rw [hMlen, srow_cons_last hRne]; exact hsr
  have hpM' : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R)
      (srow (((0, v, z) : ℕ × ℕ × ℕ) :: R)
        ((((0, v, z) : ℕ × ℕ × ℕ) :: R).length - 1))
      ((((0, v, z) : ℕ × ℕ × ℕ) :: R).length - 1) := by
    rw [hsrM, hMlen, ← hsr]; exact hpM
  have hpar0 : parent (((0, v, z) : ℕ × ℕ × ℕ) :: R)
      (srow (((0, v, z) : ℕ × ℕ × ℕ) :: R)
        ((((0, v, z) : ℕ × ℕ × ℕ) :: R).length - 1))
      ((((0, v, z) : ℕ × ℕ × ℕ) :: R).length - 1) = 0 := by
    rw [hsrM, hMlen, ← hsr]
    exact parent_cons_eq_zero hRne hd hpM
  have hdrop : (((0, v, z) : ℕ × ℕ × ℕ) :: R).dropLast
      = ((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast :=
    List.dropLast_cons_of_ne_nil hRne
  -- the peel of `M` is a `W`-member: the clause-2 data at `n = 1` suffices
  have hMd : (((0, v, z) : ℕ × ℕ × ℕ) :: R).dropLast ∈ W a := by
    rw [hdrop]
    rcases Nat.lt_or_ge R.length 2 with hshort | hbig
    · have h1 : R.length = 1 := by omega
      have : R.dropLast = [] := by
        rw [List.dropLast_eq_take, h1]; simp
      rw [this]
      exact W_mono hva (Om_mem_W v z)
    · have hzR : ¬ (entry R 0 (R.length - 1) = 0 ∧ entry R 1 (R.length - 1) = 0 ∧
          entry R 2 (R.length - 1) = 0) := by
        rintro ⟨-, ha, hb⟩
        have hlv := hd.1
        unfold lev at hlv
        omega
      have hRop : R⟦1⟧ = R.dropLast := by
        rw [oper_eq_pred_of_noParent 1 (by omega) hzR hd.2]
        unfold Pred
        rw [if_neg (by omega)]
      have hst := hop 1 le_rfl
      rw [hRop] at hst
      refine hst ?_ v z a hz1 hva
      rw [List.dropLast_eq_take]
      exact argOK_take' hR _
  have hQr : ∀ j, 1 ≤ j → j < (((0, v, z) : ℕ × ℕ × ℕ) :: R).dropLast.length →
      entry (((0, v, z) : ℕ × ℕ × ℕ) :: R).dropLast 0 0
        < entry (((0, v, z) : ℕ × ℕ × ℕ) :: R).dropLast 0 j := by
    intro j hj1 hjl
    rw [hdrop] at hjl ⊢
    have hroot : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 0 0 = 0 := by
      simp [entry]
    have hjR : j - 1 < R.dropLast.length := by
      rw [List.length_cons] at hjl; omega
    have hshift : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 0 j
        = entry R.dropLast 0 (j - 1) := by
      conv_lhs => rw [show j = (j - 1) + 1 by omega]
      rw [entry_cons]
    rw [hroot, hshift]
    exact argOK_dropLast hR _ (entry_pair_mem hjR)
  rw [oper_of_srow1_par0 hM2 hpM' hpar0 hsrM n]
  exact htow _ _ _ _ hMd hQr

/-- **The whole residue is `(TOW)` plus the row-2 half of `TowerExp`.** -/
theorem towerExp_of_tower (htow : ShiftTowerClosedS) (h2 : TowerExp2) :
    Wset.TowerExp :=
  towerExp_of_rows (towerExp1_of_tower htow) h2

/-! ### `(TOW)` の候補上位: `W u` は連結で閉じているか

`Wset.W_add` は `rsum A B`（「`B` の根が `A ++ B` の最浅列」）を要求する。これは
`XA_closed` の**証明**が必要とする条件である: `B` が最浅なら `A ++ B` のバッド
ルートは `B` から出られず、展開は `A ++ B⟦n⟧` に留まる（`oper_append_gen`）。
塔ではこれがちょうど逆で、
`shTower Q e (n+1) = shTower Q e n ++ shiftr01 (n*e) 0 Q` の後半は**最深**である。

計測 `tools/probe_cat.py`: 仮定を一切置かない

```
(CAT)   A ∈ W u → B ∈ W u → A ++ B ∈ W u
```

は 372290 例（短列全数 + 長列ランダム + ST_TS 由来）で違反 0。判定を
`n ∈ {1,2,3}` に上げた再計測でも 28065 例で違反 0。`W_shift` と合わせると
`(TOW)` は 2 行で出る（根の最浅条件すら要らなくなる）。
⚠ `minstage` の判定は有限個の `n` の展開しか見ない近似なので、これは**候補**で
あって証明ではない。 -/

/-- **(CAT)**: `W u` is closed under plain concatenation, with no side
condition — the hypothesis-free strengthening of `Wset.W_add`. -/
def WCat : Prop := ∀ (u : ℕ) (A B : TrioSeq), A ∈ W u → B ∈ W u → A ++ B ∈ W u

theorem shTower_succ (Q : TrioSeq) (e n : ℕ) :
    shTower Q e (n + 1) = shTower Q e n ++ shiftr01 (n * e) 0 Q := by
  unfold shTower
  rw [List.range_succ, List.flatMap_append]
  simp

/-- **`(CAT)` gives `(TOW)`** — and drops the shallowest-root hypothesis. -/
theorem shiftTowerClosed_of_cat (hcat : WCat) : ShiftTowerClosed := by
  intro u e n Q hQ _
  induction n with
  | zero => simpa [shTower] using W_nil u
  | succ n ih =>
      rw [shTower_succ]
      exact hcat u _ _ ih (W_shift hQ _)

/-! ### `(CAT)` を「1 列の追加」に落とす

`Xbar.oper_append_inner`（`rsum` も根条件も無し）が

```
(AP)  T ≠ [] → |T|-1 ≠ 0 → hasParent T (srow T (|T|-1)) (|T|-1)
      → (A ++ T)⟦n⟧ = A ++ T⟦n⟧
```

を既に与えている。これを使って `XA A (W u) = {B | A ++ B ∈ W u}` の上で A2' を
回すと、`Aop` の各節が**1 列追加**に落ちる:

| 節 | 処理 |
|---|---|
| 節 2・`B` に親あり | `(AP)` + `mem_of_oper_mem` |
| 節 2・`B` の末尾が孤児 | `B⟦n⟧ = Pred B = B.dropLast` ⟹ `A ++ B.dropLast ∈ W u`、`A ++ B = (A ++ B.dropLast) ++ [末尾]` |
| 節 3 | `graft B [] = B.dropLast` で同上 |
| 節 1 | `B = []` は自明、`B = [p]` は 1 列追加 |

追加した列が `C ++ [p]` でも孤児なら展開は `Pred` なので**ただ**である。残るのは

```
(SNOC)  C ∈ W u → C ≠ [] → hasParent (C ++ [p]) (srow (C++[p]) |C|) |C|
        → C ++ [p] ∈ W u
```

＝「**親を見つける 1 列を足しても段は上がらない**」。計測
`tools/probe_snoc.py`: 14455 例違反 0（孤児側の対照は 34507 例違反 0）。
`p` のレベル上限では言い換えられない: `C = [(0,0,0)]`, `p = (1,5,0)` は
`lev p = 10` だが `C ++ [p] ∈ W 0`（親が付くと `C` の窓の塔になるため）。 -/

/-- **(SNOC)**: appending one column that finds a parent costs no stage. -/
def WSnoc : Prop :=
  ∀ (u : ℕ) (C : TrioSeq) (p : ℕ × ℕ × ℕ), C ∈ W u → C ≠ [] →
    hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length → C ++ [p] ∈ W u

open Classical in
/-- The snoc step, with the orphan half discharged: only the parented case is
open. -/
theorem snoc_step (hsn : WSnoc) {u : ℕ} {C : TrioSeq} (p : ℕ × ℕ × ℕ)
    (hC : C ∈ W u) (hCne : C ≠ []) : C ++ [p] ∈ W u := by
  classical
  have hClen : 0 < C.length := List.length_pos_iff.mpr hCne
  have hlen : (C ++ [p]).length - 1 = C.length := by simp
  by_cases hpar : hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length
  · exact hsn u C p hC hCne hpar
  · refine mem_of_oper_mem (fun n hn => ?_)
    have hL : (C ++ [p]).length - 1 ≠ 0 := by rw [hlen]; omega
    have hpr : (C ++ [p])⟦n⟧ = Pred (C ++ [p]) := by
      by_cases hz : entry (C ++ [p]) 0 ((C ++ [p]).length - 1) = 0 ∧
          entry (C ++ [p]) 1 ((C ++ [p]).length - 1) = 0 ∧
          entry (C ++ [p]) 2 ((C ++ [p]).length - 1) = 0
      · exact oper_eq_pred_of_zero n hL hz
      · exact oper_eq_pred_of_noParent n hL hz (by rw [hlen]; exact hpar)
    rw [hpr]
    unfold Pred
    rw [if_neg (by simp; omega), List.dropLast_concat]
    exact hC

open Classical in
/-- **`(SNOC)` gives `(CAT)`** — every `Aop` clause reduces to one snoc. -/
theorem wcat_of_snoc (hsn : WSnoc) : WCat := by
  classical
  intro u A B hA hB
  have hsub : W u ⊆ {B : TrioSeq | A ++ B ∈ W u} := by
    refine A2' ?_
    rintro B (⟨hl, hlev⟩ | hop | ⟨m, hm, hd, hgr⟩)
    · -- clause 1: `B` is empty or a single level-`0` column
      rcases Nat.eq_zero_or_pos B.length with h0 | hpos
      · have hnil : B = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        simpa using hA
      · obtain ⟨q, rfl⟩ : ∃ q, B = [q] :=
          List.length_eq_one_iff.mp (by omega)
        show A ++ [q] ∈ W u
        rcases List.eq_nil_or_concat A with rfl | ⟨A', a, rfl⟩
        · rw [List.nil_append]
          have : q = (q.1, q.2.1, q.2.2) := rfl
          rw [this]
          refine singleton_mem_W ?_
          unfold lev entry at hlev
          simp at hlev
          omega
        · exact snoc_step hsn q hA (by simp)
    · -- clause 2
      rcases Nat.lt_or_ge B.length 2 with hsm | hbig
      · have h1 := hop 1 le_rfl
        rwa [oper_eq_self_of_short 1 (by omega)] at h1
      · have hBne : B ≠ [] := by
          intro hc; rw [hc] at hbig; simp at hbig
        by_cases hpar : hasParent B (srow B (B.length - 1)) (B.length - 1)
        · show A ++ B ∈ W u
          refine mem_of_oper_mem (fun n hn => ?_)
          rw [oper_append_inner n hBne (by omega) hpar]
          exact hop n hn
        · have hdrop : B⟦1⟧ = B.dropLast := by
            by_cases hz : entry B 0 (B.length - 1) = 0 ∧
                entry B 1 (B.length - 1) = 0 ∧ entry B 2 (B.length - 1) = 0
            · rw [oper_eq_pred_of_zero 1 (by omega) hz]
              unfold Pred; rw [if_neg (by omega)]
            · rw [oper_eq_pred_of_noParent 1 (by omega) hz hpar]
              unfold Pred; rw [if_neg (by omega)]
          have hC : A ++ B.dropLast ∈ W u := by
            have h1 := hop 1 le_rfl
            rwa [hdrop] at h1
          have hCne : A ++ B.dropLast ≠ [] := by
            intro hc
            have := congrArg List.length hc
            rw [List.length_append, List.length_dropLast] at this
            simp at this
            omega
          have hsplit : A ++ B = (A ++ B.dropLast) ++ [B.getLast hBne] := by
            rw [List.append_assoc, List.dropLast_append_getLast hBne]
          show A ++ B ∈ W u
          rw [hsplit]
          exact snoc_step hsn _ hC hCne
    · -- clause 3: the trailing orphan, grafted with the empty forest
      have hBne : B ≠ [] := by
        intro hc; rw [hc] at hd; exact not_domT_nil m hd
      have hC : A ++ B.dropLast ∈ W u := by
        have h := hgr [] (W_nil m) based_nil
        rwa [graft_nil] at h
      rcases Nat.lt_or_ge B.length 2 with hsm | hbig
      · obtain ⟨q, rfl⟩ : ∃ q, B = [q] :=
          List.length_eq_one_iff.mp (by
            have := List.length_pos_iff.mpr hBne; omega)
        show A ++ [q] ∈ W u
        rcases List.eq_nil_or_concat A with rfl | ⟨A', a, rfl⟩
        · rw [List.nil_append]
          have hq : q = (q.1, q.2.1, q.2.2) := rfl
          rw [hq]
          refine singleton_mem_W ?_
          have hlv := hd.1
          unfold lev entry at hlv
          simp at hlv
          omega
        · exact snoc_step hsn q hA (by simp)
      · have hCne : A ++ B.dropLast ≠ [] := by
          intro hc
          have := congrArg List.length hc
          rw [List.length_append, List.length_dropLast] at this
          simp at this
          omega
        have hsplit : A ++ B = (A ++ B.dropLast) ++ [B.getLast hBne] := by
          rw [List.append_assoc, List.dropLast_append_getLast hBne]
        show A ++ B ∈ W u
        rw [hsplit]
        exact snoc_step hsn _ hC hCne
  exact hsub hB

/-! ### `(SNOC)` の自由な断片

`M = C ++ [p]`、`j0 = parent M i1 |C| < |C|` とすると、窓 `[j0, |C|)` は**すべて
`C` の中**にあり

```
M⟦1⟧ = C,      M⟦n⟧ = C.take j0 ++ (C.drop j0 のガード付きコピー塔)
```

なので `(SNOC)` は「`C ∈ W u` から `C` の任意の**切り口**でのコピー塔が `W u` に
入る」と読める（`C` 自身の展開はその中の 1 つ、`C` の正準な切り口の場合）。

`i1 = 0`（`d0 = d1 = 0`）かつ `j0 = 0` のときだけコピーが `C` そのものになり、
`W_flatMap_copies` で**無条件に**閉じる。他の枝（`j0 ≥ 1`、または `i1 ≥ 1`）は
コピーが持ち上がる／接頭辞が残るので核のまま。 -/

open Classical in
/-- With a row-0 collapse whose parent is the root, the expansion is `n` literal
copies of `C`. -/
theorem oper_snoc_flat_root {C : TrioSeq} {p : ℕ × ℕ × ℕ} (hCne : C ≠ [])
    (hsr : srow (C ++ [p]) C.length = 0)
    (hbp : parent (C ++ [p]) (srow (C ++ [p]) C.length) C.length = 0)
    (hpar : hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length) (n : ℕ) :
    (C ++ [p])⟦n⟧ = (List.range n).flatMap fun _ => C := by
  have hClen : 0 < C.length := List.length_pos_iff.mpr hCne
  have hlen : (C ++ [p]).length - 1 = C.length := by simp
  have hp' : hasParent (C ++ [p])
      (srow (C ++ [p]) ((C ++ [p]).length - 1)) ((C ++ [p]).length - 1) := by
    rw [hlen]; exact hpar
  have hbp' : parent (C ++ [p])
      (srow (C ++ [p]) ((C ++ [p]).length - 1)) ((C ++ [p]).length - 1) = 0 := by
    rw [hlen]; exact hbp
  have hsr' : srow (C ++ [p]) ((C ++ [p]).length - 1) = 0 := by
    rw [hlen]; exact hsr
  have h := oper_of_srow0_par0 (by simp; omega) hp' hbp' hsr' n
  rwa [List.dropLast_concat] at h

open Classical in
/-- **The free fragment of `(SNOC)`**: a row-0 collapse whose parent is the
root.  Then the copies are `C` verbatim, so `W_flatMap_copies` closes it with no
core at all. -/
theorem snoc_flat_root {u : ℕ} {C : TrioSeq} {p : ℕ × ℕ × ℕ} (hC : C ∈ W u)
    (hCne : C ≠ [])
    (hsr : srow (C ++ [p]) C.length = 0)
    (hbp : parent (C ++ [p]) (srow (C ++ [p]) C.length) C.length = 0)
    (hpar : hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length) :
    C ++ [p] ∈ W u := by
  classical
  have hClen : 0 < C.length := List.length_pos_iff.mpr hCne
  -- the root of `C` is strictly its shallowest column: it is `p`'s row-0 parent
  have hnr := parent_nextR hpar
  rw [hbp, hsr] at hnr
  have hn0 : nextrel0 (C ++ [p]) 0 C.length := by
    unfold nextR at hnr
    rw [if_pos rfl] at hnr
    exact hnr
  have hCr : ∀ q ∈ C, entry C 0 0 ≤ q.1 := by
    intro q hq
    obtain ⟨j, hj, hje⟩ : ∃ j, j < C.length ∧ C.getD j (0, 0, 0) = q := by
      obtain ⟨j, hj⟩ := List.mem_iff_getElem.mp hq
      exact ⟨j, hj.1, by rw [← hj.2, getElem_eq_getD' hj.1]⟩
    have hEC : ∀ i, entry (C ++ [p]) i j = entry C i j := by
      intro i; unfold entry; rw [getD_append_left hj]
    have hE0 : entry (C ++ [p]) 0 0 = entry C 0 0 := by
      unfold entry; rw [getD_append_left (by omega)]
    rw [← hje]
    show entry C 0 0 ≤ entry C 0 j
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact le_rfl
    · have hdip := hn0.2.2.2.2 j ⟨hjpos, hj⟩
      have hlt := hn0.2.2.2.1
      rw [hEC 0] at hdip
      rw [hE0] at hlt
      omega
  refine mem_of_oper_mem (fun n hn => ?_)
  rw [oper_snoc_flat_root hCne hsr hbp hpar n]
  exact W_flatMap_copies hC hCr n

/-- `TowerExp` restricted to a row-2 collapse whose orphan sits at or above the
target stage.  The complementary half (`m < a`) is `(CAT)`-strength. -/
def TowerExp2Low : Prop :=
  ∀ (v z m a : ℕ) (R : TrioSeq), argOK R → R ≠ [] → z ≤ 1 → 2 * v + z ≤ a →
    a ≤ m → domT R m → (∀ n, 1 ≤ n → R⟦n⟧ ∈ Wstar) → srow R (R.length - 1) = 2 →
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length →
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a

/-- **The row-2 tower AT THE ROOT'S OWN STAGE.**  The `a` quantifier of
`TowerExp2` is spurious: `W_mono` lifts `W (2v+z)` to every `a ≥ 2v+z`, and
`tower1_le` already forces `2v+z ≤ m`, so the whole row-2 residue is the single
stage `2v+z`. -/
def TowerExp2Root : Prop :=
  ∀ (v z m : ℕ) (R : TrioSeq), argOK R → R ≠ [] → z ≤ 1 → domT R m →
    (∀ n, 1 ≤ n → R⟦n⟧ ∈ Wstar) → srow R (R.length - 1) = 2 →
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length →
    v < entry R 1 (R.length - 1) → z < entry R 2 (R.length - 1) →
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W (2 * v + z)

theorem towerExp2_of_root (h : TowerExp2Root) : TowerExp2 := by
  intro v z m a R hR hRne hz1 hva hd hop hsr hpM n hn
  obtain ⟨h1, h2⟩ := row2_revival_gap hRne hd hsr hpM
  exact W_mono hva (h v z m R hR hRne hz1 hd hop hsr hpM h1 h2 n hn)

theorem towerExp2Low_of_root (h : TowerExp2Root) : TowerExp2Low := by
  intro v z m a R hR hRne hz1 hva _ hd hop hsr hpM n hn
  obtain ⟨h1, h2⟩ := row2_revival_gap hRne hd hsr hpM
  exact W_mono hva (h v z m R hR hRne hz1 hd hop hsr hpM h1 h2 n hn)

open Classical in
/-- **★ The `m < a` half of `TowerExp` is `(CAT)`-strength.**  When the trailing
orphan's own level fits under the target stage, the single column is already a
`W a` member on its own, so `(CAT)` glues it onto `p_{v,z}(R.dropLast)`.  This
is what isolates the genuinely hard half: `a ≤ m`, where the appended column
is only harmless because it finds a parent. -/
theorem towerExp_of_cat (hcat : WCat) (h2 : TowerExp2Low) : Wset.TowerExp := by
  classical
  intro v z m a R hR hRne hz1 hva hd hop hpM n hn
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  rcases Nat.lt_or_ge m a with hma | hma
  · -- `m < a`: the appended column is itself in `W a`, so `(CAT)` suffices.
    have hCne : (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) ≠ [] := by simp
    have hCA : (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) ∈ W a := by
      rcases Nat.lt_or_ge R.length 2 with hsm | hbig
      · have hdl : R.dropLast = [] :=
          List.eq_nil_of_length_eq_zero (by simp; omega)
        rw [hdl]
        exact W_mono hva (Om_mem_W v z)
      · have h1 := hop 1 le_rfl
        rw [oper_eq_graft_nil_of_domT (n := 1) (by omega) hd, graft_nil] at h1
        exact h1 (argOK_dropLast hR) v z a hz1 hva
    have hqd : R.getLast hRne = R.getD (R.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
      rw [List.getLast_eq_getElem, getElem_eq_getD' (by omega)]
    have hlv : 2 * (R.getLast hRne).2.1 + (R.getLast hRne).2.2 = m + 1 := by
      have hl := hd.1
      unfold lev entry at hl
      rw [hqd]
      simpa using hl
    have hpW : [R.getLast hRne] ∈ W a := by
      have hq : R.getLast hRne
          = ((R.getLast hRne).1, (R.getLast hRne).2.1, (R.getLast hRne).2.2) := rfl
      rw [hq]
      exact singleton_mem_W (by omega)
    have hM : (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W a := by
      have hglue := hcat a _ _ hCA hpW
      rwa [List.cons_append, List.dropLast_append_getLast hRne] at hglue
    exact oper_closed hM hn
  · -- `a ≤ m`: row 1 still reduces to `(TOW)`, row 2 is the open half.
    have hlevpos : 0 < lev R (R.length - 1) := by rw [hd.1]; omega
    unfold lev at hlevpos
    rcases srow_cases R (R.length - 1) with hsr | hsr | hsr
    · exfalso
      unfold srow at hsr
      split at hsr
      · omega
      · split at hsr
        · omega
        · omega
    · exact towerExp1_of_tower (shiftTowerClosedS_of_closed (shiftTowerClosed_of_cat hcat))
        v z m a R hR hRne hz1 hva hd hop hsr hpM n hn
    · exact h2 v z m a R hR hRne hz1 hva hma hd hop hsr hpM n hn

open Classical in
/-- **★ `(SNOC)` gives `TowerExp` outright.**  The successor-clause tower *is* a
snoc: `domT R m` makes `R⟦1⟧ = R.dropLast`, so the clause-2 datum puts
`p_{v,z}(R.dropLast)` in `W a`, and `R`'s trailing orphan — the very column the
root revives — is the single column being appended.  `snoc_step` covers the
orphan case too, so `hpM` is not even needed.

This is what `(CAT)` could NOT do: `(CAT)` needs both sides in `W a`, whereas
here the appended column carries an arbitrarily high level and only becomes
harmless because it finds a parent in the context. -/
theorem towerExp_of_snoc (hsn : WSnoc) : Wset.TowerExp := by
  classical
  intro v z m a R hR hRne hz1 hva hd hop _hpM n hn
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hCne : (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) ≠ [] := by simp
  have hCA : (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) ∈ W a := by
    rcases Nat.lt_or_ge R.length 2 with hsm | hbig
    · have hdl : R.dropLast = [] :=
        List.eq_nil_of_length_eq_zero (by simp; omega)
      rw [hdl]
      exact W_mono hva (Om_mem_W v z)
    · have h1 := hop 1 le_rfl
      rw [oper_eq_graft_nil_of_domT (n := 1) (by omega) hd, graft_nil] at h1
      exact h1 (argOK_dropLast hR) v z a hz1 hva
  have hM : (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W a := by
    have hstep := snoc_step hsn (R.getLast hRne) hCA hCne
    rwa [List.cons_append, List.dropLast_append_getLast hRne] at hstep
  exact oper_closed hM hn

/-- **★ The `z = 1` diagonal is trivial.**  Every column carries row 2 = `1`, so
no column has a row-1 ancestor with a smaller row 2, i.e. no row-2 parent at
all; `oper` is therefore just `Pred` and the block shrinks to `[(0,v,1)]`, whose
level `2v+1` is exactly the target stage.  Together with
`PairBridge.diag_mem_W` (the `z = 0` case) this closes the `|R| = 1` base of
`TowerExp2Root` (GRAFTALL-PLAN 4.2). -/
theorem diag1_mem_W (v e f : ℕ) : ∀ n : ℕ,
    ((List.range n).map (fun k => ((k * e, v + k * f, 1) : ℕ × ℕ × ℕ)))
      ∈ W (2 * v + 1) := by
  classical
  intro n
  induction n with
  | zero => simpa using W_nil (2 * v + 1)
  | succ n ih =>
      set D : TrioSeq :=
        (List.range (n + 1)).map (fun k => ((k * e, v + k * f, 1) : ℕ × ℕ × ℕ))
        with hD
      have hlen : D.length = n + 1 := by rw [hD]; simp
      have hget : ∀ j, j < n + 1 →
          D.getD j ((0, 0, 0) : ℕ × ℕ × ℕ) = ((j * e, v + j * f, 1) : ℕ × ℕ × ℕ) := by
        intro j hj
        rw [hD, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem (by simpa using hj)]
        simp
      have hent2 : ∀ j, j < n + 1 → entry D 2 j = 1 := by
        intro j hj
        unfold entry
        rw [hget j hj]
        simp
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have hD1 : D = [((0 * e, v + 0 * f, 1) : ℕ × ℕ × ℕ)] := by rw [hD]; simp
        rw [hD1]
        exact singleton_mem_W (by omega)
      · refine mem_of_oper_mem (fun p hp => ?_)
        have hL : D.length - 1 ≠ 0 := by omega
        have hj1 : D.length - 1 < n + 1 := by omega
        have hsr : srow D (D.length - 1) = 2 := by
          unfold srow
          rw [if_pos (by rw [hent2 _ hj1]; omega)]
        have hnp : ¬ hasParent D 2 (D.length - 1) := by
          rintro ⟨j0, hj0, -⟩
          have hn2 : nextrel2 D j0 (D.length - 1) := by
            unfold nextR at hj0
            rw [if_neg (by omega), if_neg (by omega)] at hj0
            exact hj0
          have hj0l : j0 < n + 1 := by rw [← hlen]; exact hn2.1
          have := hn2.2.2.2.1
          rw [hent2 _ hj0l, hent2 _ hj1] at this
          omega
        have hzz : ¬ (entry D 0 (D.length - 1) = 0 ∧ entry D 1 (D.length - 1) = 0 ∧
            entry D 2 (D.length - 1) = 0) := by
          rintro ⟨-, -, h2⟩
          rw [hent2 _ hj1] at h2
          omega
        rw [oper_eq_pred_of_noParent p hL hzz (by rw [hsr]; exact hnp)]
        unfold Pred
        rw [if_neg (by omega)]
        have hdl : D.dropLast
            = (List.range n).map (fun k => ((k * e, v + k * f, 1) : ℕ × ℕ × ℕ)) := by
          rw [hD, List.range_succ, List.map_append]
          simp
        rw [hdl]
        exact ih

/-- **★ The diagonal at the root's own stage, for both `z ≤ 1`.**  `z = 0` is
the pair theorem (`PairBridge.diag_mem_W`, transported from lean-yapss); `z = 1`
is the `Pred` chain (`diag1_mem_W`).  This is the host `Q` that `(SUBST)`
substitutes into. -/
theorem diagz_mem_W {z : ℕ} (hz : z ≤ 1) (v e f : ℕ) (he : 0 < e) (n : ℕ) :
    ((List.range n).map (fun k => ((k * e, v + k * f, z) : ℕ × ℕ × ℕ)))
      ∈ W (2 * v + z) := by
  rcases Nat.lt_or_ge z 1 with h | h
  · have hz0 : z = 0 := by omega
    subst hz0
    simpa using PairBridge.diag_mem_W v e f n he
  · have hz1 : z = 1 := by omega
    subst hz1
    exact diag1_mem_W v e f n

section ShiftLift

variable {X : TrioSeq} {a d j : ℕ}

theorem entry0_shiftLift (hj : j < X.length) :
    entry (shiftr01 a 0 (Lift1 X d)) 0 j = entry X 0 j + a := by
  unfold entry
  rw [shiftr01_getD (by rw [Lift1_length]; exact hj)]
  show ((Lift1 X d).getD j (0, 0, 0)).1 + a = _
  rw [Lift1_getD hj]
  simp [entry, List.getD_eq_getElem?_getD]

open Classical in
theorem entry1_shiftLift (hj : j < X.length) :
    entry (shiftr01 a 0 (Lift1 X d)) 1 j
      = entry X 1 j + (if le1 X 0 j then d else 0) := by
  unfold entry
  rw [shiftr01_getD (by rw [Lift1_length]; exact hj)]
  show ((Lift1 X d).getD j (0, 0, 0)).2.1 + 0 = _
  rw [Lift1_getD hj]
  simp [entry, List.getD_eq_getElem?_getD]

theorem entry2_shiftLift (hj : j < X.length) :
    entry (shiftr01 a 0 (Lift1 X d)) 2 j = entry X 2 j := by
  unfold entry
  rw [shiftr01_getD (by rw [Lift1_length]; exact hj)]
  show ((Lift1 X d).getD j (0, 0, 0)).2.2 = _
  rw [Lift1_getD hj]
  simp [entry, List.getD_eq_getElem?_getD]

theorem entry_ge_two {Y : TrioSeq} {i j : ℕ} (hi : 2 ≤ i) :
    entry Y i j = entry Y 2 j := by
  unfold entry
  rw [if_neg (by omega), if_neg (by omega)]
  simp

@[simp] theorem shiftLift_length (X : TrioSeq) (a d : ℕ) :
    (shiftr01 a 0 (Lift1 X d)).length = X.length := by
  rw [shiftr01_length, Lift1_length]

end ShiftLift

/-! ## 二列の定理 — 高いレベルの列は根の段に吸収される -/

/-- **Repeated copies of one column.**  Every column sits at depth `0`, so none
has a row-0 predecessor and hence none has a parent at any row
(`no_hasParent_of_row0_zero`): `oper` is `Pred` throughout and the block shrinks
to `[(0,b,c)]`, whose level is exactly the stage.  This is the degenerate
diagonal, the one `diagz_mem_W` cannot reach (it needs `0 < e`). -/
theorem constcol_mem_W (b c : ℕ) : ∀ n : ℕ,
    ((List.range n).map (fun _ => ((0, b, c) : ℕ × ℕ × ℕ))) ∈ W (2 * b + c) := by
  intro n
  induction n with
  | zero => simpa using W_nil (2 * b + c)
  | succ n ih =>
      set D : TrioSeq := (List.range (n + 1)).map (fun _ => ((0, b, c) : ℕ × ℕ × ℕ))
        with hD
      have hlen : D.length = n + 1 := by rw [hD]; simp
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have hD1 : D = [((0, b, c) : ℕ × ℕ × ℕ)] := by rw [hD]; simp
        rw [hD1]
        exact singleton_mem_W le_rfl
      · refine mem_of_oper_mem (fun p hp => ?_)
        have hL : D.length - 1 ≠ 0 := by omega
        have hent0 : ∀ j, entry D 0 j = 0 := by
          intro j
          unfold entry
          rw [hD, List.getD_eq_getElem?_getD]
          rcases Nat.lt_or_ge j (n + 1) with hj | hj
          · rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using hj)]
            simp
          · rw [List.getElem?_map, List.getElem?_eq_none_iff.mpr (by simpa using hj)]
            simp
        have hpred : D⟦p⟧ = Pred D := by
          by_cases hzz : entry D 0 (D.length - 1) = 0 ∧ entry D 1 (D.length - 1) = 0 ∧
              entry D 2 (D.length - 1) = 0
          · exact oper_eq_pred_of_zero p hL hzz
          · exact oper_eq_pred_of_noParent p hL hzz
              (fun hh => no_hasParent_of_row0_zero (hent0 _) hh)
        rw [hpred]
        unfold Pred
        rw [if_neg (by omega)]
        have hdl : D.dropLast
            = (List.range n).map (fun _ => ((0, b, c) : ℕ × ℕ × ℕ)) := by
          rw [hD, List.range_succ, List.map_append]
          simp
        rw [hdl]
        exact ih

open Classical in
/-- **★★ Two columns live at the root's own stage** — for an ARBITRARY second
column, however deep and however high.

Either the second column is an orphan, and `oper` is `Pred`; or its parent is
the root, and the expansion is exactly the diagonal
`[(k*D0, v + k*D1, z)]_{k<n}` (`gcopies_eq_tower` with `M.take 1 = [(0,v,z)]`),
which `diagz_mem_W` — the pair theorem for `z = 0` — puts in `W (2v+z)`.  When
the second column has level `0` the diagonal degenerates to repeated copies of
the root (`constcol_mem_W`).

So `[(0,0,0), (1,100,1)] ∈ W 0`: a level-`201` column is harmless under a
level-`0` root.  This is the two-column host that `(SUBST1g)` grafts into. -/
theorem two_col_mem_W {v z a : ℕ} (hz : z ≤ 1) (ha : 2 * v + z ≤ a)
    (t : ℕ × ℕ × ℕ) : [((0, v, z) : ℕ × ℕ × ℕ), t] ∈ W a := by
  classical
  set M : TrioSeq := [((0, v, z) : ℕ × ℕ × ℕ), t] with hM
  have hlen : M.length = 2 := by rw [hM]; simp
  have hL : M.length - 1 ≠ 0 := by omega
  have hdl : M.dropLast = [((0, v, z) : ℕ × ℕ × ℕ)] := by rw [hM]; simp
  have hr0 : entry M 0 0 = 0 := by rw [hM]; simp [entry]
  have hr1 : entry M 1 0 = v := by rw [hM]; simp [entry]
  have hr2 : entry M 2 0 = z := by rw [hM]; simp [entry]
  refine mem_of_oper_mem (fun n hn => ?_)
  by_cases hpar : hasParent M (srow M (M.length - 1)) (M.length - 1)
  · have hne0 : entry M 0 (M.length - 1) ≠ 0 := fun h0 =>
      no_hasParent_of_row0_zero h0 hpar
    have hzz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
        entry M 2 (M.length - 1) = 0) := by
      rintro ⟨h0, -, -⟩; exact hne0 h0
    have hpar0 : parent M (srow M (M.length - 1)) (M.length - 1) = 0 := by
      have hlt := nextR_index_lt (parent_nextR hpar)
      omega
    set D0 : ℕ := (if 0 < srow M (M.length - 1)
      then entry M 0 (M.length - 1) - entry M 0 0 else 0) with hD0
    set D1 : ℕ := (if 1 < srow M (M.length - 1)
      then entry M 1 (M.length - 1) - entry M 1 0 else 0) with hD1
    have hgexp : M⟦n⟧ = gexp M 0 (M.length - 1) D0 D1 n :=
      oper_eq_gexp n hL hzz hpar hpar0
    have hone : ∀ k, shiftr01 (k * D0) 0 (Lift1 (M.take 1) (k * D1))
        = [((k * D0, v + k * D1, z) : ℕ × ℕ × ℕ)] := by
      intro k
      have htk : M.take 1 = [((0, v, z) : ℕ × ℕ × ℕ)] := by rw [hM]; simp
      rw [htk, Lift1_of_length_one (by simp) (k * D1)]
      unfold shiftr01
      simp [entry]
    have hdiag : M⟦n⟧
        = (List.range n).map (fun k => ((k * D0, v + k * D1, z) : ℕ × ℕ × ℕ)) := by
      rw [hgexp]
      unfold gexp
      rw [show M.length - 1 = 1 by omega, gcopies_eq_tower 1 D0 D1 n (by omega),
        List.flatMap_congr (fun k (_ : k ∈ List.range n) => hone k)]
      have hfm : ∀ l : List ℕ,
          List.flatMap (fun k => [((k * D0, v + k * D1, z) : ℕ × ℕ × ℕ)]) l
            = l.map (fun k => ((k * D0, v + k * D1, z) : ℕ × ℕ × ℕ)) := by
        intro l
        induction l with
        | nil => rfl
        | cons c l ih => simp [ih]
      exact hfm _
    rw [hdiag]
    rcases Nat.eq_zero_or_pos D0 with hD0z | hD0p
    · -- level-0 second column: the diagonal degenerates to repeated roots
      have hsr0 : srow M (M.length - 1) = 0 := by
        by_contra hsr
        rw [hD0, if_pos (by omega), hr0] at hD0z
        omega
      have hD1z : D1 = 0 := by rw [hD1, hsr0]; simp
      rw [hD0z, hD1z]
      have : ∀ k : ℕ, ((k * 0, v + k * 0, z) : ℕ × ℕ × ℕ) = ((0, v, z) : ℕ × ℕ × ℕ) := by
        intro k; simp
      rw [List.map_congr_left (fun k _ => this k)]
      exact W_mono ha (constcol_mem_W v z n)
    · exact W_mono ha (diagz_mem_W hz v D0 D1 hD0p n)
  · have hpred : M⟦n⟧ = Pred M := by
      by_cases hzz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
          entry M 2 (M.length - 1) = 0
      · exact oper_eq_pred_of_zero n hL hzz
      · exact oper_eq_pred_of_noParent n hL hzz hpar
    rw [hpred]
    unfold Pred
    rw [if_neg (by omega), hdl]
    exact W_mono ha (Om_mem_W v z)

/-- **(SUBST)** — the substitution closure, the shape `TowerExp2Root` needs for
`|R| ≥ 2` (GRAFTALL-PLAN 4.15).  Replacing every column of a `W u` member by a
block rooted at that column, whose other columns are strictly deeper and which
itself lies in `W` of that column's own level, keeps the stage.

The host `Q` may be assumed to be a *chain* (strictly increasing in row 0),
which is all the tower ever supplies.

The tower instance: `Q` is the diagonal `[(k*d0, v + k*d1, z)]_{k<n}` — proved
to be in `W (2v+z)` by `PairBridge.diag_mem_W` (`z = 0`) and `diag1_mem_W`
(`z = 1`) — and `B k = shiftr01 (k*d0) 0 (Lift1 M.dropLast (k*d1))`
(`gcopy_eq_shift_lift`), which `(WL)` places in `W (2*(v + k*d1) + z)`, exactly
`lev Q k`.

Probe `tools/probe_subst.py`: 38403 decided instances, 0 violations. -/
def SubstClosed : Prop :=
  ∀ (u : ℕ) (Q : TrioSeq) (B : ℕ → TrioSeq), Q ∈ W u →
    (∀ k, k + 1 < Q.length → entry Q 0 k < entry Q 0 (k + 1)) →
    (∀ k, k < Q.length → 0 < (B k).length) →
    (∀ k, k < Q.length → ∀ i, entry (B k) i 0 = entry Q i k) →
    (∀ k, k < Q.length → ∀ j, 1 ≤ j → j < (B k).length →
      entry Q 0 k < entry (B k) 0 j) →
    (∀ k, k < Q.length → B k ∈ W (lev Q k)) →
    ((List.range Q.length).flatMap B) ∈ W u

theorem entry_drop_head (Q : TrioSeq) (i k : ℕ) :
    entry (Q.drop k) i 0 = entry Q i k := by
  unfold entry
  rw [getD_drop, Nat.add_zero]

/-- **(SUBST1)** — the single-block form of `(SUBST)`.

`(SUBST)` hangs a block under *every* column of the host at once, but the
substitutions are independent and can be done ONE AT A TIME, left to right:
replacing the column at position `p` never touches positions `< p`.  So the
whole of `(SUBST)` follows from the single-block statement

    S ∈ W u,  p < |S|,  C ∈ W (lev S p),  head C = S p,  rest of C deeper
    ⟹ S.take p ++ C ++ S.drop (p+1) ∈ W u

which is a far better induction target: one block, no `flatMap`, and — as the
probe shows — no chain condition on the host.

Probe `tools/probe_subst1.py`: 62151 instances, 0 violations (58799 decided,
3352 undecided).  The stronger *graft-at-a-position* form, which only asks
`entry C 0 0 = entry S 0 p` and lets the head's level drop below `lev S p`, is
also clean: `tools/probe_subst1g.py`, 210201 instances, 0 violations, of which
148050 have a head different from `S p`. -/
def Subst1 : Prop :=
  ∀ (u p : ℕ) (S C : TrioSeq), S ∈ W u → p < S.length → C ≠ [] →
    C ∈ W (lev S p) →
    (∀ i, entry C i 0 = entry S i p) →
    (∀ j, 1 ≤ j → j < C.length → entry S 0 p < entry C 0 j) →
    (S.take p ++ C ++ S.drop (p + 1)) ∈ W u

/-- **`(SUBST1)` gives `(SUBST)`.**  Substitute the blocks left to right: after
`k` steps the object is `⧺_{j<k} B j ++ Q.drop k`, whose column at index
`|⧺_{j<k} B j|` is still `Q k`, with the same entries and the same level.  One
`(SUBST1)` step turns it into stage `k+1`, and `k = |Q|` is the goal.  The chain
hypothesis of `(SUBST)` is not used. -/
theorem substClosed_of_subst1 (hs : Subst1) : SubstClosed := by
  intro u Q B hQ _hchain hBne hBhead hBdeep hBW
  have key : ∀ k, k ≤ Q.length → ((List.range k).flatMap B ++ Q.drop k) ∈ W u := by
    intro k
    induction k with
    | zero => intro _; simpa using hQ
    | succ k ih =>
        intro hk
        have hk' : k < Q.length := by omega
        have hIH := ih (by omega)
        set P : TrioSeq := (List.range k).flatMap B with hPdef
        set T : TrioSeq := Q.drop k with hTdef
        have hTlen : T.length = Q.length - k := by rw [hTdef]; simp
        have hE : ∀ i, entry (P ++ T) i P.length = entry Q i k := by
          intro i
          have h1 := entry_append_right P T i 0
          rw [Nat.add_zero] at h1
          rw [h1, hTdef, entry_drop_head Q i k]
        have hlv : lev (P ++ T) P.length = lev Q k := by
          unfold lev; rw [hE 1, hE 2]
        have hplt : P.length < (P ++ T).length := by
          rw [List.length_append]; omega
        have htake : (P ++ T).take P.length = P := List.take_left
        have hdrop : (P ++ T).drop (P.length + 1) = Q.drop (k + 1) := by
          have h1 : (P ++ T).drop (P.length + 1) = ((P ++ T).drop P.length).drop 1 := by
            rw [List.drop_drop]
          rw [h1, List.drop_left, hTdef, List.drop_drop]
        have hstep := hs u P.length (P ++ T) (B k) hIH hplt
          (by intro h; have hb := hBne k hk'; rw [h] at hb; simp at hb)
          (by rw [hlv]; exact hBW k hk')
          (by intro i; rw [hE i]; exact hBhead k hk' i)
          (by intro j hj1 hj2; rw [hE 0]; exact hBdeep k hk' j hj1 hj2)
        rw [htake, hdrop] at hstep
        have hrange : (List.range (k + 1)).flatMap B = P ++ B k := by
          rw [List.range_succ, List.flatMap_append, hPdef]
          simp
        rw [hrange]
        exact hstep
  have h := key Q.length le_rfl
  simpa using h

/-- **(SUBST1g)** — the *graft-at-a-position* form of `(SUBST1)`: the block's
head need only sit at the same DEPTH as the column it replaces, its level may be
anything at or below `lev S p` (`C ∈ W (lev S p)` already forces
`lev (C 0) ≤ lev S p` by `lev_root_le_of_mem_W`).

This is exactly `Aop`'s clause 3 with two liberalisations — any position instead
of the last, and the block's stage raised from `lev - 1` to `lev` — which is why
it is the natural single core.

Probe `tools/probe_subst1g.py`: 210201 instances, 0 violations, of which 148050
have a head different from `S p`. -/
def Subst1g : Prop :=
  ∀ (u p : ℕ) (S C : TrioSeq), S ∈ W u → p < S.length → C ≠ [] →
    C ∈ W (lev S p) →
    entry C 0 0 = entry S 0 p →
    (∀ j, 1 ≤ j → j < C.length → entry S 0 p < entry C 0 j) →
    (S.take p ++ C ++ S.drop (p + 1)) ∈ W u

theorem subst1_of_subst1g (hg : Subst1g) : Subst1 :=
  fun u p S C hS hp hCne hCW hhead hdeep =>
    hg u p S C hS hp hCne hCW (hhead 0) hdeep

/-- The multi-block form of `(SUBST1g)`: `(SUBST)` with the head condition cut
down to the depth and the chain hypothesis dropped. -/
def SubstClosedG : Prop :=
  ∀ (u : ℕ) (Q : TrioSeq) (B : ℕ → TrioSeq), Q ∈ W u →
    (∀ k, k < Q.length → 0 < (B k).length) →
    (∀ k, k < Q.length → entry (B k) 0 0 = entry Q 0 k) →
    (∀ k, k < Q.length → ∀ j, 1 ≤ j → j < (B k).length →
      entry Q 0 k < entry (B k) 0 j) →
    (∀ k, k < Q.length → B k ∈ W (lev Q k)) →
    ((List.range Q.length).flatMap B) ∈ W u

theorem substClosed_of_substClosedG (hg : SubstClosedG) : SubstClosed :=
  fun u Q B hQ _hchain hBne hBhead hBdeep hBW =>
    hg u Q B hQ hBne (fun k hk => hBhead k hk 0) hBdeep hBW

/-- `(SUBST1g)` gives its own multi-block form, by the same left-to-right
substitution as `substClosed_of_subst1`. -/
theorem substClosedG_of_subst1g (hs : Subst1g) : SubstClosedG := by
  intro u Q B hQ hBne hBhead hBdeep hBW
  have key : ∀ k, k ≤ Q.length → ((List.range k).flatMap B ++ Q.drop k) ∈ W u := by
    intro k
    induction k with
    | zero => intro _; simpa using hQ
    | succ k ih =>
        intro hk
        have hk' : k < Q.length := by omega
        have hIH := ih (by omega)
        set P : TrioSeq := (List.range k).flatMap B with hPdef
        set T : TrioSeq := Q.drop k with hTdef
        have hTlen : T.length = Q.length - k := by rw [hTdef]; simp
        have hE : ∀ i, entry (P ++ T) i P.length = entry Q i k := by
          intro i
          have h1 := entry_append_right P T i 0
          rw [Nat.add_zero] at h1
          rw [h1, hTdef, entry_drop_head Q i k]
        have hlv : lev (P ++ T) P.length = lev Q k := by
          unfold lev; rw [hE 1, hE 2]
        have hplt : P.length < (P ++ T).length := by
          rw [List.length_append]; omega
        have htake : (P ++ T).take P.length = P := List.take_left
        have hdrop : (P ++ T).drop (P.length + 1) = Q.drop (k + 1) := by
          have h1 : (P ++ T).drop (P.length + 1) = ((P ++ T).drop P.length).drop 1 := by
            rw [List.drop_drop]
          rw [h1, List.drop_left, hTdef, List.drop_drop]
        have hstep := hs u P.length (P ++ T) (B k) hIH hplt
          (by intro h; have hb := hBne k hk'; rw [h] at hb; simp at hb)
          (by rw [hlv]; exact hBW k hk')
          (by rw [hE 0]; exact hBhead k hk')
          (by intro j hj1 hj2; rw [hE 0]; exact hBdeep k hk' j hj1 hj2)
        rw [htake, hdrop] at hstep
        have hrange : (List.range (k + 1)).flatMap B = P ++ B k := by
          rw [List.range_succ, List.flatMap_append, hPdef]
          simp
        rw [hrange]
        exact hstep
  have h := key Q.length le_rfl
  simpa using h

/-- The substitution property of a single sequence, at stage `u`. -/
def SubstProp (u : ℕ) (N : TrioSeq) : Prop :=
  ∀ p C, p < N.length → C ≠ [] → C ∈ W (lev N p) →
    entry C 0 0 = entry N 0 p →
    (∀ q ∈ C, entry N 0 p ≤ q.1) →
    (N.take p ++ C ++ N.drop (p + 1)) ∈ W u

theorem entry_getElem {M : TrioSeq} {j : ℕ} (hj : j < M.length) :
    entry M 0 j = M[j].1 := by
  unfold entry
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  simp

/-- The strict "every other column is deeper" condition implies the NON-STRICT
membership form, which is the one `oper` preserves (`oper_mem_ge`). -/
theorem mem_ge_of_deep {C : TrioSeq} {x : ℕ} (hhead : entry C 0 0 = x)
    (hdeep : ∀ j, 1 ≤ j → j < C.length → x < entry C 0 j) :
    ∀ q ∈ C, x ≤ q.1 := by
  intro q hq
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
  rw [← entry_getElem hj]
  rcases Nat.eq_zero_or_pos j with rfl | hjp
  · exact le_of_eq hhead.symm
  · exact le_of_lt (hdeep j hjp hj)

theorem substProp_nil (u : ℕ) : SubstProp u [] := by
  intro p C hp; simp at hp

open Classical in
/-- **★★★ Every SUFFIX of a `W`-member is a `W`-member at its own root's level.**

The old note "suffix closure of `W` is false" used a FIXED stage
(`[(0,0,0),(1,1,0)] ∈ W 0` but `[(1,1,0)]` needs `W 2`); with `W_root_stage` the
right stage is the suffix's own root level, and then it holds.

Induct on the datum.  With `T = N.drop j` and `2 ≤ |T|`: if `T`'s trailing column
has a parent inside `T`, `Xbar`-free `oper_append_inner` gives
`N⟦n⟧ = N.take j ++ T⟦n⟧`, so `T⟦n⟧` is a suffix of `N⟦n⟧` and the datum applies;
otherwise `oper` peels `T` and `T⟦n⟧` is a suffix of `N.dropLast = N⟦1⟧`.  The
short cases are `singleton_mem_self` and `W_nil`.

Probe: 237099 `drop` instances and 470712 segment instances, 0 failures. -/
theorem W_drop {u : ℕ} {M : TrioSeq} (h : M ∈ W u) (j : ℕ) :
    M.drop j ∈ W (lev M j) := by
  classical
  have hsub : W u ⊆ {N : TrioSeq | N ∈ W u ∧ ∀ j, N.drop j ∈ W (lev N j)} := by
    refine A2' ?_
    intro N hA
    have hmem : N ∈ W u := by
      refine A1_intro ?_
      rcases hA with h' | h' | ⟨m, hm, hd, hgr⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl fun n hn => (h' n hn).1)
      · exact Or.inr (Or.inr ⟨m, hm, hd, fun z hz hb => (hgr z hz hb).1⟩)
    refine ⟨hmem, fun j => ?_⟩
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rw [List.drop_zero]
      by_cases hne : N = []
      · subst hne; exact W_nil _
      · exact W_root_stage hmem hne
    · by_cases hjlen : N.length ≤ j
      · rw [List.drop_eq_nil_of_le hjlen]; exact W_nil _
      · have hlv0 : lev (N.drop j) 0 = lev N j := lev_drop_head N j
        have hTlen : (N.drop j).length = N.length - j := by simp
        rcases Nat.lt_or_ge ((N.drop j).length) 2 with hshort | hbig
        · obtain ⟨c, hc⟩ : ∃ c, N.drop j = [c] := by
            have h1 : (N.drop j).length = 1 := by omega
            cases hD : N.drop j with
            | nil => rw [hD] at h1; simp at h1
            | cons a t =>
                refine ⟨a, ?_⟩
                rw [hD] at h1
                simp only [List.length_cons] at h1
                rw [List.eq_nil_of_length_eq_zero (show t.length = 0 by omega)]
          rw [hc]
          rw [hc] at hlv0
          rw [← hlv0]
          exact singleton_mem_self c
        · -- `|T| ≥ 2`
          have hNlen : 1 < N.length := by omega
          have hjlt : j + 1 ≤ N.length - 1 := by omega
          have htkj : (N.take j).length = j := by
            have h2 : (N.take j).length = min j N.length := List.length_take
            omega
          have hsplit : N.take j ++ N.drop j = N := List.take_append_drop _ _
          have hdatum : ∀ n, 1 ≤ n →
              (N⟦n⟧ ∈ W u ∧ ∀ i, (N⟦n⟧).drop i ∈ W (lev (N⟦n⟧) i)) := by
            rcases hA with h' | h' | ⟨m, hm, hd, hgr⟩
            · exact absurd h'.1 (by omega)
            · exact h'
            · intro n hn
              rw [oper_eq_graft_nil_of_domT (by omega) hd]
              exact hgr [] (W_nil m) based_nil
          have hlevop : ∀ n, 1 ≤ n → lev (N⟦n⟧) j = lev N j := by
            intro n hn
            have htk := oper_take_prefix hNlen hn hjlt
            have e : ∀ i, entry (N⟦n⟧) i j = entry N i j := by
              intro i
              rw [← Wset.entry_take (X := N⟦n⟧) (l := j + 1) (i := i) (by omega),
                ← Wset.entry_take (X := N) (l := j + 1) (i := i) (by omega), htk]
            unfold lev
            rw [e 1, e 2]
          have hNdl : N.dropLast ∈ W u ∧
              ∀ i, (N.dropLast).drop i ∈ W (lev (N.dropLast) i) := by
            have := hdatum 1 le_rfl
            rwa [oper_one_eq_dropLast hNlen] at this
          rw [← hlv0]
          refine A1_intro (Or.inr (Or.inl (fun n hn => ?_)))
          rw [hlv0]
          by_cases hTp : hasParent (N.drop j)
              (srow (N.drop j) ((N.drop j).length - 1)) ((N.drop j).length - 1)
          · have hTne : N.drop j ≠ [] := by
              intro hc; rw [hc] at hbig; simp at hbig
            have hop : N⟦n⟧ = N.take j ++ (N.drop j)⟦n⟧ := by
              conv_lhs => rw [← hsplit]
              exact oper_append_inner n hTne (by omega) hTp
            have hdr : (N⟦n⟧).drop j = (N.drop j)⟦n⟧ := by
              have hdl : (N.take j ++ (N.drop j)⟦n⟧).drop (N.take j).length
                  = (N.drop j)⟦n⟧ := List.drop_left
              rw [htkj] at hdl
              rw [hop, hdl]
            rw [← hdr, ← hlevop n hn]
            exact (hdatum n hn).2 j
          · have hzz : ¬ (entry (N.drop j) 0 ((N.drop j).length - 1) = 0 ∧
                entry (N.drop j) 1 ((N.drop j).length - 1) = 0 ∧
                entry (N.drop j) 2 ((N.drop j).length - 1) = 0) ∨
                (entry (N.drop j) 0 ((N.drop j).length - 1) = 0 ∧
                entry (N.drop j) 1 ((N.drop j).length - 1) = 0 ∧
                entry (N.drop j) 2 ((N.drop j).length - 1) = 0) := by
              tauto
            have hpred : (N.drop j)⟦n⟧ = (N.drop j).dropLast := by
              rcases hzz with hz | hz
              · rw [oper_eq_pred_of_noParent n (by omega) hz hTp]
                unfold Pred; rw [if_neg (by omega)]
              · rw [oper_eq_pred_of_zero n (by omega) hz]
                unfold Pred; rw [if_neg (by omega)]
            rw [hpred]
            have heq : (N.drop j).dropLast = (N.dropLast).drop j := by
              rw [List.dropLast_eq_take, List.dropLast_eq_take, List.drop_take]
              congr 1
              simp
              omega
            have hlevdl : lev (N.dropLast) j = lev N j := by
              unfold lev
              rw [List.dropLast_eq_take,
                Wset.entry_take (X := N) (l := N.length - 1) (i := 1) (by omega),
                Wset.entry_take (X := N) (l := N.length - 1) (i := 2) (by omega)]
            rw [heq, ← hlevdl]
            exact hNdl.2 j
  exact (hsub h).2 j

/-- **Segments too**: `Wself` is closed under taking any contiguous block, at
that block's own root level. -/
theorem W_segment {u : ℕ} {M : TrioSeq} (h : M ∈ W u) (j k : ℕ) :
    (M.drop j).take k ∈ W (lev M j) :=
  W_take (W_drop h j) k

/-- **The stage-free form of `W`.**  `W_root_stage` and `lev_root_le_of_mem_W`
together give `M ∈ W u ↔ M ∈ Wself ∧ lev M 0 ≤ u`: the whole indexed family
collapses to ONE set plus a root-level side condition. -/
def Wself : Set TrioSeq := {M : TrioSeq | M ∈ W (lev M 0)}

theorem mem_Wself_iff (u : ℕ) (M : TrioSeq) :
    M ∈ W u ↔ (M ∈ Wself ∧ lev M 0 ≤ u) := by
  constructor
  · intro h
    by_cases hne : M = []
    · subst hne
      exact ⟨show ([] : TrioSeq) ∈ W (lev ([] : TrioSeq) 0) from W_nil _,
        by simp [lev, entry]⟩
    · exact ⟨W_root_stage h hne, lev_root_le_of_mem_W h hne⟩
  · rintro ⟨h1, h2⟩
    exact W_mono h2 h1

/-- **★★ The `z = 0` fragment of trio is already done.**

A trio sequence whose row 2 is identically zero IS a pair sequence, and
`YAPSS.Wset.mem_W_of_bound` puts every pair sequence in `W u` as soon as `u`
bounds its row-1 values — unconditionally, since lean-yapss's `mem_Wstar` is
unconditional.  The bridge carries that to trio, and `W_root_stage` then sharpens
the stage down to the root's own level.

So all of trio's difficulty sits in the row-2 columns. -/
theorem zeroRow2_mem_Wself {M : TrioSeq} (hz : ∀ p ∈ M, p.2.2 = 0) : M ∈ Wself := by
  classical
  by_cases hne : M = []
  · subst hne
    exact show ([] : TrioSeq) ∈ W (lev ([] : TrioSeq) 0) from W_nil _
  · set S : YAPSS.PairSeq := M.map (fun p => (p.1, p.2.1)) with hS
    have hemb : PairBridge.emb S = M := by
      rw [hS]
      unfold PairBridge.emb
      rw [List.map_map,
        List.map_congr_left (g := fun p : ℕ × ℕ × ℕ => p)
          (fun p hp => by
            show ((p.1, p.2.1, 0) : ℕ × ℕ × ℕ) = p
            rw [← hz p hp])]
      simp
    have h1 : S ∈ YAPSS.Wset.W (YAPSS.maxr1 S) := YAPSS.Wset.mem_W_maxr1 S
    have h2 : M ∈ W (2 * YAPSS.maxr1 S) := by
      rw [← hemb]; exact PairBridge.emb_mem_W h1
    exact W_root_stage h2 hne

theorem gcopy_row2 {M : TrioSeq} {r L d0 d1 k : ℕ} {q : ℕ × ℕ × ℕ}
    (hq : q ∈ gcopy M r L d0 d1 k) : ∃ j, r ≤ j ∧ j < r + L ∧ q.2.2 = entry M 2 j := by
  unfold gcopy at hq
  rw [List.mem_map] at hq
  obtain ⟨j, hj, rfl⟩ := hq
  rw [List.mem_range'] at hj
  obtain ⟨i, hi, rfl⟩ := hj
  exact ⟨r + 1 * i, by omega, by omega, rfl⟩

theorem gcopies_row2 {M : TrioSeq} {r L d0 d1 n : ℕ} {q : ℕ × ℕ × ℕ}
    (hq : q ∈ gcopies M r L d0 d1 n) :
    ∃ j, r ≤ j ∧ j < r + L ∧ q.2.2 = entry M 2 j := by
  unfold gcopies at hq
  rw [List.mem_flatMap] at hq
  obtain ⟨k, -, hk⟩ := hq
  exact gcopy_row2 hk

open Classical in
/-- **Appending a column that stays an ORPHAN is free.**  `oper` peels it back
off, so the whole expansion is the block itself, and the root is untouched.
This is what makes the orphan half of `(LOW)` (lowering a trailing column) free:
only the case where the new column FINDS a parent is open. -/
theorem snoc_orphan {A : TrioSeq} (hA : A ∈ Wself) (hAne : A ≠ [])
    (t : ℕ × ℕ × ℕ)
    (hnp : ¬ hasParent (A ++ [t]) (srow (A ++ [t]) ((A ++ [t]).length - 1))
      ((A ++ [t]).length - 1)) :
    (A ++ [t]) ∈ Wself := by
  classical
  have hAlen : 0 < A.length := List.length_pos_iff.mpr hAne
  have hlen : (A ++ [t]).length = A.length + 1 := by rw [List.length_append]; simp
  have hdl : (A ++ [t]).dropLast = A := by simp
  have hroot : ∀ i, entry (A ++ [t]) i 0 = entry A i 0 :=
    fun i => entry_append_left _ _ (by omega)
  have hlv : lev (A ++ [t]) 0 = lev A 0 := by unfold lev; rw [hroot 1, hroot 2]
  refine A1_intro (Or.inr (Or.inl (fun n hn => ?_)))
  have hpred : (A ++ [t])⟦n⟧ = Pred (A ++ [t]) := by
    by_cases hz : entry (A ++ [t]) 0 ((A ++ [t]).length - 1) = 0 ∧
        entry (A ++ [t]) 1 ((A ++ [t]).length - 1) = 0 ∧
        entry (A ++ [t]) 2 ((A ++ [t]).length - 1) = 0
    · exact oper_eq_pred_of_zero n (by omega) hz
    · exact oper_eq_pred_of_noParent n (by omega) hz hnp
  rw [hpred]
  unfold Pred
  rw [if_neg (by omega), hdl, hlv]
  exact hA

theorem dropLast_mem_Wself {M : TrioSeq} (h : M ∈ Wself) (hne : M.dropLast ≠ []) :
    M.dropLast ∈ Wself := by
  have hlen : 0 < M.dropLast.length := List.length_pos_iff.mpr hne
  have hdl : M.dropLast.length = M.length - 1 := List.length_dropLast
  have hlv : lev M.dropLast 0 = lev M 0 := by
    unfold lev
    rw [List.dropLast_eq_take,
      Wset.entry_take (X := M) (l := M.length - 1) (i := 1) (by omega),
      Wset.entry_take (X := M) (l := M.length - 1) (i := 2) (by omega)]
  show M.dropLast ∈ W (lev M.dropLast 0)
  rw [hlv]
  exact W_dropLast h

/-- **(LOW)** — lowering the trailing column of a `Wself` member. -/
def LowerLast : Prop :=
  ∀ (A : TrioSeq) (c t : ℕ × ℕ × ℕ), (A ++ [c]) ∈ Wself → A ≠ [] →
    t.1 = c.1 → 2 * t.2.1 + t.2.2 ≤ 2 * c.2.1 + c.2.2 →
    (A ++ [t]) ∈ Wself

/-- `(LOW)` restricted to the case where the lowered column FINDS a parent. -/
def LowerLastParented : Prop :=
  ∀ (A : TrioSeq) (c t : ℕ × ℕ × ℕ), (A ++ [c]) ∈ Wself → A ≠ [] →
    t.1 = c.1 → 2 * t.2.1 + t.2.2 ≤ 2 * c.2.1 + c.2.2 →
    hasParent (A ++ [t]) (srow (A ++ [t]) ((A ++ [t]).length - 1))
      ((A ++ [t]).length - 1) →
    (A ++ [t]) ∈ Wself

/-- **The orphan half of `(LOW)` is free** (`snoc_orphan`). -/
theorem lowerLast_of_parented (h : LowerLastParented) : LowerLast := by
  classical
  intro A c t hAc hAne ht hlev
  by_cases hp : hasParent (A ++ [t]) (srow (A ++ [t]) ((A ++ [t]).length - 1))
      ((A ++ [t]).length - 1)
  · exact h A c t hAc hAne ht hlev hp
  · refine snoc_orphan ?_ hAne t hp
    have hdl : (A ++ [c]).dropLast = A := by simp
    have := dropLast_mem_Wself hAc (by rw [hdl]; exact hAne)
    rwa [hdl] at this

open Classical in
/-- **★★ A row-2-free block carries ANY trailing column.**

If every column of `M'` has row 2 = 0 then `M' ++ [t] ∈ Wself` for an arbitrary
`t` — arbitrary depth, arbitrary level.  The reason is that `oper` never copies
the trailing column: either it is an orphan and `oper` peels back to `M'`, or the
copies are taken from `M[j0 .. |M|-2] ⊆ M'`, so the whole expansion is again
row-2-free and `zeroRow2_mem_Wself` applies.  Row 2 is never incremented by an
expansion, so the copies stay row-2-free.

This strictly generalises `two_col_mem_W` (the case `|M'| = 1`). -/
theorem snoc_zeroRow2 {M' : TrioSeq} (hz : ∀ p ∈ M', p.2.2 = 0) (t : ℕ × ℕ × ℕ) :
    (M' ++ [t]) ∈ Wself := by
  classical
  by_cases hnil : M' = []
  · subst hnil
    simpa using singleton_mem_self t
  · have hM'len : 0 < M'.length := List.length_pos_iff.mpr hnil
    set M : TrioSeq := M' ++ [t] with hM
    have hlen : M.length = M'.length + 1 := by rw [hM, List.length_append]; simp
    have hdl : M.dropLast = M' := by rw [hM]; simp
    have hroot : ∀ i, entry M i 0 = entry M' i 0 :=
      fun i => entry_append_left _ _ (by omega)
    have hlv : lev M 0 = lev M' 0 := by unfold lev; rw [hroot 1, hroot 2]
    have hM'z : ∀ j, j < M'.length → entry M' 2 j = 0 :=
      fun j hj => hz _ (entry_pair_mem hj)
    refine A1_intro (Or.inr (Or.inl (fun n hn => ?_)))
    have hlevop : lev (M⟦n⟧) 0 = lev M 0 := by
      have htk := oper_take_prefix (M := M) (by omega) hn (i := 1) (by omega)
      have e : ∀ i, entry (M⟦n⟧) i 0 = entry M i 0 := by
        intro i
        rw [← Wset.entry_take (X := M⟦n⟧) (l := 1) (i := i) (by omega),
          ← Wset.entry_take (X := M) (l := 1) (i := i) (by omega), htk]
      unfold lev
      rw [e 1, e 2]
    have hgoal : ∀ q ∈ M⟦n⟧, q.2.2 = 0 := by
      by_cases hp : hasParent M (srow M (M.length - 1)) (M.length - 1)
      · have hzz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
            entry M 2 (M.length - 1) = 0) := by
          rintro ⟨h0, -, -⟩
          exact no_hasParent_of_row0_zero h0 hp
        rw [oper_gcopies n (by omega) hzz hp]
        intro q hq
        have hj0 : parent M (srow M (M.length - 1)) (M.length - 1) < M.length - 1 :=
          nextR_index_lt (parent_nextR hp)
        rcases List.mem_append.mp hq with hq | hq
        · rw [List.take_append_of_le_length (by omega)] at hq
          exact hz q (List.mem_of_mem_take hq)
        · obtain ⟨j, -, hjlt, hqj⟩ := gcopies_row2 hq
          rw [hqj, entry_append_left _ _ (by omega), hM'z j (by omega)]
      · have hpred : M⟦n⟧ = Pred M := by
          by_cases hzz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
              entry M 2 (M.length - 1) = 0
          · exact oper_eq_pred_of_zero n (by omega) hzz
          · exact oper_eq_pred_of_noParent n (by omega) hzz hp
        rw [hpred]
        unfold Pred
        rw [if_neg (by omega), hdl]
        exact hz
    rw [← hlevop]
    exact zeroRow2_mem_Wself hgoal

/-- **The shifted copy tower over a row-2-free block is free.**  Every column of
the tower is a row-0 shift of a column of `Q`, and `shiftr01` does not touch row
2, so `zeroRow2_mem_Wself` applies.  Together with `|Q| = 1` (a constant
diagonal, `diagz_mem_W`) and `e = 0` (identical copies, `W_flatMap_copies`) this
pins `(TOW)`'s content to `|Q| ≥ 2` carrying a row-2 column. -/
theorem shTower_zeroRow2 {Q : TrioSeq} (hz : ∀ p ∈ Q, p.2.2 = 0) (e n : ℕ) :
    shTower Q e n ∈ Wself := by
  refine zeroRow2_mem_Wself (fun q hq => ?_)
  unfold shTower at hq
  rw [List.mem_flatMap] at hq
  obtain ⟨k, -, hk⟩ := hq
  unfold shiftr01 at hk
  rw [List.mem_map] at hk
  obtain ⟨p, hp, rfl⟩ := hk
  exact hz p hp

/-- **Every subtree, re-based to depth 0, is a `based` `W`-member at its own
level** — the shape `Aop`'s clause 3 wants for its graft argument. -/
theorem drop_rebase_mem_W {u : ℕ} {M : TrioSeq} (h : M ∈ W u) (j : ℕ)
    (hsub : ∀ x ∈ M.drop j, entry M 0 j ≤ x.1) :
    shiftl0 (entry M 0 j) (M.drop j) ∈ W (lev M j) :=
  W_shiftl0 (W_drop h j) hsub

theorem drop_mem_Wself {u : ℕ} {M : TrioSeq} (h : M ∈ W u) (j : ℕ) :
    M.drop j ∈ Wself := by
  have := W_drop h j
  rwa [← lev_drop_head M j] at this

/-- `Wself` is closed under expansion: the root column survives every step, so
the stage does not move. -/
theorem oper_mem_Wself {M : TrioSeq} (h : M ∈ Wself) {n : ℕ} (hn : 1 ≤ n) :
    M⟦n⟧ ∈ Wself := by
  classical
  rcases Nat.lt_or_ge 1 M.length with hL | hL
  · have hlev : lev (M⟦n⟧) 0 = lev M 0 := by
      have htk := oper_take_prefix hL hn (i := 1) (by omega)
      have e : ∀ i, entry (M⟦n⟧) i 0 = entry M i 0 := by
        intro i
        rw [← Wset.entry_take (X := M⟦n⟧) (l := 1) (i := i) (by omega),
          ← Wset.entry_take (X := M) (l := 1) (i := i) (by omega), htk]
      unfold lev
      rw [e 1, e 2]
    show M⟦n⟧ ∈ W (lev (M⟦n⟧) 0)
    rw [hlev]
    exact oper_closed h hn
  · rw [oper_eq_self_of_short n (by omega)]
    exact h

/-- The root of a substituted sequence: the block's root when `p = 0`, the
host's otherwise. -/
theorem entry_subst_root {S C : TrioSeq} {p : ℕ} (hCne : C ≠ []) (hp : p < S.length)
    (i : ℕ) : entry (S.take p ++ C ++ S.drop (p + 1)) i 0
      = if p = 0 then entry C i 0 else entry S i 0 := by
  have hCpos : 0 < C.length := List.length_pos_iff.mpr hCne
  have htk : (S.take p).length = min p S.length := List.length_take
  rcases Nat.eq_zero_or_pos p with rfl | hpp
  · rw [if_pos rfl, List.take_zero, List.nil_append,
      entry_append_left _ _ (by omega)]
  · rw [if_neg (by omega), entry_append_left _ _ (by rw [List.length_append]; omega),
      entry_append_left _ _ (by omega), entry_take (by omega)]

/-- **The residue of `(SUBST1g)`: the context revives a dead orphan.**

`subst1g_of_revive` closes every other case.  Writing `D = S.drop (p+1)` and `R`
for the substituted sequence, what survives is exactly: `R`'s trailing column HAS
a parent, although it is an ORPHAN inside the block it belongs to — the block `C`
itself when `D = []`, and the tail `D` otherwise.  So the parent is supplied by
the CONTEXT.  This is the shape the whole campaign keeps meeting (装置 γ).

The depth condition is the NON-STRICT one, because that is what `oper` preserves
(`oper_mem_ge`); it is what the nested induction on the block needs, and it is
measured just as clean (165768 instances with at least one flush column,
0 violations). -/
def Subst1gRevive : Prop :=
  ∀ (u p : ℕ) (S C : TrioSeq), S ∈ W u → p < S.length → C ≠ [] →
    C ∈ W (lev S p) →
    entry C 0 0 = entry S 0 p →
    (∀ q ∈ C, entry S 0 p ≤ q.1) →
    hasParent (S.take p ++ C ++ S.drop (p + 1))
      (srow (S.take p ++ C ++ S.drop (p + 1))
        ((S.take p ++ C ++ S.drop (p + 1)).length - 1))
      ((S.take p ++ C ++ S.drop (p + 1)).length - 1) →
    ((S.drop (p + 1) = [] ∧
        ¬ hasParent C (srow C (C.length - 1)) (C.length - 1)) ∨
      (S.drop (p + 1) ≠ [] ∧
        ¬ hasParent (S.drop (p + 1))
          (srow (S.drop (p + 1)) ((S.drop (p + 1)).length - 1))
          ((S.drop (p + 1)).length - 1))) →
    (S.take p ++ C ++ S.drop (p + 1)) ∈ W u

/-- **★★★ The residue with the STAGE QUANTIFIER REMOVED.**

`mem_Wself_iff` collapses the whole `W`-family to the single set `Wself` plus a
root-level side condition, and a substitution never raises the root level
(`entry_subst_root`: the root is the block's when `p = 0` and the host's
otherwise).  So `u` drops out of the core entirely. -/
def Subst1gReviveSelf : Prop :=
  ∀ (p : ℕ) (S C : TrioSeq), S ∈ Wself → p < S.length → C ≠ [] →
    C ∈ Wself → lev C 0 ≤ lev S p →
    entry C 0 0 = entry S 0 p →
    (∀ q ∈ C, entry S 0 p ≤ q.1) →
    hasParent (S.take p ++ C ++ S.drop (p + 1))
      (srow (S.take p ++ C ++ S.drop (p + 1))
        ((S.take p ++ C ++ S.drop (p + 1)).length - 1))
      ((S.take p ++ C ++ S.drop (p + 1)).length - 1) →
    ((S.drop (p + 1) = [] ∧
        ¬ hasParent C (srow C (C.length - 1)) (C.length - 1)) ∨
      (S.drop (p + 1) ≠ [] ∧
        ¬ hasParent (S.drop (p + 1))
          (srow (S.drop (p + 1)) ((S.drop (p + 1)).length - 1))
          ((S.drop (p + 1)).length - 1))) →
    (∃ q ∈ (S.take p ++ C ++ S.drop (p + 1)).dropLast, 0 < q.2.2) →
    (S.take p ++ C ++ S.drop (p + 1)) ∈ Wself

theorem subst1gRevive_of_self (h : Subst1gReviveSelf) : Subst1gRevive := by
  intro u p S C hS hp hCne hCW hhead hdeep hRp hdisj
  obtain ⟨hSself, hSlev⟩ := (mem_Wself_iff u S).mp hS
  obtain ⟨hCself, hClev⟩ := (mem_Wself_iff (lev S p) C).mp hCW
  refine (mem_Wself_iff u _).mpr ⟨?_, ?_⟩
  · by_cases hz2 : ∃ q ∈ (S.take p ++ C ++ S.drop (p + 1)).dropLast, 0 < q.2.2
    · exact h p S C hSself hp hCne hCself hClev hhead hdeep hRp hdisj hz2
    · have hCpos : 0 < C.length := List.length_pos_iff.mpr hCne
      have hRne : S.take p ++ C ++ S.drop (p + 1) ≠ [] := by
        intro hc
        have hl : (S.take p ++ C ++ S.drop (p + 1)).length = 0 := by rw [hc]; simp
        rw [List.length_append, List.length_append] at hl
        omega
      have hzz : ∀ q ∈ (S.take p ++ C ++ S.drop (p + 1)).dropLast, q.2.2 = 0 := by
        intro q hq
        by_contra hc
        exact hz2 ⟨q, hq, by omega⟩
      have hsn := snoc_zeroRow2 hzz ((S.take p ++ C ++ S.drop (p + 1)).getLast hRne)
      rwa [List.dropLast_append_getLast hRne] at hsn
  have hr : ∀ i, entry (S.take p ++ C ++ S.drop (p + 1)) i 0
      = if p = 0 then entry C i 0 else entry S i 0 :=
    fun i => entry_subst_root hCne hp i
  rcases Nat.eq_zero_or_pos p with hp0 | hpp
  · have he : lev (S.take p ++ C ++ S.drop (p + 1)) 0 = lev C 0 := by
      unfold lev; rw [hr 1, hr 2, if_pos hp0, if_pos hp0]
    rw [he]
    have : lev C 0 ≤ lev S p := hClev
    rw [hp0] at this
    omega
  · have he : lev (S.take p ++ C ++ S.drop (p + 1)) 0 = lev S 0 := by
      unfold lev; rw [hr 1, hr 2, if_neg (by omega), if_neg (by omega)]
    rw [he]; exact hSlev

theorem not_hasParent_zero {M : TrioSeq} {i : ℕ} (h : hasParent M i 0) : False := by
  obtain ⟨j0, hj0, -⟩ := h
  exact absurd (nextR_index_lt hj0) (Nat.not_lt_zero j0)

open Classical in
/-- **★★ End substitution, by a nested induction on the BLOCK's datum.**

`S ≠ []` and a block `C` rooted at `S`'s trailing column: `S.dropLast ++ C ∈ W u`.
Induct on `C`'s `W` datum over the prefix-closed property (prefixes free, as
before).  With `A = S.dropLast`:

* `C`'s trailing column has a parent INSIDE `C` — `oper_append_inner` gives
  `(A ++ C)⟦n⟧ = A ++ C⟦n⟧`, and `C`'s clause-2 datum carries it (clause 3 is
  impossible: a dominant terminal is parentless);
* it is an orphan in `A ++ C` too — `oper_append_pred` peels to `A ++ C.dropLast`,
  supplied by the prefix package (or `A ∈ W u` itself when `C` is a singleton);
* it is an orphan in `C` but revived by `A` — the residue.

`S.dropLast = []` is separate and free: the goal is then `C ∈ W u`, and
`lev_root_le_of_mem_W` puts `C`'s stage below `u`. -/
theorem end_subst_of_revive (hrev : Subst1gRevive) {u : ℕ} {S : TrioSeq}
    (hS : S ∈ W u) (hSne : S ≠ []) :
    ∀ C : TrioSeq, C ∈ W (lev S (S.length - 1)) → C ≠ [] →
      entry C 0 0 = entry S 0 (S.length - 1) →
      (∀ q ∈ C, entry S 0 (S.length - 1) ≤ q.1) →
      (S.dropLast ++ C) ∈ W u := by
  classical
  have hSlen : 0 < S.length := List.length_pos_iff.mpr hSne
  have hdlen : S.dropLast.length = S.length - 1 := List.length_dropLast
  have hST : S.take (S.length - 1) = S.dropLast := List.dropLast_eq_take.symm
  have hSD : S.drop (S.length - 1 + 1) = [] :=
    List.drop_eq_nil_of_le (by omega)
  by_cases hAnil : S.dropLast = []
  · intro C hCW hCne _ _
    rw [hAnil, List.nil_append]
    have h1 : S.length = 1 := by
      have : S.dropLast.length = 0 := by rw [hAnil]; simp
      omega
    exact W_mono (by rw [h1]; exact lev_root_le_of_mem_W hS hSne) hCW
  · have hAlen : 0 < S.dropLast.length := List.length_pos_iff.mpr hAnil
    have hsub : W (lev S (S.length - 1)) ⊆
        {B : TrioSeq | B ∈ W (lev S (S.length - 1)) ∧ ∀ k,
          (B.take k ≠ [] → entry (B.take k) 0 0 = entry S 0 (S.length - 1) →
            (∀ q ∈ B.take k, entry S 0 (S.length - 1) ≤ q.1) →
            (S.dropLast ++ B.take k) ∈ W u)} := by
      refine A2' ?_
      intro B hA
      have hmemB : B ∈ W (lev S (S.length - 1)) := by
        refine A1_intro ?_
        rcases hA with h | h | ⟨m, hm, hd, hgr⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl fun n hn => (h n hn).1)
        · exact Or.inr (Or.inr ⟨m, hm, hd, fun z hz hb => (hgr z hz hb).1⟩)
      have hpre : ∀ k, k < B.length → (B.take k ≠ [] →
          entry (B.take k) 0 0 = entry S 0 (S.length - 1) →
          (∀ q ∈ B.take k, entry S 0 (S.length - 1) ≤ q.1) →
          (S.dropLast ++ B.take k) ∈ W u) := by
        intro k hk
        rcases hA with h | h | ⟨m, hm, hd, hgr⟩
        · rw [show k = 0 from by omega, List.take_zero]
          intro hc; exact absurd rfl hc
        · rcases Nat.lt_or_ge 1 B.length with hBlen | hBlen
          · have := (h 1 le_rfl).2 k
            rwa [oper_take_prefix hBlen le_rfl (by omega)] at this
          · rw [show k = 0 from by omega, List.take_zero]
            intro hc; exact absurd rfl hc
        · rcases Nat.lt_or_ge 1 B.length with hBlen | hBlen
          · have := (hgr [] (W_nil m) based_nil).2 k
            rwa [graft_nil, List.dropLast_eq_take, List.take_take,
              show min k (B.length - 1) = k from by omega] at this
          · rw [show k = 0 from by omega, List.take_zero]
            intro hc; exact absurd rfl hc
      have hmain : B ≠ [] → entry B 0 0 = entry S 0 (S.length - 1) →
          (∀ q ∈ B, entry S 0 (S.length - 1) ≤ q.1) →
          (S.dropLast ++ B) ∈ W u := by
        intro hBne hhead hdeep
        have hBlen : 0 < B.length := List.length_pos_iff.mpr hBne
        have hcat : 1 < (S.dropLast ++ B).length := by
          rw [List.length_append]; omega
        by_cases hBp : hasParent B (srow B (B.length - 1)) (B.length - 1)
        · have hBL : B.length - 1 ≠ 0 := by
            have := nextR_index_lt (parent_nextR hBp); omega
          have hdatum : ∀ n, 1 ≤ n → (B⟦n⟧ ≠ [] →
              entry (B⟦n⟧) 0 0 = entry S 0 (S.length - 1) →
              (∀ q ∈ B⟦n⟧, entry S 0 (S.length - 1) ≤ q.1) →
              (S.dropLast ++ B⟦n⟧) ∈ W u) := by
            rcases hA with h | h | ⟨m, hm, hd, hgr⟩
            · exact absurd h.1 (by omega)
            · intro n hn
              have := (h n hn).2 (B⟦n⟧).length
              rwa [List.take_length] at this
            · exact absurd hBp hd.2
          refine mem_of_oper_mem (fun n hn => ?_)
          rw [oper_append_inner n hBne hBL hBp]
          obtain ⟨R', hR'⟩ := oper_eq_dropLast_append (M := B) (by omega) hn
          refine hdatum n hn (by
              intro hc
              rw [hc] at hR'
              have : B.dropLast.length = 0 := by
                have := congrArg List.length hR'.symm
                simp at this
                omega
              rw [List.length_dropLast] at this
              omega)
            (by rw [oper_head_eq hn]; exact hhead) (oper_mem_ge hdeep)
        · by_cases hRp : hasParent (S.dropLast ++ B)
              (srow (S.dropLast ++ B) ((S.dropLast ++ B).length - 1))
              ((S.dropLast ++ B).length - 1)
          · have hgo := hrev u (S.length - 1) S B hS (by omega) hBne
              hmemB hhead hdeep
            rw [hST, hSD, List.append_nil] at hgo
            exact hgo hRp (Or.inl ⟨rfl, hBp⟩)
          · refine mem_of_oper_mem (fun n hn => ?_)
            rw [oper_append_pred n hBne (by omega) hRp]
            by_cases hdl : B.dropLast = []
            · rw [hdl, List.append_nil]
              exact W_dropLast hS
            · have hdlne : B.take (B.length - 1) ≠ [] := by
                rwa [← List.dropLast_eq_take]
              have hhd : entry (B.take (B.length - 1)) 0 0
                  = entry S 0 (S.length - 1) := by
                rw [entry_take (show (0:ℕ) < B.length - 1 by
                  rw [← List.length_dropLast]
                  exact List.length_pos_iff.mpr hdl)]
                exact hhead
              have hdp : ∀ q ∈ B.take (B.length - 1),
                  entry S 0 (S.length - 1) ≤ q.1 :=
                fun q hq => hdeep q (List.mem_of_mem_take hq)
              have := hpre (B.length - 1) (by omega) hdlne hhd hdp
              rwa [← List.dropLast_eq_take] at this
      refine ⟨hmemB, fun k => ?_⟩
      rcases Nat.lt_or_ge k B.length with hk | hk
      · exact hpre k hk
      · rw [List.take_of_length_le hk]
        exact hmain
    intro C hCW hCne hhead hdeep
    have h := (hsub hCW).2 C.length
    rw [List.take_length] at h
    exact h hCne hhead hdeep

open Classical in
/-- **★★★ `(SUBST1g)` minus the revival case.**

Induct on the host's `W` datum, over the PREFIX-CLOSED property
`∀ k, SubstProp u (M.take k)` — prefixes come free from the datum
(`oper_take_prefix` for clause 2, `graft M [] = M.dropLast` for clause 3), and
having them is what pays for the orphan case below.  Write `D = S.drop (p+1)`.

* **mirror** (`D` has ≥ 2 columns and its trailing column has a parent INSIDE
  `D`): `Xbar.oper_append_inner` — which needs no `rsum` — applies to both
  `S = S.take (p+1) ++ D` and `R = (S.take p ++ C) ++ D` with the SAME
  hypothesis, so `S⟦n⟧ = S.take (p+1) ++ D⟦n⟧` and `R⟦n⟧ = (S.take p ++ C) ++ D⟦n⟧`.
  The column at `p` survives with all three entries, so the datum at `S⟦n⟧` IS
  the goal.
* **orphan** (`D ≠ []` and `R`'s trailing column has no parent in `R` either):
  `R⟦n⟧ = Pred R = S.take p ++ C ++ D.dropLast`, which is the substitution
  applied to the PREFIX `S.dropLast` — supplied by the prefix package.
* clause 1 (`|S| ≤ 1`, `lev S 0 = 0`) is immediate: `C ∈ W 0 ⊆ W u`.

What is left is `Subst1gRevive`. -/
theorem subst1g_of_revive (hrev : Subst1gRevive) : Subst1g := by
  classical
  intro u
  have hsub : W u ⊆ {M : TrioSeq | M ∈ W u ∧ ∀ k, SubstProp u (M.take k)} := by
    refine A2' ?_
    intro M hA
    have hmem : M ∈ W u := by
      refine A1_intro ?_
      rcases hA with h | h | ⟨m, hm, hd, hgr⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl fun n hn => (h n hn).1)
      · exact Or.inr (Or.inr ⟨m, hm, hd, fun z hz hb => (hgr z hz hb).1⟩)
    -- the whole prefix package of `M`, minus `M` itself
    have hpre : ∀ k, k < M.length → SubstProp u (M.take k) := by
      intro k hk
      rcases hA with h | h | ⟨m, hm, hd, hgr⟩
      · have hk0 : k = 0 := by omega
        rw [hk0, List.take_zero]
        exact substProp_nil u
      · rcases Nat.lt_or_ge 1 M.length with hMlen | hMlen
        · have := (h 1 le_rfl).2 k
          rwa [oper_take_prefix hMlen le_rfl (by omega)] at this
        · rw [show k = 0 from by omega, List.take_zero]
          exact substProp_nil u
      · rcases Nat.lt_or_ge 1 M.length with hMlen | hMlen
        · have := (hgr [] (W_nil m) based_nil).2 k
          rwa [graft_nil, List.dropLast_eq_take, List.take_take,
            show min k (M.length - 1) = k from by omega] at this
        · rw [show k = 0 from by omega, List.take_zero]
          exact substProp_nil u
    -- and the main step
    have hmain : SubstProp u M := by
      intro p C hp hCne hCW hhead hdeep
      set D : TrioSeq := M.drop (p + 1) with hD
      have hDlen0 : D.length = M.length - (p + 1) := by rw [hD]; simp
      by_cases hmir : 2 ≤ D.length ∧
          hasParent D (srow D (D.length - 1)) (D.length - 1)
      · obtain ⟨hDlen, hDp⟩ := hmir
        have hDne : D ≠ [] := by intro h; rw [h] at hDlen; simp at hDlen
        have hDL : D.length - 1 ≠ 0 := by omega
        have htk : (M.take (p + 1)).length = p + 1 := by
          have h2 : (M.take (p + 1)).length = min (p + 1) M.length := List.length_take
          omega
        have hdatum : ∀ n, 1 ≤ n → SubstProp u (M⟦n⟧) := by
          rcases hA with h | h | ⟨m, hm, hd, hgr⟩
          · exact absurd h.1 (by omega)
          · intro n hn
            have := (h n hn).2 (M⟦n⟧).length
            rwa [List.take_length] at this
          · intro n hn
            rw [oper_eq_graft_nil_of_domT (by omega) hd]
            have := (hgr [] (W_nil m) based_nil).2 (graft M []).length
            rwa [List.take_length] at this
        refine mem_of_oper_mem (fun n hn => ?_)
        have hMsplit : M.take (p + 1) ++ D = M := List.take_append_drop _ _
        have hOpM : M⟦n⟧ = M.take (p + 1) ++ D⟦n⟧ := by
          conv_lhs => rw [← hMsplit]
          exact oper_append_inner n hDne hDL hDp
        have hOpR : (M.take p ++ C ++ D)⟦n⟧ = (M.take p ++ C) ++ D⟦n⟧ :=
          oper_append_inner n hDne hDL hDp
        rw [hOpR]
        have hent : ∀ i, entry (M⟦n⟧) i p = entry M i p := by
          intro i
          rw [hOpM, entry_append_left _ _ (by rw [htk]; omega), entry_take (by omega)]
        have hlv : lev (M⟦n⟧) p = lev M p := by unfold lev; rw [hent 1, hent 2]
        have hlen' : p < (M⟦n⟧).length := by
          rw [hOpM, List.length_append, htk]; omega
        have hstep := hdatum n hn p C hlen' hCne (by rw [hlv]; exact hCW)
          (by rw [hent 0]; exact hhead)
          (by intro q hq; rw [hent 0]; exact hdeep q hq)
        have htake' : (M⟦n⟧).take p = M.take p := by
          rw [hOpM, List.take_append_of_le_length (by omega), List.take_take]
          congr 1
          omega
        have hdrop' : (M⟦n⟧).drop (p + 1) = D⟦n⟧ := by
          have hdl : ((M.take (p + 1)) ++ D⟦n⟧).drop (M.take (p + 1)).length = D⟦n⟧ :=
            List.drop_left
          rw [htk] at hdl
          rw [hOpM, hdl]
        rwa [htake', hdrop'] at hstep
      · by_cases hDnil : D = []
        · -- nothing after the block: end substitution on the prefix `M.take (p+1)`
          have hTne : M.take (p + 1) ≠ [] := by
            intro hc
            have : (M.take (p + 1)).length = 0 := by rw [hc]; simp
            have h2 : (M.take (p + 1)).length = min (p + 1) M.length := List.length_take
            omega
          have htk1 : (M.take (p + 1)).length - 1 = p := by
            have h2 : (M.take (p + 1)).length = min (p + 1) M.length := List.length_take
            omega
          have hdl1 : (M.take (p + 1)).dropLast = M.take p := by
            rw [List.dropLast_eq_take, htk1, List.take_take,
              show min p (p + 1) = p from by omega]
          have hE1 : ∀ i, entry (M.take (p + 1)) i p = entry M i p :=
            fun i => entry_take (by omega)
          have hgo := end_subst_of_revive hrev (W_take hmem (p + 1)) hTne C
            (by rw [htk1]; unfold lev; rw [hE1 1, hE1 2]; exact hCW) hCne
            (by rw [htk1, hE1 0]; exact hhead)
            (by intro q hq; rw [htk1, hE1 0]; exact hdeep q hq)
          rw [hdl1] at hgo
          rw [hDnil, List.append_nil]
          exact hgo
        · have hDpos : 0 < D.length := List.length_pos_iff.mpr hDnil
          have hCpos : 0 < C.length := List.length_pos_iff.mpr hCne
          have hRlen : 1 < (M.take p ++ C ++ D).length := by
            rw [List.length_append, List.length_append]
            omega
          have hnoD : ¬ hasParent D (srow D (D.length - 1)) (D.length - 1) := by
            intro hc
            rcases Nat.lt_or_ge D.length 2 with hsm | hbig
            · have h1 : D.length - 1 = 0 := by omega
              rw [h1] at hc
              exact not_hasParent_zero hc
            · exact hmir ⟨hbig, hc⟩
          by_cases hRp : hasParent (M.take p ++ C ++ D)
              (srow (M.take p ++ C ++ D) ((M.take p ++ C ++ D).length - 1))
              ((M.take p ++ C ++ D).length - 1)
          · exact hrev u p M C hmem hp hCne hCW hhead hdeep hRp
              (Or.inr ⟨hDnil, hnoD⟩)
          · -- orphan: `oper` peels, and the peel is the substitution on `M.dropLast`
            refine mem_of_oper_mem (fun n hn => ?_)
            rw [oper_append_pred n hDnil (by omega) hRp]
            have hpd : p < (M.dropLast).length := by
              rw [List.length_dropLast]; omega
            have hdlt : (M.dropLast).take p = M.take p := by
              rw [List.dropLast_eq_take, List.take_take,
                show min p (M.length - 1) = p from by omega]
            have hdld : (M.dropLast).drop (p + 1) = D.dropLast := by
              rw [List.dropLast_eq_take, List.drop_take, ← hD, List.dropLast_eq_take]
              congr 1
              rw [hDlen0]
              omega
            have hentd : ∀ i, entry (M.dropLast) i p = entry M i p := by
              intro i
              rw [List.dropLast_eq_take]
              exact entry_take (by omega)
            have hlvd : lev (M.dropLast) p = lev M p := by
              unfold lev; rw [hentd 1, hentd 2]
            have hstep := hpre (M.length - 1) (by omega) p C
              (by rw [← List.dropLast_eq_take]; exact hpd) hCne
              (by rw [← List.dropLast_eq_take, hlvd]; exact hCW)
              (by rw [← List.dropLast_eq_take, hentd 0]; exact hhead)
              (by
                intro q hq
                rw [← List.dropLast_eq_take, hentd 0]
                exact hdeep q hq)
            rw [← List.dropLast_eq_take, hdlt, hdld] at hstep
            exact hstep
    refine ⟨hmem, fun k => ?_⟩
    rcases Nat.lt_or_ge k M.length with hk | hk
    · exact hpre k hk
    · rw [List.take_of_length_le hk]
      exact hmain
  intro p S C hS hp hCne hCW hhead hdeep
  have h := (hsub hS).2 S.length
  rw [List.take_length] at h
  exact h p C hp hCne hCW hhead (mem_ge_of_deep hhead hdeep)

section ShiftEntry

variable {Q : TrioSeq} {d j : ℕ}

theorem entry0_shift (hj : j < Q.length) :
    entry (shiftr01 d 0 Q) 0 j = entry Q 0 j + d := by
  unfold entry
  rw [shiftr01_getD hj]
  simp

theorem entry1_shift (hj : j < Q.length) :
    entry (shiftr01 d 0 Q) 1 j = entry Q 1 j := by
  unfold entry
  rw [shiftr01_getD hj]
  simp

theorem entry2_shift (hj : j < Q.length) :
    entry (shiftr01 d 0 Q) 2 j = entry Q 2 j := by
  unfold entry
  rw [shiftr01_getD hj]
  simp

end ShiftEntry

open Classical in
/-- **★★ `(TOW)` from `(SUBST)`.**

The tower's spine is the CONSTANT diagonal `[(x0 + k*e, b, c)]_{k<n}` sitting at
the stage's own level `2b+c = u` — in `W u` by `diagz_mem_W` with `f = 0`, or by
`constcol_mem_W` when `e = 0`.  Copy `k` is `shiftr01 (k*e) 0 Q ∈ W u`, exactly
`W (lev spine k)`, rooted at the spine column `x0 + k*e` and strictly deeper
elsewhere — which is where `ShiftTowerClosedS`'s strict root-minimality is
consumed.  So `(SUBST)` absorbs the last consumer of `(CAT)`. -/
theorem shiftTowerClosedS_of_substG (hg : SubstClosedG) : ShiftTowerClosedS := by
  classical
  intro u e n Q hQ hs
  have hflat : shTower Q e n
      = (List.range n).flatMap (fun k => shiftr01 (k * e) 0 Q) := rfl
  by_cases hQnil : Q = []
  · subst hQnil
    have hnil : ∀ m : ℕ,
        (List.range m).flatMap (fun k => shiftr01 (k * e) 0 ([] : TrioSeq)) = [] := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [List.range_succ, List.flatMap_append, ih]; simp
    rw [hflat, hnil]
    exact W_nil u
  · have hQlen : 0 < Q.length := List.length_pos_iff.mpr hQnil
    have hbc : 2 * (u / 2) + u % 2 = u := by omega
    have hc1 : u % 2 ≤ 1 := by omega
    set D : TrioSeq :=
      (List.range n).map (fun k => ((k * e, u / 2, u % 2) : ℕ × ℕ × ℕ)) with hD
    have hDlen : D.length = n := by rw [hD]; simp
    have hDget : ∀ k, k < n →
        D.getD k ((0, 0, 0) : ℕ × ℕ × ℕ) = ((k * e, u / 2, u % 2) : ℕ × ℕ × ℕ) := by
      intro k hk
      rw [hD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (by simpa using hk)]
      simp
    have hDmem : D ∈ W u := by
      rcases Nat.eq_zero_or_pos e with he | he
      · have heq : D = (List.range n).map (fun _ => ((0, u / 2, u % 2) : ℕ × ℕ × ℕ)) := by
          rw [hD, he]; simp
        have hcc := constcol_mem_W (u / 2) (u % 2) n
        rw [hbc] at hcc
        rw [heq]
        exact hcc
      · have hd0 := diagz_mem_W hc1 (u / 2) e 0 he n
        have heq : ((List.range n).map
            (fun k => ((k * e, u / 2 + k * 0, u % 2) : ℕ × ℕ × ℕ))) = D := by
          rw [hD]; simp
        rw [heq, hbc] at hd0
        exact hd0
    set H : TrioSeq := shiftr01 (entry Q 0 0) 0 D with hH
    have hHlen : H.length = n := by rw [hH, shiftr01_length, hDlen]
    have hHmem : H ∈ W u := by rw [hH]; exact W_shift hDmem _
    have hHent0 : ∀ k, k < n → entry H 0 k = entry Q 0 0 + k * e := by
      intro k hk
      rw [hH, entry0_shift (by omega : k < D.length)]
      have : entry D 0 k = k * e := by unfold entry; rw [hDget k hk]; simp
      omega
    have hHlev : ∀ k, k < n → lev H k = u := by
      intro k hk
      have h1 : entry D 1 k = u / 2 := by unfold entry; rw [hDget k hk]; simp
      have h2 : entry D 2 k = u % 2 := by unfold entry; rw [hDget k hk]; simp
      unfold lev
      rw [hH, entry1_shift (by omega : k < D.length),
        entry2_shift (by omega : k < D.length), h1, h2]
      omega
    set B : ℕ → TrioSeq := fun k => shiftr01 (k * e) 0 Q with hB
    have hBlen : ∀ k, (B k).length = Q.length := by
      intro k; rw [hB]; exact shiftr01_length _ _ _
    have hmain := hg u H B hHmem
      (by intro k hk; rw [hBlen k]; exact hQlen)
      (by
        intro k hk
        rw [hHlen] at hk
        simp only [hB]
        rw [entry0_shift hQlen, hHent0 k hk])
      (by
        intro k hk j hj1 hjl
        rw [hHlen] at hk
        rw [hBlen k] at hjl
        simp only [hB]
        rw [entry0_shift hjl, hHent0 k hk]
        have := hs j hj1 hjl
        omega)
      (by
        intro k hk
        rw [hHlen] at hk
        rw [hHlev k hk]
        simp only [hB]
        exact W_shift hQ _)
    rw [hHlen] at hmain
    rw [hflat]
    exact hmain

open Classical in
/-- **★★ The `m < a` half of `TowerExp`, from `(SUBST)` instead of `(CAT)`.**

The two-column sequence `[(0,v,z), t]` — `t` the trailing column that the root
revives — is in `W a` outright (`two_col_mem_W`), and its two levels are exactly
`2v+z` and `m+1`.  Grafting the peel `p_{v,z}(R.dropLast) ∈ W (2v+z)` under the
first column and the singleton `[t] ∈ W (m+1)` under the second rebuilds
`p_{v,z}(R)`.  `(CAT)` needed BOTH sides in `W a`; here the deep column is paid
for by its own host column. -/
theorem cons_mem_W_of_substG (hg : SubstClosedG) {v z m a : ℕ} {R : TrioSeq}
    (hR : argOK R) (hRne : R ≠ []) (hz1 : z ≤ 1) (hva : 2 * v + z ≤ a)
    (hd : domT R m) (hma : m < a) (hop : ∀ n, 1 ≤ n → R⟦n⟧ ∈ Wstar) :
    (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W a := by
  classical
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  set t : ℕ × ℕ × ℕ := R.getLast hRne with ht
  have hqd : t = R.getD (R.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) := by
    rw [ht, List.getLast_eq_getElem, getElem_eq_getD' (by omega)]
  have hlv : 2 * t.2.1 + t.2.2 = m + 1 := by
    have hl := hd.1
    unfold lev entry at hl
    rw [hqd]
    simpa using hl
  set C : TrioSeq := ((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast with hC
  have hCA : C ∈ W (2 * v + z) := by
    rcases Nat.lt_or_ge R.length 2 with hsm | hbig
    · have hdl : R.dropLast = [] := List.eq_nil_of_length_eq_zero (by simp; omega)
      rw [hC, hdl]
      exact Om_mem_W v z
    · have h1 := hop 1 le_rfl
      rw [oper_eq_graft_nil_of_domT (n := 1) (by omega) hd, graft_nil] at h1
      exact h1 (argOK_dropLast hR) v z (2 * v + z) hz1 le_rfl
  set Q : TrioSeq := [((0, v, z) : ℕ × ℕ × ℕ), t] with hQ
  have hQlen : Q.length = 2 := by rw [hQ]; simp
  have hQmem : Q ∈ W a := two_col_mem_W hz1 hva t
  have hQ0 : entry Q 0 0 = 0 := by rw [hQ]; simp [entry]
  have hQ1 : entry Q 0 1 = t.1 := by rw [hQ]; simp [entry]
  have hlvQ0 : lev Q 0 = 2 * v + z := by rw [hQ]; simp [lev, entry]
  have hlvQ1 : lev Q 1 = m + 1 := by rw [hQ]; simp [lev, entry]; omega
  set B : ℕ → TrioSeq := fun k => if k = 0 then C else [t] with hB
  have hB0 : B 0 = C := by rw [hB]; simp
  have hB1 : B 1 = [t] := by rw [hB]; simp
  have hCdeep : ∀ j, 1 ≤ j → j < C.length → 0 < entry C 0 j := by
    intro j hj1 hjl
    have hClen : C.length = R.dropLast.length + 1 := by rw [hC]; simp
    have hjR : j - 1 < R.dropLast.length := by omega
    have hshift : entry C 0 j = entry R.dropLast 0 (j - 1) := by
      rw [hC]
      conv_lhs => rw [show j = (j - 1) + 1 by omega]
      rw [entry_cons]
    rw [hshift]
    exact argOK_dropLast hR _ (entry_pair_mem hjR)
  have hmain := hg a Q B hQmem
    (by
      intro k hk
      rw [hQlen] at hk
      rcases Nat.lt_or_ge k 1 with hk0 | hk1
      · have hkk : k = 0 := by omega
        subst hkk; rw [hB0, hC]; simp
      · have hkk : k = 1 := by omega
        subst hkk; rw [hB1]; simp)
    (by
      intro k hk
      rw [hQlen] at hk
      rcases Nat.lt_or_ge k 1 with hk0 | hk1
      · have hkk : k = 0 := by omega
        subst hkk; rw [hB0, hQ0, hC]; simp [entry]
      · have hkk : k = 1 := by omega
        subst hkk; rw [hB1, hQ1]; simp [entry])
    (by
      intro k hk j hj1 hjl
      rw [hQlen] at hk
      rcases Nat.lt_or_ge k 1 with hk0 | hk1
      · have hkk : k = 0 := by omega
        subst hkk
        rw [hB0] at hjl ⊢
        rw [hQ0]
        exact hCdeep j hj1 hjl
      · have hkk : k = 1 := by omega
        subst hkk
        rw [hB1] at hjl; simp at hjl; omega)
    (by
      intro k hk
      rw [hQlen] at hk
      rcases Nat.lt_or_ge k 1 with hk0 | hk1
      · have hkk : k = 0 := by omega
        subst hkk; rw [hB0, hlvQ0]; exact hCA
      · have hkk : k = 1 := by omega
        subst hkk
        rw [hB1, hlvQ1]
        have hte : t = ((t.1, t.2.1, t.2.2) : ℕ × ℕ × ℕ) := rfl
        rw [hte]
        exact singleton_mem_W (by omega))
  rw [hQlen] at hmain
  have hflat : (List.range 2).flatMap B = C ++ [t] := by
    rw [show (List.range 2) = [0, 1] from rfl]
    simp [hB0, hB1]
  rw [hflat, hC, List.cons_append, ht, List.dropLast_append_getLast hRne] at hmain
  exact hmain

/-- **★★ `TowerExp` with `(CAT)` fully replaced by `(SUBST)`.**  The `m < a`
half is `cons_mem_W_of_substG`, the row-1 half is the shifted copy tower, and the
row-2 half at `a ≤ m` is the low core. -/
theorem towerExp_of_substG (hg : SubstClosedG) (htow : ShiftTowerClosedS)
    (h2 : TowerExp2Low) : Wset.TowerExp := by
  intro v z m a R hR hRne hz1 hva hd hop hpM n hn
  rcases Nat.lt_or_ge m a with hma | hma
  · exact oper_closed (cons_mem_W_of_substG hg hR hRne hz1 hva hd hma hop) hn
  · have hlevpos : 0 < lev R (R.length - 1) := by rw [hd.1]; omega
    unfold lev at hlevpos
    rcases srow_cases R (R.length - 1) with hsr | hsr | hsr
    · exfalso
      unfold srow at hsr
      split at hsr
      · omega
      · split at hsr
        · omega
        · omega
    · exact towerExp1_of_tower htow v z m a R hR hRne hz1 hva hd hop hsr hpM n hn
    · exact h2 v z m a R hR hRne hz1 hva hma hd hop hsr hpM n hn

open Classical in
/-- **★ `TowerExp2Root` from `(SUBST)` and the stage law `(WL)`.**

`M⟦n⟧` is the tower of guarded copies (`gcopies_eq_tower`); copy `k` is
`shiftr01 (k*d0) 0 (Lift1 M.dropLast (k*d1))`, rooted at the diagonal column
`(k*d0, v + k*d1, z)` and — by `(WL)` applied to `M.dropLast ∈ W (2v+z)` — living
in `W (2*(v + k*d1) + z)`, exactly that column's level.  The diagonal itself is
`diagz_mem_W`.  So `(SUBST)` closes the gap. -/
theorem towerExp2Root_of_subst (hsub : SubstClosed) (hWL : LiftStage) :
    TowerExp2Root := by
  classical
  intro v z m R hR hRne hz1 hd hop hi1 hpM hvw hzy n hn
  set p0 : ℕ × ℕ × ℕ := (0, v, z) with hp0
  set M : TrioSeq := p0 :: R with hMdef
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hMlen : M.length - 1 = R.length := by rw [hMdef]; simp
  have hE : ∀ i, entry M i R.length = entry R i (R.length - 1) :=
    fun i => entry_cons_last hRne i
  have hxpos : 0 < entry R 0 (R.length - 1) :=
    hR _ (entry_pair_mem (B := R) (by omega))
  have hL : M.length - 1 ≠ 0 := by rw [hMlen]; omega
  have hzz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0) := by
    rw [hMlen]; rintro ⟨h1, -, -⟩; rw [hE 0] at h1; omega
  have hsrM : srow M (M.length - 1) = 2 := by
    rw [hMlen, hMdef, srow_cons_last hRne, hi1]
  have hpM' : hasParent M (srow M (M.length - 1)) (M.length - 1) := by
    rw [hsrM, hMlen, hMdef, ← hi1]; exact hpM
  have hpar0 : parent M (srow M (M.length - 1)) (M.length - 1) = 0 := by
    rw [hsrM, hMlen]
    have := parent_cons_eq_zero (v := v) (z := z) hRne hd hpM
    rwa [hi1] at this
  have hroot0 : entry M 0 0 = 0 := by rw [hMdef]; simp [entry, hp0]
  have hroot1 : entry M 1 0 = v := by rw [hMdef]; simp [entry, hp0]
  have hroot2 : entry M 2 0 = z := by rw [hMdef]; simp [entry, hp0]
  set D0 : ℕ := (if 0 < srow M (M.length - 1)
    then entry M 0 (M.length - 1) - entry M 0 0 else 0) with hD0
  set D1 : ℕ := (if 1 < srow M (M.length - 1)
    then entry M 1 (M.length - 1) - entry M 1 0 else 0) with hD1
  have hD0pos : 0 < D0 := by
    rw [hD0, hsrM, if_pos (by omega), hroot0, hMlen, hE 0]; omega
  -- the peel `M.dropLast = p_{v,z}(R.dropLast)` lands in `W (2v+z)`
  set Md : TrioSeq := M.dropLast with hMd
  have hMdcons : Md = p0 :: R.dropLast := by rw [hMd, hMdef, dropLast_cons hRne]
  have hMdlen : 0 < Md.length := by rw [hMdcons]; simp
  have hMdmem : Md ∈ W (2 * v + z) := by
    rcases Nat.lt_or_ge R.length 2 with hsm | hbig
    · have hdl : R.dropLast = [] :=
        List.eq_nil_of_length_eq_zero (by simp; omega)
      rw [hMdcons, hdl]
      exact Om_mem_W v z
    · have h1 := hop 1 le_rfl
      rw [oper_eq_graft_nil_of_domT (n := 1) (by omega) hd, graft_nil] at h1
      rw [hMdcons]
      exact h1 (argOK_dropLast hR) v z (2 * v + z) hz1 le_rfl
  -- the copies
  set B : ℕ → TrioSeq := fun k => shiftr01 (k * D0) 0 (Lift1 Md (k * D1)) with hB
  have hBlen : ∀ k, (B k).length = Md.length := fun k => by
    rw [hB]; exact shiftLift_length Md _ _
  have hBmem : ∀ k, B k ∈ W (2 * (v + k * D1) + z) := by
    intro k
    have h := hWL (2 * v + z) (k * D1) Md hMdmem
    have he : 2 * v + z + 2 * (k * D1) = 2 * (v + k * D1) + z := by omega
    rw [he] at h
    simpa only [hB] using W_shift h (k * D0)
  -- the diagonal host
  set Q : TrioSeq :=
    (List.range n).map (fun k => ((k * D0, v + k * D1, z) : ℕ × ℕ × ℕ)) with hQ
  have hQlen : Q.length = n := by rw [hQ]; simp
  have hQget : ∀ k, k < n → Q.getD k ((0, 0, 0) : ℕ × ℕ × ℕ)
      = ((k * D0, v + k * D1, z) : ℕ × ℕ × ℕ) := by
    intro k hk
    rw [hQ, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by simpa using hk)]
    simp
  have hQent : ∀ k, k < n →
      entry Q 0 k = k * D0 ∧ entry Q 1 k = v + k * D1 ∧ entry Q 2 k = z := by
    intro k hk
    refine ⟨?_, ?_, ?_⟩ <;> · unfold entry; rw [hQget k hk]; simp
  have hQmem : Q ∈ W (2 * v + z) := diagz_mem_W hz1 v D0 D1 hD0pos n
  -- assemble
  have hmain := hsub (2 * v + z) Q B hQmem
    (by
      intro k hk
      have hk1 : k + 1 < n := by rw [← hQlen]; exact hk
      rcases hQent k (by omega) with ⟨e0, -, -⟩
      rcases hQent (k + 1) hk1 with ⟨e0', -, -⟩
      rw [e0, e0']
      have hmul : (k + 1) * D0 = k * D0 + D0 := Nat.succ_mul k D0
      omega)
    (by intro k hk; rw [hBlen k]; exact hMdlen)
    (by
      intro k hk i
      have hk' : k < n := by rw [← hQlen]; exact hk
      have hlt : (0 : ℕ) < Md.length := hMdlen
      rcases hQent k hk' with ⟨e0, e1, e2⟩
      have hM0 : entry Md 0 0 = 0 := by
        rw [hMdcons]; simp [entry, hp0]
      have hM1 : entry Md 1 0 = v := by
        rw [hMdcons]; simp [entry, hp0]
      have hM2 : entry Md 2 0 = z := by
        rw [hMdcons]; simp [entry, hp0]
      simp only [hB]
      rcases Nat.lt_or_ge i 1 with hi0 | hi1'
      · have hii : i = 0 := by omega
        subst hii
        rw [entry0_shiftLift hlt, hM0, e0]
        omega
      · rcases Nat.lt_or_ge i 2 with hia | hib
        · have hii : i = 1 := by omega
          subst hii
          rw [entry1_shiftLift hlt, hM1, e1, if_pos (le1_refl hlt)]
        · rw [entry_ge_two hib, entry_ge_two hib, entry2_shiftLift hlt, hM2, e2])
    (by
      intro k hk j hj1 hjlt
      have hk' : k < n := by rw [← hQlen]; exact hk
      rcases hQent k hk' with ⟨e0, -, -⟩
      rw [hBlen k] at hjlt
      simp only [hB]
      rw [entry0_shiftLift hjlt, e0]
      have hpos : 0 < entry Md 0 j := by
        rw [hMdcons]
        have hMdl : Md.length = R.dropLast.length + 1 := by rw [hMdcons]; simp
        have hjR : j - 1 < R.dropLast.length := by omega
        have : entry (p0 :: R.dropLast) 0 j = entry R.dropLast 0 (j - 1) := by
          conv_lhs => rw [show j = (j - 1) + 1 by omega]
          rw [entry_cons]
        rw [this]
        exact argOK_dropLast hR _ (entry_pair_mem hjR)
      omega)
    (by
      intro k hk
      have hk' : k < n := by rw [← hQlen]; exact hk
      rcases hQent k hk' with ⟨-, e1, e2⟩
      have : lev Q k = 2 * (v + k * D1) + z := by unfold lev; rw [e1, e2]
      rw [this]
      exact hBmem k)
  rw [hQlen] at hmain
  have hgexp : M⟦n⟧ = gexp M 0 (M.length - 1) D0 D1 n :=
    oper_eq_gexp n hL hzz hpM' hpar0
  rw [hgexp]
  unfold gexp
  rw [List.take_zero, List.nil_append,
    gcopies_eq_tower (M := M) (M.length - 1) D0 D1 n (by omega),
    ← List.dropLast_eq_take, ← hMd]
  exact hmain

end TRIO
