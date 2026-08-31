/-
課題 L11: **`TieFree` は「弱められない」**（証明ずみのリフト言語の中では**必要**）。
あわせて `(WL)` が実際に消費される場所を**塔の族だけ**に絞る。

## 1. どこで `TieFree` を使っているか（課題 L11 (1) の答え）

`Wtower2.liftStage_of_tieFree` の証明は 2 行しかない:

    rw [Lift1_eq_mlift_of_tieFree hv h d]     -- ここだけで TieFree を使う
    exact mlift_mem_W X hX

`Lift1_eq_mlift_of_tieFree` は `List.map_congr_left` で
`Lift1 X d = mlift X (v0-1) d` を**列ごと**に示す。`TieFree` はその
`if_neg` の枝、すなわち **`le1 X 0 j` が偽である `j` すべて**で使われる。
`j` の部分集合には絞れない（絞ると 2 つの列が実際に食い違う）。

## 2. 閾値や階段を自由にしても弱まらない（課題 L11 (3) の答え）

`L10Tie.maskMatch_iff_tieFree` は「閾値 `v` を自由にしても `TieFree` と同値」
を示した。ここではさらに**階段 `Stair φ` まで自由にしても同じ**ことを示す:

    SliftMatch X d := ∃ φ, Stair φ ∧ slift X φ = Lift1 X d

`Cgraft.slift` は「証明ずみのリフト法則（`Wslift.slift_mem_W_tight`）が扱える
リフトすべて」であり、`mlift` はその特別な場合である。定理
`sliftMatch_iff_tieFree` は

    (v0 ≥ 1, d ≥ 1)  ⟹  SliftMatch X d  ↔  TieFree X

を与える。⟹ **証明ずみのリフト言語の中では `TieFree` は十分条件であるだけで
なく必要条件**であり、「もっと弱い仮定で `(WL)` を出す」道はこの言語の中には
存在しない。

## 3. `(WL)` が消費されるのは塔の族だけ（課題 L11 (2) の枠）

`Wtower2.towerGraft2_of_liftStage` を読むと `LiftStage` は**ただ 1 行**でしか
使われていない:

    have hmem : Lift1 (M⟦j⟧) d1 ∈ W (2*v+z+2*d1) := hWL _ _ _ ih

`M = (0,v,z) :: R`、`d1 = row1(R[-1]) - v`、`M⟦0⟧ = []`、
`M⟦j+1⟧ = (0,v,z) :: graft R (Lift1 (M⟦j⟧) d1)`。つまり `(WL)` に本当に要るのは
「すべての `X ∈ W m`」ではなく**この族だけ**である（`LiftStageTower`）。

実測（`tools/probe_tiefree_tower.py`）:

    塔の 1 段は TieFree を**完全に保つ**
      本番     26412 サイト x 5 段、TieFree(X_1) ⟺ TieFree(X_j)、**両向き 0 違反**
      陽性対照 リフト量を d1-1 にすると 2398 中 1604 で「後から破れる」
    ⟹ 残るのは**土台 `TieFree ((0,v,z) :: R.dropLast)` だけ**

    ところが土台は 26412 中 7640（29%）で偽。しかも
    `X_1 ∈ W (2v+z)` を課しても消えない（1364 例が「W に入るのにタイあり」）。
    タイの正体は 1284/1364 が「`R` の中に行 1 がちょうど `v` の列がある」。
    `TowerGraft2` は `∀ v z` なので、`v` は `R` の行 1 の値を必ず走る。

⟹ **`(WL)` を証明ずみのリフト言語で出す道は、塔に絞っても閉じている。**
-/
import Wtower2

namespace TRIO
namespace L11

open Wset

/-! ## 1. 証明ずみのリフト言語で `Lift1` が表せること -/

/-- `Lift1 X d` が**証明ずみの**階段リフト（`Cgraft.slift`）で表せる。
`Wslift.slift_mem_W_tight` が扱えるリフトはすべてこの形である。 -/
def SliftMatch (X : TrioSeq) (d : ℕ) : Prop :=
  ∃ φ : ℕ → ℕ, Stair φ ∧ slift X φ = Lift1 X d

/-- **`TieFree` は十分**（既知 `Lift1_eq_mlift_of_tieFree` の言い換え）。 -/
theorem sliftMatch_of_tieFree {X : TrioSeq} {d : ℕ} (hv : 1 ≤ entry X 1 0)
    (h : TieFree X) : SliftMatch X d :=
  ⟨fun m => m + (if entry X 1 0 - 1 < m then d else 0), stair_step _ _,
    (mlift_eq_slift X (entry X 1 0 - 1) d).symm.trans
      (Lift1_eq_mlift_of_tieFree hv h d).symm⟩

/-- **★ `TieFree` は必要でもある。**

根 `0` は自分の行 1 錐に入っている（`le1_refl`）ので、階段は根の `amin`
（= `entry X 1 0`）でちょうど `d` だけ持ち上げねばならない。`Stair.step` は
`φ m - m` の単調性を課すので、`amin` が根以上の列（＝ `coneV` の中）でも
持ち上げ量は `d` 以上になる。したがって `coneV` の中の列は `Lift1` でも
持ち上がる、すなわち `le1` 錐に入る。 -/
theorem tieFree_of_sliftMatch {X : TrioSeq} {d : ℕ} (hpos : 0 < X.length)
    (hd : 1 ≤ d) (hv : 1 ≤ entry X 1 0) (h : SliftMatch X d) : TieFree X := by
  obtain ⟨φ, hφ, heq⟩ := h
  have h0 : entry (slift X φ) 1 0 = entry (Lift1 X d) 1 0 := by rw [heq]
  rw [entry1_slift hpos, entry1_Lift1 hpos, if_pos (le1_refl hpos),
    amin_zero] at h0
  have hstep0 : φ (entry X 1 0) - entry X 1 0 = d := by omega
  intro j hj
  by_contra hnl
  have hjlt : j < X.length := by
    by_contra hge
    have hjj := hj j Relation.ReflTransGen.refl
    rw [entry_out (by omega : X.length ≤ j)] at hjj
    omega
  have hamin : entry X 1 0 ≤ amin X j := by
    have := coneV_iff_amin.mp hj
    omega
  have hs := hφ.step (entry X 1 0) (amin X j) hamin
  have he : entry (slift X φ) 1 j = entry (Lift1 X d) 1 j := by rw [heq]
  rw [entry1_slift hjlt, entry1_Lift1 hjlt, if_neg hnl] at he
  omega

/-- **★★ 証明ずみのリフト言語の中では `TieFree` がちょうどの条件。**
弱めることはできない。 -/
theorem sliftMatch_iff_tieFree {X : TrioSeq} {d : ℕ} (hpos : 0 < X.length)
    (hd : 1 ≤ d) (hv : 1 ≤ entry X 1 0) : SliftMatch X d ↔ TieFree X :=
  ⟨tieFree_of_sliftMatch hpos hd hv, sliftMatch_of_tieFree hv⟩

end L11
end TRIO

#print axioms TRIO.L11.tieFree_of_sliftMatch
#print axioms TRIO.L11.sliftMatch_iff_tieFree
