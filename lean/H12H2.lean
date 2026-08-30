/-
H12H2.lean: L3 の §163 の前提 `h2` を消費側の `Q` について確かめる。

`h2`（`L105Cap.lean:11588`、逐語）:
    `∀ j, j < Q.length → 0 < entry Q 2 j → hasParent (Q.take (j + 1)) 2 j`

⚠ **`j = 0` を入れると、結論 `hasParent _ 2 0` は常に偽**
（`L53.not_hasParent_zero`、`L53Subst.lean:3308`）。
⟹ **`h2` は `entry Q 2 0 = 0` を含意する。**
⟹ **L3 が捨てたはずの旧前提 `entry Q 2 0 = 0` が、`h2` の `j = 0` の場合として復活している。**
⟹ 消費側の `Q = Lift1 ((0,v,z) :: R.dropLast) t` では `entry Q 2 0 = z` なので、
   **`z = 1` では `h2` は偽**。
-/
import L105Cap

namespace TRIO
namespace H12H2

open Wset
open L105

/-- **★ `h2` は旧前提 `entry Q 2 0 = 0` を含意する**（`j = 0` の場合）。 -/
theorem h2_implies_root_row2_zero {Q : TrioSeq} (hQne : Q ≠ [])
    (h2 : ∀ j, j < Q.length → 0 < entry Q 2 j → hasParent (Q.take (j + 1)) 2 j) :
    entry Q 2 0 = 0 := by
  by_contra hc
  exact L53.not_hasParent_zero (Q.take 1) 2
    (h2 0 (List.length_pos_iff.mpr hQne) (by omega))

/-- **⟹ 消費側の `Q = Lift1 ((0,v,z) :: R.dropLast) t` では `h2` は `z = 0` を強制する。** -/
theorem h2_forces_z_zero {v z t : ℕ} {R : TrioSeq}
    (h2 : ∀ j, j < (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t).length →
      0 < entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t) 2 j →
      hasParent ((Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t).take (j + 1)) 2 j) :
    z = 0 := by
  have hne : Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t ≠ [] := by
    intro hc
    have : (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t).length = 0 := by
      rw [hc]; rfl
    rw [Lift1_length] at this
    simp at this
  have hroot := h2_implies_root_row2_zero hne h2
  rw [entry2_Lift1] at hroot
  show z = 0
  have : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 2 0 = z := rfl
  omega


/-! ## 2. ⛔ **`h2` は `j >= 1` に弱めても偽** —— 断片の中の 2 列の反例

`h2` の `j = 0` を外した版

    `h2' : ∀ j, 1 <= j → j < Q.length → 0 < entry Q 2 j → hasParent (Q.take (j+1)) 2 j`

でも救えない。反例:

    **`Q = Lift1 [(0,0,0),(1,0,1)] t = [(0,t,0),(1,0,1)]`**

`Infcex.cexX`（`Infcex.lean:41`）と同じ形だが、**行 2 が 1 なので z<2 断片の中**。

    列 1 は行 2 が 1 > 0。しかし**行 1 が増えない**ので `le1 Q 0 1` が偽
    （`nextrel1` は行 1 の狭義増加を要求）。`nextrel2` は `le1` を要求するので
    **列 1 は行 2 の親を持たない**。
    しかも **`Q ∈ W a`**（末尾列は孤児なので `oper = Pred`、`Aop` の節 2）。

⟹ **`h2` は `hQmem : Q ∈ W a` からも `hQshallow` からも出ない。** -/

/-- 反例の列（`Lift1 [(0,0,0),(1,0,1)] t` に等しい）。 -/
def X (t : ℕ) : TrioSeq := [((0, t, 0) : ℕ × ℕ × ℕ), ((1, 0, 1) : ℕ × ℕ × ℕ)]

/-- 列 1 は行 1 の祖先を持たない（行 1 が増えない）。 -/
theorem not_le1_X (t : ℕ) : ¬ le1 (X t) 0 1 := by
  rintro ⟨-, -, hr⟩
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨b, -, hb⟩
  · exact absurd h (by omega)
  · have hblt : b < 1 := hb.2.2.1
    have hb0 : b = 0 := by omega
    subst hb0
    have hlt : entry (X t) 1 0 < entry (X t) 1 1 := hb.2.2.2.1
    rw [show entry (X t) 1 0 = t from rfl, show entry (X t) 1 1 = 0 from rfl] at hlt
    omega

/-- ⟹ 列 1 は行 2 の親も持たない（`nextrel2` は `le1` を要求する）。 -/
theorem not_hasParent_X (t : ℕ) : ¬ hasParent (X t) 2 1 := by
  rintro ⟨j, hj, -⟩
  unfold nextR at hj
  rw [if_neg (by omega), if_neg (by omega)] at hj
  have hjlt : j < 1 := hj.2.2.1
  have hj0 : j = 0 := by omega
  subst hj0
  exact not_le1_X t hj.2.2.2.2.1

/-- **★ 反例は `Lift1 ((0,v,z) :: R.dropLast) t` の形をしている**
（`v = 0`, `z = 0`, `R.dropLast = [(1,0,1)]`）。 -/
theorem lift_X (t : ℕ) :
    Lift1 (((0, (0 : ℕ), (0 : ℕ)) : ℕ × ℕ × ℕ) :: [((1, 0, 1) : ℕ × ℕ × ℕ)]) t
      = X t := by
  have hle0 : le1 (X 0) 0 0 :=
    ⟨by simp [X], by simp [X], Relation.ReflTransGen.refl⟩
  have hle1 : ¬ le1 (X 0) 0 1 := not_le1_X 0
  show Lift1 (X 0) t = X t
  unfold Lift1
  rw [show (X 0).length = 2 from rfl, show List.range 2 = [0, 1] from rfl]
  simp only [List.map_cons, List.map_nil, if_pos hle0, if_neg hle1]
  rw [show entry (X 0) 0 0 = 0 from rfl, show entry (X 0) 1 0 = 0 from rfl,
    show entry (X 0) 2 0 = 0 from rfl, show entry (X 0) 0 1 = 1 from rfl,
    show entry (X 0) 1 1 = 0 from rfl, show entry (X 0) 2 1 = 1 from rfl,
    Nat.zero_add]
  rfl

/-- **★ 反例は本当に `W a` の中にいる**（`hQmem` を満たす）。 -/
theorem X_mem_W {a t : ℕ} (ha : 2 * t ≤ a) : X t ∈ W a := by
  have hsingle : [((0, t, (0 : ℕ)) : ℕ × ℕ × ℕ)] ∈ W a :=
    W_mono (show 2 * t + 0 ≤ a by omega) (Om_mem_W t 0)
  have hsrow : srow (X t) ((X t).length - 1) = 2 := by
    show srow (X t) 1 = 2
    unfold srow
    rw [if_pos (show 0 < entry (X t) 2 1 from by
      rw [show entry (X t) 2 1 = 1 from rfl]; omega)]
  have hnp : ¬ hasParent (X t) (srow (X t) ((X t).length - 1))
      ((X t).length - 1) := by
    rw [hsrow, show (X t).length - 1 = 1 from rfl]
    exact not_hasParent_X t
  refine A1_intro (Or.inr (Or.inl (fun n _ => ?_)))
  have hL : (X t).length - 1 ≠ 0 := by
    rw [show (X t).length - 1 = 1 from rfl]; omega
  have hz : ¬ (entry (X t) 0 ((X t).length - 1) = 0 ∧
      entry (X t) 1 ((X t).length - 1) = 0 ∧
      entry (X t) 2 ((X t).length - 1) = 0) := by
    rw [show (X t).length - 1 = 1 from rfl, show entry (X t) 0 1 = 1 from rfl]
    rintro ⟨h0, -, -⟩
    omega
  rw [oper_eq_pred_of_noParent n hL hz hnp]
  unfold Pred
  rw [if_neg (show ¬ (X t).length ≤ 1 from by
    rw [show (X t).length = 2 from rfl]; omega)]
  rw [show (X t).dropLast = [((0, t, (0 : ℕ)) : ℕ × ℕ × ℕ)] from rfl]
  exact hsingle

/-- ⛔ **`h2` を `1 <= j` に弱めても偽。** -/
theorem h2_prime_false (t : ℕ) :
    ¬ (∀ j, 1 ≤ j → j < (X t).length → 0 < entry (X t) 2 j →
        hasParent ((X t).take (j + 1)) 2 j) := by
  intro h
  have hx := h 1 (by omega)
    (show (1 : ℕ) < (X t).length from by rw [show (X t).length = 2 from rfl]; omega)
    (show 0 < entry (X t) 2 1 from by rw [show entry (X t) 2 1 = 1 from rfl]; omega)
  rw [show (X t).take (1 + 1) = X t from rfl] at hx
  exact not_hasParent_X t hx

/-- ⛔ **`h2`（`L105Cap.lean:11588`）は `hQmem : Q ∈ W a` と根の浅さからは出ない。**
`Q = X t` は `W a` の中にあり、根が狭義最浅で、しかも `h2`（弱めた版でも）を満たさない。 -/
theorem h2_not_derivable :
    ∃ Q : TrioSeq, (∀ a, 2 * 0 ≤ a → Q ∈ W a) ∧
      (∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) ∧
      ¬ (∀ j, 1 ≤ j → j < Q.length → 0 < entry Q 2 j →
          hasParent (Q.take (j + 1)) 2 j) := by
  refine ⟨X 0, fun a ha => X_mem_W ha, ?_, h2_prime_false 0⟩
  intro l hl0 hll
  rw [show (X 0).length = 2 from rfl] at hll
  have : l = 1 := by omega
  subst this
  rw [show entry (X 0) 0 0 = 0 from rfl, show entry (X 0) 0 1 = 1 from rfl]
  omega


/-! ## 3. ★ **`h2` の残差はちょうど 2 つ** —— 根（`z=1`）と、行 1 の錐の外の列

§248.3 の反例は**錐の外の列**だった。錐の中に限れば `h2` は**既存の緑の補題から無料**:

    `Wset.hasParent_two_of`（`Wset.lean:1858`）
      `b < |M|` → `k < b` → `le1 M k b` → `entry M 2 k < entry M 2 b` → `hasParent M 2 b`

を `M = Q.take (j+1)`, `k = 0`, `b = j` で使うだけ。

⟹ **`h2` を消費側で満たせない原因は、ちょうど次の 2 つに限られる:**

    (i)  **`j = 0`（根）** … `entry Q 2 0 = z`。`z = 1` なら即座に偽
    (ii) **錐の外の行 2 正の列** … `¬ le1 Q 0 j`（ブロッカーの向こう側）

これは `L105Cap.lean` §79.1 が既に書いている「孤児の条件」と同じもの。
⟹ **`h2` は新しい前提ではなく、`hnb`（ブロッカーなし）＋ `z = 0` の言い換え。** -/

/-- ★ **錐の中の列では `h2` は無料**（`hasParent_two_of` そのもの）。 -/
theorem h2_cone {Q : TrioSeq} (hz0 : entry Q 2 0 = 0) :
    ∀ j, 1 ≤ j → j < Q.length → 0 < entry Q 2 j → le1 Q 0 j →
      hasParent (Q.take (j + 1)) 2 j := by
  intro j hj1 hjl hpos hcone
  have hlen : (Q.take (j + 1)).length = j + 1 := by
    rw [List.length_take]; omega
  refine hasParent_two_of (M := Q.take (j + 1)) (b := j) (k := 0)
    (show j < (Q.take (j + 1)).length from by rw [hlen]; omega) (by omega) ?_ ?_
  · exact (le1_take (by omega) (by omega)).mpr hcone
  · rw [entry_take (by omega), entry_take (by omega), hz0]
    omega

/-- ★★ **⟹ `h2` の残差はちょうど「根」と「錐の外」だけ。**
`entry Q 2 0 = 0`（＝ `z = 0`）と「行 2 が正なら錐の中」があれば `h2` は成り立つ。 -/
theorem h2_of_cone {Q : TrioSeq} (hz0 : entry Q 2 0 = 0)
    (hcone : ∀ j, 1 ≤ j → j < Q.length → 0 < entry Q 2 j → le1 Q 0 j) :
    ∀ j, j < Q.length → 0 < entry Q 2 j → hasParent (Q.take (j + 1)) 2 j := by
  intro j hjl hpos
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · exact absurd hz0 (by omega)
  · exact h2_cone hz0 j hj1 hjl hpos (hcone j hj1 hjl hpos)


/-! ## 4. ★★★ **⟹ `h2` は前提から丸ごと消せる** —— `entry Q 2 0 = 0` 1 本で足りる

`L105Cap.lean` の `mTowerClosed_of_snocStepCone`（現行版）の証明本体を読むと、
**`h2` が使われるのはただ 1 か所**:

    refine hstep n j hj (fun hj1 hcone => ?_) hC
    have hloc := block_blockParent_all_cone hj hj1 hr0 hcone (h2 j hj1 hj)
                                                    ^^^^^ ここで `hcone : le1 Q 0 j` が
                                                          すでにスコープにいる

⟹ **`h2` は「錐の中の `j`」でしか呼ばれない。** そして §3 の `h2_cone` により
錐の中では `entry Q 2 0 = 0` だけで `h2` の結論が出る。

⟹ **`h2` を `hz0 : entry Q 2 0 = 0` に置き換えられる**（＝ 消費側では `z = 0`）。
以下は `L105Cap` の証明本体をそのまま写して `h2` を `hz0` に差し替えたもの。 -/

open Classical in
/-- ★★★ **`h2` なし版**: 前提は `hr0` と **`entry Q 2 0 = 0`** と `hstep` だけ。 -/
theorem mTowerClosed_of_snocStepCone' {u : ℕ} {Q : TrioSeq} {d e : ℕ}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hz0 : entry Q 2 0 = 0)
    (hstep : ∀ (n j : ℕ), j < Q.length →
      (0 < j → le1 Q 0 j → n * Q.length ≤
        parent (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
          (srow (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
            (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length)
          (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length) →
      mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j ∈ W u →
      mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1) ∈ W u) :
    ∀ n, mTower Q d e n ∈ W u := by
  refine mTowerClosed_of_snocStepPar ?_
  intro n j hj _ hC
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
  refine hstep n j hj (fun hj1 hcone => ?_) hC
  -- ★ ここが唯一の差分: `h2 j hj1 hj` を `h2_cone` で作る（`hcone` が使える）
  have hloc : hasParent (B.take (j + 1)) (srow (B.take (j + 1)) j) j :=
    block_blockParent_all_cone hj hj1 hr0 hcone
      (fun hpos => h2_cone hz0 j hj1 hj hpos hcone)
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


/-! ## 5. ★★★ **⟹ `hz0` も消費側で無料になる** —— `zle1 R` を足せば

§250 で前提は `hr0` / `hz0` / `hstep` の 3 本になった。`hz0` は消費側では
`z = 0`（`entry Q 2 0 = z`）。⟹ **`z = 1` の枝さえ潰せば `hz0` は無料。**

そして**それは既に緑**:

    `L105Cap.tower2_z_zero_of_zle1`（`L105Cap.lean:3813`）
      `R ≠ []` → `z ≤ 1` → **`zle1 R`** → `domT R m` → `srow R (|R|-1) = 2`
      → `hasParent ((0,v,z)::R) (srow R (|R|-1)) |R|` → **`z = 0`**

⚠ **`zle1 R`（`Wset.lean:2470`: ∀p∈M, p.2.2 ≤ 1）はこのプロジェクトの断片条件そのもの**
（`Wset.mem_Wstar`（`Wset.lean:4646`）が `zle1 R` を入力に取る）。
L3 は既に `TowerExpBigZ`（`L105Cap.lean:3831`）で「`zle1 R` を足した版」を作っている。

⟹ **`LiftTowerExp2` にも `zle1 R` を足せば、`hz0` は下の 1 本で出る。** -/

/-- ★★★ **`zle1 R` があれば消費側の `hz0` は無料**。
`Q = Lift1 ((0,v,z) :: R.dropLast) t` の行 2 の根は `z`、そして `z = 0`。 -/
theorem hz0_of_zle1 {v z t m : ℕ} {R : TrioSeq} (hRne : R ≠ []) (hz1 : z ≤ 1)
    (hz : zle1 R) (hd : domT R m) (hi2 : srow R (R.length - 1) = 2)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t) 2 0 = 0 := by
  have hzz : z = 0 := tower2_z_zero_of_zle1 hRne hz1 hz hd hi2 hpM
  rw [entry2_Lift1]
  show entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 2 0 = 0
  have : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 2 0 = z := rfl
  omega

/-- ★★★★ **⟹ まとめ**: `zle1 R` を足せば `mTowerClosed_of_snocStepCone` の
前提は **`hr0` と `hstep` の 2 本だけ**になる（`h2` も `hz0` も消える）。 -/
theorem mTowerClosed_of_snocStepCone_zle1 {u : ℕ} {v z t m d e : ℕ} {R : TrioSeq}
    (hRne : R ≠ []) (hz1 : z ≤ 1) (hz : zle1 R) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length)
    (hr0 : ∀ l, 0 < l → l < (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t).length →
      entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t) 0 0
        < entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t) 0 l)
    (hstep : ∀ (n j : ℕ),
      j < (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t).length →
      (0 < j → le1 (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t) 0 j →
        n * (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t).length ≤
        parent (mTower (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t) d e n
            ++ (Lift1 (shiftr01 (d * n) 0
              (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t)) (e * n)).take (j + 1))
          (srow (mTower (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t) d e n
            ++ (Lift1 (shiftr01 (d * n) 0
              (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t)) (e * n)).take (j + 1))
            (mTower (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t) d e n
              ++ (Lift1 (shiftr01 (d * n) 0
                (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t)) (e * n)).take j).length)
          (mTower (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t) d e n
            ++ (Lift1 (shiftr01 (d * n) 0
              (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t)) (e * n)).take j).length) →
      mTower (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t) d e n
        ++ (Lift1 (shiftr01 (d * n) 0
          (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t)) (e * n)).take j ∈ W u →
      mTower (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t) d e n
        ++ (Lift1 (shiftr01 (d * n) 0
          (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t)) (e * n)).take (j + 1) ∈ W u) :
    ∀ n, mTower (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t) d e n ∈ W u :=
  mTowerClosed_of_snocStepCone' hr0 (hz0_of_zle1 hRne hz1 hz hd hi2 hpM) hstep


/-! ## 6. ★★★★ **F2a の一般化** —— 末尾列でなくてよい

`L105Cap.mTower_orphan_row2`（`L105Cap.lean:8048`、「F2a」）は
**`Q` の末尾列**（位置 `|Q| - 1`）にしか当たらない。
ところが `hstep` が要るのは **任意の `j`** の位置（§252.3）。
実測では `|R|=4` で**破れる列の 8 割が内側**なので、F2a だけでは届かない。

⚠ ところが道具は既に一般だった:

    `L105Cap.le1_mTower_in_block`（`L105Cap.lean:8026`）… **`q` は任意**（`hq`, `hq1`）
    `L105Cap.nextrel2_lastBlock_absurd`（`L105Cap.lean:7836`）… **`b` は任意**

⟹ **F2a は「`q := |Q| - 1` に固定した特殊化」だった。**一般化は下のとおり
（`L105Cap` の証明本体をそのまま写して `M.dropLast.length - 1` を `q` にしただけ）。 -/

open Classical in
/-- ★★★★ **F2a の一般化**: `Q` の**任意の**列 `q` が「錐の外 ∧ 行 2 の孤児」なら、
塔のその位置でも行 2 の孤児。（元の `mTower_orphan_row2` は `q = |Q| - 1` の場合。） -/
theorem mTower_orphan_row2_gen {M : TrioSeq} {d e n' q : ℕ} (hM2 : 2 ≤ M.length)
    (hd1pos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hQ2 : 2 ≤ M.dropLast.length)
    (hq : q < M.dropLast.length) (hq1 : 0 < q)
    (hout : ¬ le1 M 0 (0 + q))
    (horph : ¬ hasParent M.dropLast 2 q) :
    ¬ hasParent (mTower M.dropLast d e (n' + 1)) 2
      ((mTower M.dropLast d e n').length + q) := by
  have hLb : 0 < M.dropLast.length := by omega
  have hAlen : (mTower M.dropLast d e n').length = n' * M.dropLast.length := by
    rw [mTower_length]
  rintro ⟨a, ha, -⟩
  have hnr : nextrel2 (mTower M.dropLast d e (n' + 1)) a
      ((mTower M.dropLast d e n').length + q) := by
    unfold nextR at ha
    rw [if_neg (by omega), if_neg (by omega)] at ha
    exact ha
  have hge : n' * M.dropLast.length ≤ a := by
    have h := le1_mTower_in_block (n := n' + 1) (k := n') hM2 hd1pos hd0e hr0 hlp
      (by omega) hq hq1 hout a ?_
    · exact h
    · rw [hAlen] at hnr
      exact hnr.2.2.2.2.1.2.2
  have halt : a < (mTower M.dropLast d e n').length + q := hnr.2.2.1
  obtain ⟨qa, hqa⟩ : ∃ qa, a = (mTower M.dropLast d e n').length + qa :=
    ⟨a - n' * M.dropLast.length, by omega⟩
  subst hqa
  rw [mTower_succ] at hnr
  exact nextrel2_lastBlock_absurd horph hnr

/-- ⟹ 元の `mTower_orphan_row2` は上の `q := |M.dropLast| - 1` の場合。 -/
theorem mTower_orphan_row2_of_gen {M : TrioSeq} {d e n' : ℕ} (hM2 : 2 ≤ M.length)
    (hd1pos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hQ2 : 2 ≤ M.dropLast.length)
    (hout : ¬ le1 M 0 (0 + (M.dropLast.length - 1)))
    (horph : ¬ hasParent M.dropLast 2 (M.dropLast.length - 1)) :
    ¬ hasParent (mTower M.dropLast d e (n' + 1)) 2
      ((mTower M.dropLast d e n').length + (M.dropLast.length - 1)) :=
  mTower_orphan_row2_gen hM2 hd1pos hd0e hr0 hlp hQ2 (by omega) (by omega) hout horph


/-! ## 7. **位置合わせ** —— `hstep` の主語は塔の接頭辞

`hstep` の主語は `mTower Q d e n ++ B.take (j+1)`（`B = Lift1 (shiftr01 (d*n) 0 Q) (e*n)`）。
`mTower_succ` により `mTower Q d e (n+1) = mTower Q d e n ++ B` なので、

    `mTower Q d e n ++ B.take (j+1) = (mTower Q d e (n+1)).take (n*|Q| + (j+1))`

⟹ **`hstep` の主語は塔の接頭辞**。そして `hasParent` は接頭辞と行き来する。 -/

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


/-! ## 8. ★★★★★ **(C2) の枝が組み上がった** —— 錐の外の列で `hstep` は無料

§253 の `mTower_orphan_row2_gen`（任意の `j`）＋ §7 の位置合わせ ＋
`L105Cap.snoc_orphan_W`（`L105Cap.lean:144`）を繋ぐ。 -/

open Classical in
/-- ★★★★★ **錐の外の 行 2 正の列では `hstep` は無料**（`W u` に自動で入る）。 -/
theorem snocStep_outOfCone {u : ℕ} {M : TrioSeq} {d e n j : ℕ}
    (hM2 : 2 ≤ M.length) (hd1pos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hQ2 : 2 ≤ M.dropLast.length)
    (hj : j < M.dropLast.length) (hj1 : 0 < j)
    (hout : ¬ le1 M 0 (0 + j))
    (horph : ¬ hasParent M.dropLast 2 j)
    (hpos : 0 < entry M.dropLast 2 j)
    (hC : mTower M.dropLast d e n
      ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j ∈ W u)
    (hCne : mTower M.dropLast d e n
      ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j ≠ []) :
    mTower M.dropLast d e n
      ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1) ∈ W u := by
  have hBlen : (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).length
      = M.dropLast.length := by rw [Lift1_length, shiftr01_length]
  have hTlen : (mTower M.dropLast d e n).length = n * M.dropLast.length :=
    mTower_length M.dropLast d e n
  have hjB : j < (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).length := by
    rw [hBlen]; omega
  have hsplit : (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)
      = (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j
        ++ [(Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n))[j]'hjB] :=
    List.take_succ_eq_append_getElem hjB
  have hCl : (mTower M.dropLast d e n
      ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length
      = n * M.dropLast.length + j := by
    rw [List.length_append, hTlen, List.length_take, hBlen,
      Nat.min_eq_left (by omega)]
  -- ★ 行 2 が正 ⟹ `srow = 2`
  have hpos' : 0 < entry (mTower M.dropLast d e n
      ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)) 2
      (n * M.dropLast.length + j) := by
    rw [show n * M.dropLast.length + j = (mTower M.dropLast d e n).length + j from by
        rw [hTlen],
      entry_append_right, entry_take (by omega), entry2_Lift1, entry2_shiftr01]
    exact hpos
  have hsrow2 : srow (mTower M.dropLast d e n
      ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
      (n * M.dropLast.length + j) = 2 := by
    unfold srow; rw [if_pos hpos']
  -- ★ 塔でも孤児（§253 の一般化 ＋ §7 の位置合わせ）
  have horph2 : ¬ hasParent (mTower M.dropLast d e n
      ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)) 2
      (n * M.dropLast.length + j) := by
    rw [mTower_append_take,
      hasParent_two_take (by rw [mTower_length, Nat.succ_mul]; omega)
        (show n * M.dropLast.length + j < n * M.dropLast.length + (j + 1) from by omega)]
    have := mTower_orphan_row2_gen (n' := n) hM2 hd1pos hd0e hr0 hlp hQ2 hj hj1
      hout horph
    rwa [hTlen] at this
  -- ★ 孤児 snoc は無料
  rw [hsplit, ← List.append_assoc]
  refine snoc_orphan_W _ hC hCne ?_
  rw [List.append_assoc, ← hsplit, hCl, hsrow2]
  exact horph2


/-! ## 9. ★★ **(a)(b) `hlp` / `hd1pos` / `hd0e` は `hpM` と `hr0` から出る**

§254.3 の予想を証明する。`snocStep_outOfCone` の前提のうち

    `hlp : le1 M 0 (0 + |M.dropLast|)`
    `hd1pos : 0 < e`
    `hd0e : entry M 0 (0 + |M.dropLast|) = entry M 0 0 + d`

の 3 本は、**消費側が既に持っている `hpM`（悪根が根）と `hr0`（根が狭義最浅）から出る**。
`d`, `e` は `L105Cap.oper_eq_mTower`（`L105Cap.lean:5228`）の定義そのもの（`srow = 2` の枝）。 -/

/-- ★ `srow = 2` かつ悪根が根なら、**末尾列は根の行 1 錐の中**で、
しかも**行 1 は狭義に増える**。 -/
theorem lp_and_row1_lt_of_hpM {M : TrioSeq} (hM2 : 2 ≤ M.length)
    (hi2 : srow M (M.length - 1) = 2)
    (hpM : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hj0 : parent M (srow M (M.length - 1)) (M.length - 1) = 0) :
    le1 M 0 (M.length - 1) ∧ entry M 1 0 < entry M 1 (M.length - 1) := by
  have hnr := parent_nextR hpM
  rw [hj0, hi2] at hnr
  have h2 : nextrel2 M 0 (M.length - 1) := by
    unfold nextR at hnr
    rw [if_neg (by omega), if_neg (by omega)] at hnr
    exact hnr
  have hle : le1 M 0 (M.length - 1) := h2.2.2.2.2.1
  exact ⟨hle, le1_entry1_lt hle (by omega)⟩

/-- ⟹ **`hlp` は無料**（`0 + |M.dropLast| = |M| - 1`）。 -/
theorem hlp_of_hpM {M : TrioSeq} (hM2 : 2 ≤ M.length)
    (hi2 : srow M (M.length - 1) = 2)
    (hpM : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hj0 : parent M (srow M (M.length - 1)) (M.length - 1) = 0) :
    le1 M 0 (0 + M.dropLast.length) := by
  rw [Nat.zero_add, List.length_dropLast]
  exact (lp_and_row1_lt_of_hpM hM2 hi2 hpM hj0).1

/-- ⟹ **`hd1pos : 0 < e` は無料**（`e` は `oper_eq_mTower` の `srow = 2` の枝）。 -/
theorem hd1pos_of_hpM {M : TrioSeq} (hM2 : 2 ≤ M.length)
    (hi2 : srow M (M.length - 1) = 2)
    (hpM : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hj0 : parent M (srow M (M.length - 1)) (M.length - 1) = 0) :
    0 < (if 1 < srow M (M.length - 1) then
          entry M 1 (M.length - 1) - entry M 1 0 else 0) := by
  rw [hi2, if_pos (by omega)]
  have := (lp_and_row1_lt_of_hpM hM2 hi2 hpM hj0).2
  omega

/-- ⟹ **`hd0e` は `hr0` から無料**（`d` は `oper_eq_mTower` の `srow = 2` の枝）。 -/
theorem hd0e_of_hr0 {M : TrioSeq} (hM2 : 2 ≤ M.length)
    (hi2 : srow M (M.length - 1) = 2)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l) :
    entry M 0 (0 + M.dropLast.length) = entry M 0 0
      + (if 0 < srow M (M.length - 1) then
          entry M 0 (M.length - 1) - entry M 0 0 else 0) := by
  rw [hi2, if_pos (by omega), Nat.zero_add, List.length_dropLast]
  have := hr0 (M.length - 1) (by omega) (by omega)
  omega


/-! ## 10. ★★★★★★ **まとめ**: (C2) の枝は**消費側の前提だけ**で閉じる

`d`, `e` は `L105Cap.oper_eq_mTower`（`L105Cap.lean:5228`）が出す値そのもの。 -/

/-- `oper_eq_mTower` の `d`（行 0 のずれ）。 -/
def dOf (M : TrioSeq) : ℕ :=
  if 0 < srow M (M.length - 1) then entry M 0 (M.length - 1) - entry M 0 0 else 0

/-- `oper_eq_mTower` の `e`（行 1 のずれ）。 -/
def eOf (M : TrioSeq) : ℕ :=
  if 1 < srow M (M.length - 1) then entry M 1 (M.length - 1) - entry M 1 0 else 0

open Classical in
/-- ★★★★★★ **(C2) の枝は消費側の前提だけで閉じる。**
補助的な `hlp` / `hd1pos` / `hd0e` は `hpM` と `hr0` から出るので、
残るのは **`hout`（錐の外）・`horph`（`Q` で孤児）・`hpos`（行 2 が正）** の
「その列の性質」3 本だけ。 -/
theorem snocStep_outOfCone_consumer {u : ℕ} {M : TrioSeq} {n j : ℕ}
    (hM2 : 2 ≤ M.length)
    (hi2 : srow M (M.length - 1) = 2)
    (hpM : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hj0 : parent M (srow M (M.length - 1)) (M.length - 1) = 0)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hQ2 : 2 ≤ M.dropLast.length)
    (hj : j < M.dropLast.length) (hj1 : 0 < j)
    (hout : ¬ le1 M 0 (0 + j))
    (horph : ¬ hasParent M.dropLast 2 j)
    (hpos : 0 < entry M.dropLast 2 j)
    (hC : mTower M.dropLast (dOf M) (eOf M) n
      ++ (Lift1 (shiftr01 (dOf M * n) 0 M.dropLast) (eOf M * n)).take j ∈ W u)
    (hCne : mTower M.dropLast (dOf M) (eOf M) n
      ++ (Lift1 (shiftr01 (dOf M * n) 0 M.dropLast) (eOf M * n)).take j ≠ []) :
    mTower M.dropLast (dOf M) (eOf M) n
      ++ (Lift1 (shiftr01 (dOf M * n) 0 M.dropLast) (eOf M * n)).take (j + 1) ∈ W u :=
  snocStep_outOfCone hM2
    (hd1pos_of_hpM hM2 hi2 hpM hj0)
    (hd0e_of_hr0 hM2 hi2 hr0)
    hr0 (hlp_of_hpM hM2 hi2 hpM hj0) hQ2 hj hj1 hout horph hpos hC hCne


/-! ## 11. ⚠⚠ **自己訂正**: §254/§255 の `snocStep_outOfCone` は**核には要らない**

`L105Cap.mTowerClosed_of_snocStepPar`（`L105Cap.lean:10040`）の**中身**を読み直した:

    by_cases hP : hasParent … 
    · exact hstep n j hj (Or.inl hP) hC
    · rw [hsplit]
      exact snoc_orphan_W _ hC hE (by rw [← hsplit]; exact hP)   ← **孤児はここで消える**

⟹ **孤児の列は `hstep` に届かない。`snocStepPar` が内部で `snoc_orphan_W` で片づけている。**
L3 も §139.1 に「§137 の 5 つの前提は場合分けにすれば要りませんでした」と書いている。

⚠ **ところが `mTowerClosed_of_snocStepCone` はその情報を捨てている**:

    refine mTowerClosed_of_snocStepPar ?_
    intro n j hj _ hC        ← **`_` が「親がある ∨ 空」。捨てられている**

⟹ **捨てずに `hstep` に渡せば、錐の外の孤児の枝は `hstep` の義務から消える。**
⟹ **残る本当の残差は「錐の外 ∧ しかし親を持つ」列だけ。**

> **⟹ §254/§255 の `snocStep_outOfCone` は「既に無料だったもの」を証明していた。**
> **定理としては正しいが、核を減らす役には立たない。正直に記録する。**
> （`mTower_orphan_row2_gen`（§253）は F2a の一般化として独立に残る。） -/

open Classical in
/-- ★★★ **`hstep` に「親がある ∨ 空」を渡す版**（`mTowerClosed_of_snocStepCone` は
これを捨てている）。⟹ **錐の外の孤児は `hstep` の義務から消える。** -/
theorem mTowerClosed_of_snocStepConePar {u : ℕ} {Q : TrioSeq} {d e : ℕ}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hz0 : entry Q 2 0 = 0)
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
      (fun hpos => h2_cone hz0 j hj1 hj hpos hcone)
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


/-! ## 12. ★★★★★★ **(e) は消える** —— 錐の外の列の親は、必ず同じブロック

§256.2 で残った本当の残差は **(e)「錐の外 ∧ しかし親を持つ」**だった。
答えは `mTower_orphan_row2_gen` の証明の中に**既に入っていた**:

    `L105Cap.le1_mTower_in_block`（`L105Cap.lean:8026`）
      錐の外（`¬ le1 M 0 q`）の列の**行 1 の祖先は同じブロックから出ない**:
      `∀ a, ReflTransGen (nextrel1 (mTower …)) a (k*|Q| + q) → k*|Q| ≤ a`

そして `nextrel2` は `le1` を要求する（§248 の要点）。
⟹ **行 2 の親も前のブロックからは来られない。**

> ⟹ **(e) の親は必ず同じブロック ⟹ 窓 < |Q| ⟹ (C1) と同じ測度の議論が効く。**
> ⟹ **「前のブロックからの復活」は起きない。第 3 の枝は消える。**

実測（`h91.py`）: **復活 0 / 18798**（`|R| ∈ {2,3,4}`、`n ∈ {1,2,3}`）。
内訳は「親なし」18654 件、「親は同じブロック」144 件、「前のブロック」**0 件**。 -/

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


/-! ## 13. ★★★★★★★ **(f) `hstep` から `le1 Q 0 j` を落とす**

§257.3 で「親があるなら、錐の中でも外でも親は同じブロック」が出た。
⟹ `hstep` の窓の前提から **`le1 Q 0 j` を外せる**。

必要なのは `parent` の接頭辞不変性（`hasParent_two_take` の `parent` 版）。 -/

/-- `parent`（行 2）は接頭辞と一致する。 -/
theorem parent_two_take {M : TrioSeq} {l p : ℕ} (hl : l ≤ M.length) (hp : p < l)
    (h : hasParent M 2 p) :
    parent (M.take l) 2 p = parent M 2 p := by
  have hnR : ∀ (N : TrioSeq) (j : ℕ), nextR N 2 j p ↔ nextrel2 N j p := by
    intro N j; unfold nextR; rw [if_neg (by omega), if_neg (by omega)]
  have ht : hasParent (M.take l) 2 p := (hasParent_two_take hl hp).mpr h
  refine ht.unique (parent_nextR ht) ?_
  exact (hnR _ _).mpr ((nextrel2_take_iff hl hp).mpr ((hnR M _).mp (parent_nextR h)))

open Classical in
/-- ★★★★★★★ **錐の外の 行 2 正の列でも、親が居るなら窓は `< |Q|`。**
（＝ `hstep` の窓の前提は `le1 Q 0 j` を要らない。） -/
theorem window_of_outOfCone {M : TrioSeq} {d e n j : ℕ}
    (hM2 : 2 ≤ M.length) (hd1pos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hj : j < M.dropLast.length) (hj1 : 0 < j)
    (hout : ¬ le1 M 0 (0 + j))
    (hpos : 0 < entry M.dropLast 2 j)
    (hpar0 : hasParent (mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
      (srow (mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
        (mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length)
      (mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length) :
    n * M.dropLast.length
      ≤ parent (mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
        (srow (mTower M.dropLast d e n
            ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
          (mTower M.dropLast d e n
            ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length)
        (mTower M.dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length := by
  have hBlen : (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).length
      = M.dropLast.length := by rw [Lift1_length, shiftr01_length]
  have hTlen : (mTower M.dropLast d e n).length = n * M.dropLast.length :=
    mTower_length M.dropLast d e n
  have hCl : (mTower M.dropLast d e n
      ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length
      = n * M.dropLast.length + j := by
    rw [List.length_append, hTlen, List.length_take, hBlen,
      Nat.min_eq_left (by omega)]
  -- 行 2 が正 ⟹ `srow = 2`
  have hpos' : 0 < entry (mTower M.dropLast d e n
      ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)) 2
      (n * M.dropLast.length + j) := by
    rw [show n * M.dropLast.length + j = (mTower M.dropLast d e n).length + j from by
        rw [hTlen],
      entry_append_right, entry_take (by omega), entry2_Lift1, entry2_shiftr01]
    exact hpos
  have hsrow2 : srow (mTower M.dropLast d e n
      ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
      (n * M.dropLast.length + j) = 2 := by
    unfold srow; rw [if_pos hpos']
  rw [hCl, hsrow2] at hpar0 ⊢
  -- 塔の接頭辞に直す
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


/-! ## 14. **(g) 行 1 の列も同じ** —— `le1_mTower_in_block` が直接効く

`le1_mTower_in_block` の結論は `ReflTransGen (nextrel1 …)` についてなので、
**`nextrel1` 1 歩は `ReflTransGen.single` でそのまま入る**。
⟹ 行 1 の親も前のブロックからは来られない。

⚠ **行 0（`srow = 0`）は別**: `nextrel0` は `le1` を要求しないので、
この議論は効かない。**未解決のまま残す。** -/

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


/-! ## 15. ★★★★★★★ **行 0 も閉じる** —— ブロックの根が「行 0 の壁」になる

`srow = 0` の列は `nextrel0` の親を探す。`nextrel0` は `le1` を要求しないので
§257/§258 の議論は効かない。**が、別の理由で閉じる。**

    `nextrel0 T j0 j1` の最小性: **`j0` と `j1` の間の列は全部 `j1` 以上の深さ**

ところが第 `n` ブロックの**根**は位置 `n*|Q|` にあり、深さは `entry Q 0 0 + d*n`。
`hr0`（根が狭義に最浅）より `entry Q 0 0 < entry Q 0 j`（`0 < j`）なので、
**ブロックの根は目標の列より狭義に浅い**。

⟹ 前のブロックに親があるとすると、その間にあるブロックの根が最小性を破る。
⟹ **行 0 の親も同じブロック。**

⚠ **この議論は `hout`（錐の外）を使わない** ⟹ **全ての `j > 0` で成り立つ。** -/

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


/-! ## 16. **行 1 の接頭辞移送と窓** —— 行 2 版（§7・§258.1）の写し

`nextrel1` は `le0` を使うので **`Wset.le0_take`（`Wset.lean:851`）**と
**`L105Cap.le0_le'`（`:931`）**を使う。形は行 2 版と同じ。 -/

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


/-! ## 17. ★★★★★★★★ **(h) 3 行を 1 本に** —— `hstep` の窓の前提から `le1` が落ちる -/

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


/-! ## 18. ★★★★★★★★ **核の最終形**: `hstep` から `le1` が消える

    錐の中 … L3 の `block_blockParent_all_cone` ＋ `snocStep_parent_sameBlock`
    錐の外 … §17 の `window_of_outOfCone_all`

⟹ **`hstep` の窓の前提は `0 < j → 窓 < |Q|` の 1 本**（`le1 Q 0 j` は不要）。 -/

open Classical in
/-- ★★★★★★★★ **核の最終形**: `hstep` の窓の前提から **`le1` が消える**。 -/
theorem mTowerClosed_of_snocStepNoCone {u : ℕ} {M : TrioSeq} {d e : ℕ}
    (hM2 : 2 ≤ M.length) (hd1pos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0M : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hr0 : ∀ l, 0 < l → l < M.dropLast.length →
      entry M.dropLast 0 0 < entry M.dropLast 0 l)
    (hz0 : entry M.dropLast 2 0 = 0)
    (hstep : ∀ (n j : ℕ), j < M.dropLast.length →
      (0 < j → n * M.dropLast.length ≤
        parent (mTower M.dropLast d e n
            ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
          (srow (mTower M.dropLast d e n
              ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
            (mTower M.dropLast d e n
              ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length)
          (mTower M.dropLast d e n
            ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j).length) →
      mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j ∈ W u →
      mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1) ∈ W u) :
    ∀ n, mTower M.dropLast d e n ∈ W u := by
  refine mTowerClosed_of_snocStepPar ?_
  intro n j hj hpar0 hC
  set B := Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n) with hB
  have hBlen : B.length = M.dropLast.length := by
    rw [hB, Lift1_length, shiftr01_length]
  have hTlen : (mTower M.dropLast d e n).length = n * M.dropLast.length :=
    mTower_length M.dropLast d e n
  have hClen : (mTower M.dropLast d e n ++ B.take j).length
      = n * M.dropLast.length + j := by
    rw [List.length_append, hTlen, List.length_take, hBlen,
      Nat.min_eq_left (by omega)]
  have hC1len : (mTower M.dropLast d e n ++ B.take (j + 1)).length
      = n * M.dropLast.length + (j + 1) := by
    rw [List.length_append, hTlen, List.length_take, hBlen,
      Nat.min_eq_left (by omega)]
  have hsrow : srow (mTower M.dropLast d e n ++ B.take (j + 1))
      (n * M.dropLast.length + j) = srow (B.take (j + 1)) j := by
    unfold srow
    rw [show n * M.dropLast.length + j = (mTower M.dropLast d e n).length + j from by
        rw [hTlen],
      entry_append_right _ _ 2 j, entry_append_right _ _ 1 j]
  refine hstep n j hj (fun hj1 => ?_) hC
  by_cases hcone : le1 M.dropLast 0 j
  · -- ★ 錐の中: L3 の既存経路
    have hloc : hasParent (B.take (j + 1)) (srow (B.take (j + 1)) j) j :=
      block_blockParent_all_cone hj hj1 hr0 hcone
        (fun hpos => h2_cone hz0 j hj1 hj hpos hcone)
    have hpar : hasParent (mTower M.dropLast d e n ++ B.take (j + 1))
        (srow (B.take (j + 1)) j)
        ((mTower M.dropLast d e n ++ B.take (j + 1)).length - 1) := by
      rw [hC1len, show n * M.dropLast.length + (j + 1) - 1
          = (mTower M.dropLast d e n).length + j from by rw [hTlen]; omega]
      exact hasParent_append_right_of _ _ hloc
    have hres := snocStep_parent_sameBlock (d := d) (e := e) (n := n)
      (i := srow (B.take (j + 1)) j) hj hloc hpar
    rw [hC1len, show n * M.dropLast.length + (j + 1) - 1
      = n * M.dropLast.length + j from by omega] at hres
    rw [hClen, hsrow]
    exact hres
  · -- ★ 錐の外: §17
    have hjM : j < M.length - 1 := by
      rw [List.length_dropLast] at hj; omega
    have hout : ¬ le1 M 0 (0 + j) := by
      rw [Nat.zero_add]
      intro hc
      exact hcone (by
        rw [List.dropLast_eq_take]
        exact (le1_take (by omega) (by omega)).mpr hc)
    rw [hClen] at hpar0 ⊢
    rcases hpar0 with hp | hE
    · exact window_of_outOfCone_all hM2 hd1pos hd0e hr0M hlp hj hj1 hout hp
    · exfalso
      have : (mTower M.dropLast d e n ++ B.take j).length = 0 := by rw [hE]; rfl
      rw [hClen] at this
      omega




/-! ## 19. ★★★★★★★ **(c): 「親はブロック `n-1` にいる」を証明する**

L3 の §187.2 は「**親を `(n-1)*|Q| + p_rel` とすると**」と始まる
⟹ **「親がブロック `n-1` にいる」は仮定されていて、証明されていない。**

⚠ §263.2 で「`nextrel0` を 1 歩で繋ぐと `entry Q 0 0 + d ≤ entry Q 0 i` が要り、
`hr0`（`+1`）からは出ない」と書いたが、**それは 1 歩に限った話だった**:

    **`Gcopy.rtg0_of_window`（`Gcopy.lean:65`）**
      `j < |M|` → `a ≤ j` → (**`∀ l, a < l → l ≤ j → entry M 0 a < entry M 0 l`**)
      → `ReflTransGen (nextrel0 M) a j`

⟹ **鎖なら窓条件は狭義 `<` だけでよい。`+d` は要らない。⟹ §263.2 の障害は消えた。** -/

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


/-! ## 20. ★★ **`p_rel` の分割**（L3 の §187.2 の形）

`blockRoot_parent_prevBlock`（§19）で「親はブロック `k` の中」が出たので、
**`p_rel := parent − k*|Q|` が取れて `p_rel < |Q|`**。
⟹ L3 の §187.2 の「親を `k*|Q| + p_rel` とすると」がそのまま書ける。 -/

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

/-- ★ **ブロックの根は `srow = 1`**（`entry Q 2 0 = 0` ∧ `0 < e` ∧ `k+1 ≥ 1` のとき）。
⚠ 射程: **`k + 1 ≥ 1` と `0 < e` が要る**（`n = 0` のブロック 0 の根や `e = 0` では偽）。 -/
theorem srow_mTower_blockRoot_succ {Q : TrioSeq} {d e n k : ℕ}
    (hQ1 : 0 < Q.length) (hQne : Q ≠ []) (he : 0 < e) (hk : k + 1 < n)
    (hz0 : entry Q 2 0 = 0) :
    srow (mTower Q d e n) ((k + 1) * Q.length) = 1 := by
  have h2 : entry (mTower Q d e n) 2 ((k + 1) * Q.length) = 0 := by
    rw [entry2_mTower_blockRoot Q d e n (k + 1) (by omega) hQ1]; exact hz0
  have h1 : entry (mTower Q d e n) 1 ((k + 1) * Q.length) = entry Q 1 0 + e * (k + 1) :=
    entry1_mTower_blockRoot hQne d e n (k + 1) (by omega)
  have hmul : e * (k + 1) = e * k + e := Nat.mul_succ e k
  unfold srow
  rw [if_neg (by omega), if_pos (by omega)]

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


/-! ## 21. **塔の座標補題を揃える**

索引を引いた限り、**塔の中身を `(ブロック番号, ブロック内の添字)` で書く補題**は
プロジェクトに無い（`entry (mTower …)` を結論に持つ定理が 0 件）。
⟹ どの測度が生き残るかによらず使えるので、行 2 の一般版も入れておく。

    行 0 … `entry0_mTower_block`（§19、無条件）
    行 2 … 下（**無条件**。`Lift1` も `shiftr01` も行 2 を変えない）
    ⚠ 行 1 … **無条件では書けない**（`Lift1` は錐の中の列だけ持ち上げる）
             ⟹ 根（`i = 0`、必ず錐の中）だけが `entry1_mTower_blockRoot`（§19） -/

/-- 塔の第 `k` ブロックの `i` 番目の列の行 2（無条件）。 -/
theorem entry2_mTower_block (Q : TrioSeq) (d e : ℕ) :
    ∀ (n k i : ℕ), k < n → i < Q.length →
      entry (mTower Q d e n) 2 (k * Q.length + i) = entry Q 2 i := by
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
          entry_append_right, entry2_Lift1, entry2_shiftr01]

/-- ⟹ **`Q` の行 2 が一定なら、塔の行 2 も同じ値で一定**。
⚠ `L105Cap:6186` に**同名の別定理**があるので `h12_` を付けた（L3 の指摘）。 -/
theorem h12_row2_const_mTower (Q : TrioSeq) (d e n : ℕ) {c : ℕ}
    (h : ∀ i, i < Q.length → entry Q 2 i = c) :
    ∀ p, p < (mTower Q d e n).length → entry (mTower Q d e n) 2 p = c := by
  intro p hp
  rw [mTower_length] at hp
  have hQ1 : 0 < Q.length := by
    rcases Nat.eq_zero_or_pos Q.length with h0 | h0
    · rw [h0, Nat.mul_zero] at hp; omega
    · exact h0
  have hk : p / Q.length < n :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hp)
  have hi : p % Q.length < Q.length := Nat.mod_lt _ hQ1
  have hpq : p / Q.length * Q.length + p % Q.length = p := Nat.div_add_mod' p Q.length
  calc entry (mTower Q d e n) 2 p
      = entry (mTower Q d e n) 2 (p / Q.length * Q.length + p % Q.length) := by
        rw [hpq]
    _ = entry Q 2 (p % Q.length) := entry2_mTower_block Q d e n _ _ hk hi
    _ = c := h _ hi


/-! ## 22. **`j = 0` の窓の式**（L3 の §187.2 の「窓 `= |Q| − p_rel`」）

`blockRoot_parent_split`（§20）から、窓の値がそのまま出る。
⟹ **`p_rel ≥ 1` なら窓 `< |Q|`**（L3 の「良い側」の枝）。
⚠ **`p_rel = 0` は窓 `= |Q|`**（減らない側）。そこが核。 -/

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


/-! ## 23. ★★★★★★★★ **接頭辞つき窓補題**（L3 の指名）

L3 の `prefixTowerClosed_of_snocStepCone`（§167）は**接頭辞あり**だが `le1 Q 0 j` が残る。
私の `window_of_outOfCone_all`（§17）は **`le1` を消す**が接頭辞なし。
⟹ **足りないのはその接頭辞つき版 1 本。**

⚠ L3 の指定した合成点（`prefixSnocStep_parent_sameBlock`）は **`hloc`（ブロック内に親）**を
要求するが、**錐の外の列は 68.8% がブロック内で孤児**なので `hloc` は出ない。
⟹ **別の道を使う**（索引を**型**で引いて見つけた。教訓: 名前ではなく型で引く）:

    **`Column.hasParent_append_right`（`Column.lean:363`）**
      `entry T 0 0 = 0` → `0 < entry (A ++ T) 0 (|A| + j1)` →
      **`hasParent (A ++ T) i (|A| + j1) ↔ hasParent T i j1`**
    **`Column.parent_append_right`（`Column.lean:384`）**
      同じ前提 ＋ `hasParent T i j1` →
      **`parent (A ++ T) i (|A| + j1) = |A| + parent T i j1`**

⟹ **`T := mTower Q d e n ++ B.take (j+1)` と取れば、接頭辞 `A` がまるごと剥がれる。**
⚠ `entry T 0 0 = entry Q 0 0` なので **`entry Q 0 0 = 0`（根が深さ 0）が要る**。
　 消費側の `Q = Lift1 ((0,v,z) :: R.dropLast) t` では成り立つ。 -/

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


/-! ## 24. **L3 の §167 の書き方に合わせた版** ＋ **二分法の `iff`**

L3 の §167 は位置を **`(A ++ mTower Q d e n ++ B.take j).length`** と書く。
私の §23 は **`(A ++ mTower Q d e n).length + j`**。値は同じなので橋を 1 本。 -/

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


/-! ## 25. **R2 の骨の 1 行を Lean に** —— 行 2 はリフトされないので親になれない

R2 の 6 行のうち:

> **塔のブロック根どうしは、その行がリフトを受けない限り値が等しい。**
> **`nextrel_i` は狭義不等号を要求するので、親になれるのは「リフトを受けている行」だけ。**
> **行 0 ＝ `shiftr01 (d*k)` ⟹ `d > 0` が要る。行 1 ＝ `Lift1 (e*k)` ⟹ `e > 0` が要る。**
> **行 2 ＝ リフトされない ⟹ 決して親になれない。**

⟹ 行 2 の分は `entry2_mTower_blockRoot`（§20）から直に出る。 -/

/-- ★ **ブロック根どうしの行 2 は等しい**（`Lift1` も `shiftr01` も行 2 を変えない）。 -/
theorem entry2_blockRoots_eq (Q : TrioSeq) (d e n k m : ℕ)
    (hQ1 : 0 < Q.length) (hk : k < n) (hm : m < n) :
    entry (mTower Q d e n) 2 (k * Q.length)
      = entry (mTower Q d e n) 2 (m * Q.length) := by
  rw [entry2_mTower_blockRoot Q d e n k hk hQ1,
    entry2_mTower_blockRoot Q d e n m hm hQ1]

/-- ★★ **行 2 ではブロック根はブロック根の親になれない**（狭義増加が破れる）。
＝ R2 の「行 2 はリフトされない ⟹ 決して親になれない」。 -/
theorem no_nextrel2_between_blockRoots {Q : TrioSeq} {d e n k m : ℕ}
    (hQ1 : 0 < Q.length) (hk : k < n) (hm : m < n) :
    ¬ nextrel2 (mTower Q d e n) (k * Q.length) (m * Q.length) := by
  intro h
  have hlt : entry (mTower Q d e n) 2 (k * Q.length)
      < entry (mTower Q d e n) 2 (m * Q.length) := h.2.2.2.1
  rw [entry2_blockRoots_eq Q d e n k m hQ1 hk hm] at hlt
  omega

/-- ★ **行 1 では `e > 0` が要る**（`e = 0` ならブロック根の行 1 も等しく、親になれない）。 -/
theorem no_nextrel1_between_blockRoots_of_e_zero {Q : TrioSeq} {d n k m : ℕ}
    (hQne : Q ≠ []) (hk : k < n) (hm : m < n) :
    ¬ nextrel1 (mTower Q d 0 n) (k * Q.length) (m * Q.length) := by
  intro h
  have hlt : entry (mTower Q d 0 n) 1 (k * Q.length)
      < entry (mTower Q d 0 n) 1 (m * Q.length) := h.2.2.2.1
  rw [entry1_mTower_blockRoot hQne d 0 n k hk,
    entry1_mTower_blockRoot hQne d 0 n m hm] at hlt
  omega

/-- ★ **行 0 では `d > 0` が要る**（`d = 0` ならブロック根の行 0 も等しく、親になれない）。 -/
theorem no_nextrel0_between_blockRoots_of_d_zero {Q : TrioSeq} {e n k m : ℕ}
    (hQ1 : 0 < Q.length) (hk : k < n) (hm : m < n) :
    ¬ nextrel0 (mTower Q 0 e n) (k * Q.length) (m * Q.length) := by
  intro h
  have hlt : entry (mTower Q 0 e n) 0 (k * Q.length)
      < entry (mTower Q 0 e n) 0 (m * Q.length) := h.2.2.2.1
  have hk0 := entry0_mTower_block Q 0 e n k 0 hk hQ1
  have hm0 := entry0_mTower_block Q 0 e n m 0 hm hQ1
  rw [Nat.add_zero] at hk0 hm0
  rw [hk0, hm0] at hlt
  omega


/-! ## 26. **`hbase` は消費側で無料**（§271 で私が足した唯一の前提を消す）

§271 の `prefix_window_of_outOfCone_all` に **`hbase : entry M.dropLast 0 0 = 0`** を
足した。⟹ 消費側の `M = Lift1 ((0,v,z) :: R) t` では無料であることを示す。
（**自分が足した前提は自分で消す。**） -/

/-- `dropLast` は先頭列を変えない（`2 ≤ |M|` なら）。 -/
theorem entry_dropLast_zero {M : TrioSeq} (hM2 : 2 ≤ M.length) (i : ℕ) :
    entry M.dropLast i 0 = entry M i 0 := by
  rw [List.dropLast_eq_take, entry_take (show (0 : ℕ) < M.length - 1 by omega)]

/-- ★ **消費側では `hbase` は無料**: `M = Lift1 ((0,v,z) :: R) t` の根の行 0 は 0。 -/
theorem hbase_of_consumer {v z t : ℕ} {R : TrioSeq}
    (hM2 : 2 ≤ (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length) :
    entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).dropLast 0 0 = 0 := by
  rw [entry_dropLast_zero hM2, entry0_Lift1]
  rfl

open Classical in
/-- ★★ ⟹ **消費側の形に特化した接頭辞つき窓補題**（`hbase` を落とした）。 -/
theorem prefix_window_of_outOfCone_consumer {A : TrioSeq} {v z t : ℕ} {R : TrioSeq}
    {d e n j : ℕ}
    (hM2 : 2 ≤ (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length)
    (hd1pos : 0 < e)
    (hd0e : entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t) 0
        (0 + (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).dropLast.length)
      = entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t) 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length →
      entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t) 0 0
        < entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t) 0 l)
    (hlp : le1 (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t) 0
      (0 + (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).dropLast.length))
    (hj : j < (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).dropLast.length) (hj1 : 0 < j)
    (hout : ¬ le1 (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t) 0 (0 + j))
    (hpar0 : hasParent (A ++ mTower (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0
          (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).dropLast) (e * n)).take (j + 1))
      (srow (A ++ mTower (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0
            (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).dropLast) (e * n)).take (j + 1))
        ((A ++ mTower (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).dropLast d e n).length + j))
      ((A ++ mTower (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).dropLast d e n).length + j)) :
    (A ++ mTower (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).dropLast d e n).length
      ≤ parent (A ++ mTower (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).dropLast d e n
          ++ (Lift1 (shiftr01 (d * n) 0
            (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).dropLast) (e * n)).take (j + 1))
        (srow (A ++ mTower (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).dropLast d e n
            ++ (Lift1 (shiftr01 (d * n) 0
              (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).dropLast) (e * n)).take (j + 1))
          ((A ++ mTower (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).dropLast d e n).length + j))
        ((A ++ mTower (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).dropLast d e n).length + j) :=
  prefix_window_of_outOfCone_all hM2 hd1pos hd0e hr0 hlp (hbase_of_consumer hM2)
    hj hj1 hout hpar0


/-! ## 27. ★★★★★★★★ **§186 の接頭辞つき版**（L3 の指名。測度の帰納の最後の 1 つ）

L3 の `snocStep_oper_tower`（`L105Cap:13093`、緑）は**接頭辞なし**。
測度の帰納は族 **`A ++ mTower V d e m`** の上で回すので**接頭辞つきが要る**。

⟹ §23 と**同じ道**（接頭辞をまるごと剥がす）で出る:

    **`Column.oper_append_right`（`Column.lean:437`）**
      `2 ≤ |T|` → **`entry T 0 0 = 0`** → **`oper (A ++ T) n = A ++ oper T n`**

⟹ `T := mTower Q d e n ++ B.take (j+1)` と取れば、`entry T 0 0 = entry Q 0 0`
（§23 の `entry0_towerPrefix_root`）なので、消費側では `= 0`。 -/

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


/-! ## 28. ★★★★★★★★ **測度 `(|V|, rankDE)` の整礎帰納**（L3 の指名、形 (b)）

L3 の指定:「形 **(b)**（`ℕ` の対についての強帰納の原理）が使いやすい」。

⚠ **索引ではなく Mathlib を引いた**（L3 の指示）:

    **`WellFounded.prod_lex`**（`Mathlib/Order/RelClasses.lean:180`）
      `WellFounded ra → WellFounded rb → WellFounded (Prod.Lex ra rb)`
    **`wellFounded_lt`** … `[WellFoundedLT α]` のとき `WellFounded (· < ·)`

⟹ 作る必要はなく、繋ぐだけだった。 -/

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

/-! ### 28.1 **関係を作る側**（L3 が各段で使う形）

`Prod.Lex` の構成子を、この場面の名前で置いておく。 -/

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


/-! ## 29. **(n1b) `MTowerClosedRow2` と `L106` の鎖の噛み合わせ**

`Final.lean:875` が要るのは **`L105.MTowerClosedRow2`（`L105Cap:5794`）**:

    ∀ (u d e n) (Q), **`Q ∈ W u`** → **`∀ j, 1 ≤ j → j < |Q| → entry Q 0 0 < entry Q 0 j`**
      → **`∃ p ∈ Q, 0 < p.2.2`** → `mTower Q d e n ∈ W u`

`L106` の鎖（`prefixTowerClosed_of_snocStepCone`、`L105Cap:11940`）が要るのは

    `hA : A ∈ W u`, `hr0`, **`hz0 : entry Q 2 0 = 0`**, `hstep`

⟹ ⛔ **`MTowerClosedRow2` は `hz0` を供給しない。**
`∃ p ∈ Q, 0 < p.2.2` は「**どれかの**列の行 2 が正」であって、
**根の行 2 が 0 とは言っていない**。

### 29.1 ⟹ 覆えている場合と、覆えていない場合

    **行 2 ≡ 0**       … `mTower_mem_of_zeroRow2`（`L105Cap:5781`、仮定ゼロ）✅
                        （だから `MTowerClosedRow2` は「行 2 に非零」だけを見る）
    **`entry Q 2 0 = 0` ∧ どれかが正** … **`L106` の鎖**（`hz0` が出る）✅
    **行 2 ≡ c ≥ 1**   … 下の `mTower_mem_of_constRow2`（**この節で緑にした**）✅
    ⛔ **`entry Q 2 0 > 0` ∧ 行 2 が定数でない** … **どれも当たらない ＝ 穴**

⟹ **これが `Final.lean` に繋ぐときの最後の穴。** -/

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


/-! ## 30. ★★★ **(n2) `MTowerSingle` の接頭辞つき版**

R2 の測定: 消費側で降りて現れる `V` の残差のうち **4.32% が `|V| = 1`**。
⟹ §81 `mTowerSingle_holds`（緑）が覆うが、**結論に接頭辞が無い**（L3 の §191.2）。

⚠ 消費側は `MTowerClosedRow2` の枝なので **`∃ p ∈ Q, 0 < p.2.2`**、
`|Q| = 1` なら **`0 < entry Q 2 0`**。⟹ **行 2 が正の場合だけでよい。**

⟹ そのとき塔の**行 2 は定数で正**なので、末尾列は**必ず行 2 の孤児**:

    `L105.not_hasParent_two_of_row2_const`（`L105Cap:6216`）
    `L105.snoc_orphan_W`（`L105Cap:144`）… 孤児 snoc は段によらず無料

⚠ 接頭辞を剥がすのに `Column.hasParent_append_right` を使うが、その `hpos`
（列の行 0 が正）は **深さ 0 の列では破れる**。⟹ **深さ 0 は別に潰す**（下）。 -/

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


/-! ## 31. ★★★ **(m1) `zle1 R` は「末尾列 1 本」に落ちる**

team-lead の (n3) への (C):「`hz0 : entry Q 2 0 = 0` が強すぎる。弱めよ」。
⟹ **`hz0'`（行 2 の最小性）より良い道がありました。**

⚠ `L105.tower2_not_z1_of_zle1`（`L105Cap:3801`）の証明を読むと、**`zle1 R` は 1 か所**

    `have hle : entry R 2 (R.length - 1) ≤ 1 := hz _ hmem`

にしか使われていない ⟹ **末尾列だけ**。そして本体は

    **`L53.tower2_zr`（`L53Subst:2380`、緑、**`zle1` 不要**）**
      `R ≠ []` → `domT R m` → `srow R (|R|-1) = 2` → `hpM` → **`z < entry R 2 (|R|-1)`**

⟹ ★ **`tower2_zr` の 4 前提は `LiftTowerExp2` が**全部持っています**。**
⟹ ⟹ **`z = 0` ⟺ `entry R 2 (|R|-1) ≤ 1`**（**1 列だけの条件**）。 -/

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


/-! ## 32. ⛔ **`h1out` は偽** —— L3 自身の §184 の反例がそのまま効く

L3 の §211 `prefixTowerClosed_final_full` が新しく置いた前提:

    `h1out : ∀ j, 0 < j → j < |Q| → ¬ le1 Q 0 j →
       0 < entry Q 1 j → **entry Q 1 0 < entry Q 1 j**`

⚠ これは `hhigh`（L3 の §180 `le1_chain_in_block` の前提）に
`0 < entry Q 1 j` を足しただけ。⟹ **L3 が §184 で見つけた反例がそのまま効く。**

    **`Q = (0,1,0)(1,0,0)(1,1,1)(1,0,0)`、`j = 2`**
      錐の外 ✓（行 1 が根と**等号** ⟹ `not_le1_of_tie`）
      `entry Q 1 2 = 1 > 0` ✓（`h1out` の前件を満たす）
      **`entry Q 1 0 = 1 < 1` は偽** ⟹ **`h1out` が破れる**

⟹ ★ **等号のブロッカーは `0 < entry Q 1 j` を満たすので、前件では除けない。** -/

/-- `h1out` の反例（L3 の §184 と同じ `Q`）。 -/
def Qh1 : TrioSeq :=
  [((0, 1, 0) : ℕ × ℕ × ℕ), ((1, 0, 0) : ℕ × ℕ × ℕ),
   ((1, 1, 1) : ℕ × ℕ × ℕ), ((1, 0, 0) : ℕ × ℕ × ℕ)]

/-- ⛔ **`h1out` は偽**。 -/
theorem h1out_false :
    ¬ (∀ j, 0 < j → j < Qh1.length → ¬ le1 Qh1 0 j →
        0 < entry Qh1 1 j → entry Qh1 1 0 < entry Qh1 1 j) := by
  intro h
  have hout : ¬ le1 Qh1 0 2 :=
    L105.not_le1_of_tie (by omega)
      (show entry Qh1 1 2 = entry Qh1 1 0 from rfl)
  have hres := h 2 (by omega)
    (show (2 : ℕ) < Qh1.length from by rw [show Qh1.length = 4 from rfl]; omega)
    hout (show 0 < entry Qh1 1 2 from by rw [show entry Qh1 1 2 = 1 from rfl]; omega)
  rw [show entry Qh1 1 0 = 1 from rfl, show entry Qh1 1 2 = 1 from rfl] at hres
  omega


/-! ## 33. **(z1)(z2)(z3) 行 2 は増えない。しかし `zle1` は `W u` の不変量ではない**

team-lead:「行 2 はリフトされない ⟹ `zle1` を `W u` の不変量にできるのでは」。

### (z1) ⚠ **既にありました**（今日 6 件目）

    **`Wset.zle1_oper`（`Wset:2472`、緑）** … `zle1 B → zle1 (B⟦n⟧)`
    **`Wset.zle1_ST_TS`（`:2516`、緑）** … `ST_TS M → zle1 M`（**標準形は `zle1`**）

### (z2) `graft` も行 2 を**そのまま写す**

    `Wset.graft`（`Wset:66`）:
      `graft M z = M.dropLast ++ z.map (fun p => (p.1 + entry M 0 (|M|-1), **p.2.1, p.2.2**))`
    ⟹ **行 2 は逐語コピー。増えません。**

### (z3) ⛔ **それでも `zle1` は `W u` の不変量になりません**

⚠ **障害は「増える箇所」ではなく、`W` の**基底**です:**

    **`Wset.Om_mem_W (v z) : [(0,v,z)] ∈ W (2*v + z)`**（`Wset:1696`、緑）
    ⟹ **`z` は任意**。⟹ `[(0,0,2)] ∈ W 2` で **`zle1` が破れる**。

⟹ **`Aop` の節 3 は `∀ y ∈ W m` を走るので、`zle1` でない `y` が必ず来ます。**
⟹ ★ **team-lead の元の判定（「全列の条件は復元できない」）は**正しかった**。**
⟹ ⟹ ただし理由は「節 3 で作り直せない」ではなく「**`W` がそもそも `zle1` で閉じていない**」。 -/

/-- ⛔ **`W u` は `zle1` で閉じていない**（基底 `Om_mem_W` に任意の `z` が入る）。 -/
theorem W_not_zle1_closed :
    ([((0, 0, 2) : ℕ × ℕ × ℕ)] ∈ W 2) ∧ ¬ zle1 [((0, 0, 2) : ℕ × ℕ × ℕ)] := by
  refine ⟨?_, ?_⟩
  · have := Om_mem_W 0 2
    simpa using this
  · intro h
    have h2 := h ((0, 0, 2) : ℕ × ℕ × ℕ) (by simp)
    have : ((0, 0, 2) : ℕ × ℕ × ℕ).2.2 = 2 := rfl
    omega


/-! ## 34. **(z0) 強めた `h1out` も偽** —— ただし team-lead の直しは**半分効く**

team-lead:「`h1` の枝は `¬ (0 < entry (B.take (j+1)) 2 j)` の中なので、
`entry Q 2 j = 0` を**タダで**前件に足せる」⟹ **正しいです。**

    **✅ §32 の反例（`srow = 2`）は死にます**: `Q = (0,1,0)(1,0,0)(1,1,1)(1,0,0)`、`j = 2`
      ⟹ `entry Q 2 2 = 1 ≠ 0` ⟹ 前件を満たさない ⟹ 空虚に真

⛔ **しかし `srow = 1` のブロッカーが残ります**（行 2 = 0 で行 1 が根と等号）:

    **`Q = (0,1,0)(1,1,0)`、`j = 1`**
      錐の外 ✓（行 1 が根と**等号**）／ **`entry Q 2 1 = 0`** ✓（強めた前件も満たす）
      `0 < entry Q 1 1 = 1` ✓ ／ `entry Q 1 0 < entry Q 1 1` ⟺ `1 < 1` ⟹ **偽**

⚠ **この `Q` は `hr0` を満たします**（根の深さ 0 < 1）。⟹ 前提で除けません。

⟹ ★ **分母は 16960 → 4428（`srow = 1`）に落ちるが、0 にはならない。**
⟹ ⟹ **残る 4428 が、まさに「等号のブロッカー」＝ 私の (C2) の残差の源。** -/

/-- 強めた `h1out` の反例（`srow = 1` の等号ブロッカー）。 -/
def Qh1s : TrioSeq := [((0, 1, 0) : ℕ × ℕ × ℕ), ((1, 1, 0) : ℕ × ℕ × ℕ)]

/-- ⛔ **`entry Q 2 j = 0` を足しても `h1out` は偽**。 -/
theorem h1out_strong_false :
    ¬ (∀ j, 0 < j → j < Qh1s.length → ¬ le1 Qh1s 0 j →
        entry Qh1s 2 j = 0 → 0 < entry Qh1s 1 j →
        entry Qh1s 1 0 < entry Qh1s 1 j) := by
  intro h
  have hout : ¬ le1 Qh1s 0 1 :=
    L105.not_le1_of_tie (by omega)
      (show entry Qh1s 1 1 = entry Qh1s 1 0 from rfl)
  have hres := h 1 (by omega)
    (show (1 : ℕ) < Qh1s.length from by rw [show Qh1s.length = 2 from rfl]; omega)
    hout (show entry Qh1s 2 1 = 0 from rfl)
    (show 0 < entry Qh1s 1 1 from by rw [show entry Qh1s 1 1 = 1 from rfl]; omega)
  rw [show entry Qh1s 1 0 = 1 from rfl, show entry Qh1s 1 1 = 1 from rfl] at hres
  omega

/-- ⟹ ★ ただし `Qh1s` は `hr0`（根が狭義最浅）を**満たす** ⟹ 前提では除けない。 -/
theorem Qh1s_hr0 : ∀ l, 0 < l → l < Qh1s.length → entry Qh1s 0 0 < entry Qh1s 0 l := by
  intro l hl0 hll
  rw [show Qh1s.length = 2 from rfl] at hll
  have : l = 1 := by omega
  subst this
  rw [show entry Qh1s 0 0 = 0 from rfl, show entry Qh1s 0 1 = 1 from rfl]
  omega


/-! ## 35. ★★★ **(あ) `h1out` の正体: 「`j` 自身がブロッカーでない」**

team-lead の手（「その枝で何がタダで手元にあるか読む」）をもう一度当てた。
`block_blockParent_row1_outcone`（`L105Cap:12276`）の証明の 1 行目:

    `obtain ⟨y, hy, hy0, hy1⟩ := (**not_le1_zero_iff** hr0 hj).mp hout`

    **`L105.not_le1_zero_iff`（`L105Cap:7149`、緑）**
      `¬ le1 Q 0 q ↔ **∃ y, ReflTransGen (nextrel0 Q) y q ∧ y ≠ 0 ∧ entry Q 1 y ≤ entry Q 1 0**`

⟹ ★ **錐の外 ⟺ ブロッカー `y` が存在する**（行 0 の祖先で、非根で、行 1 が根以下）。

そして `hhigh : entry Q 1 0 < entry Q 1 j` は、証明の中で
**`y = j` の場合を潰す**ためだけに使われている（`hylt : y < j` の導出）。

> ★★ **⟹ `h1out` ⟺ 「ブロッカーは `j` 自身ではない」。**
> ⟹ ⟹ **`h1out` が破れる ⟺ `j` 自身がブロッカー**（`entry Q 1 j ≤ entry Q 1 0`）。

⟹ ★ **私の反例 `Q = (0,1,0)(1,1,0)`, `j = 1` は、まさに「`j` 自身がブロッカー」。**
⟹ ⟹ そしてそのとき **根は行 1 の親になれない**（`nextrel1` は狭義増加を要求）。
⟹ ⟹ ⟹ **「等号 ⟹ 親なし」の線（team-lead の (い)）は、ここから来る。** -/

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


/-! ## 36. ★★★ **(p1) `blockRoot_parent_prevBlock` の行 0 版**

team-lead:「`srow = 0` のブロック根なら、行 1 の議論が**行 0**でできるのでは」。

⚠ **(p1b) の答えを先に**: **行 0 のほうが**簡単**です。**

    `nextrel1` の最小性 … **`le0` 祖先の上**だけ ⟹ `rtg0_blockRoot_succ`（鎖）が要った
    **`nextrel0` の最小性 … `j0` と `j1` の**素の区間**の上** ⟹ **鎖が要らない**

⟹ ★ ですから行 0 版は `le0` 条件なしで通ります。 -/

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


/-! ## 37. ★★★ **(q2a) `blockRoot_parent_prevBlock` の証人つき一般化**

team-lead:「最小性の**証人**に『ブロック `k` の**根**』を入れているから `e` が要る。
**根でない証人**なら `e = 0` でも矛盾が出る」。⟹ **一般化は正しく、通ります。**

⚠ **道具**: `L105.block_getD`（`L105Cap:7056`）
    `(Lift1 (shiftr01 (d*n) 0 Q) (e*n)).getD j = (entry Q 0 j + d*n,
       **entry Q 1 j + (if le1 Q 0 j then e*n else 0)**, entry Q 2 j)`
⟹ **行 1 は `entry Q 1 j + e*n` で上から押さえられる**（錐の中でも外でも）。 -/

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


/-! ## 38. ★★★★ **(q5) `le0` の祖先を 1 ブロック前へずらす**

team-lead の訂正した ③。⚠ **(q5a): 索引に無い**（`le0_block_in_tower` は**ブロック内**、
`le0_block_root` は根→列。**ブロックを跨ぐ平行移動は無い**）。
⚠ 実測 **100%**（分母 347,648 まで、3 箱、`e ∈ {0,1,2}`）。

### 道具立て: `le0` の**窓の特徴づけ**（これも索引に無かった）

    `Gcopy.rtg0_of_window`（`Gcopy:65`）… **窓 ⟹ 鎖**（既存）
    ⛔ **鎖 ⟹ 窓** … **無い** ⟹ 下で作る（`rtg0_entry_mono` ＋ `rtg0_window`） -/

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


/-! ## 39. ★★★★★ **(q3b) `he`（`0 < e`）が落ちた** —— (q5) が効きました

`e = 0` のときブロックは**行 1 を触らない**ので、(q5) の証人（ブロック `k` の同じ位置）の
行 1 は `a` の行 1 と**等しい**。⟹ `nextrel1` の狭義増加と矛盾。 -/

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


/-! ## 40. ★★★ **接頭辞つきの `d = e = 0` の枝は無料**（`ZeroDOK`）

§290 の場合分けの最後の枝 `srow = 1` ∧ `e = 0` ∧ `d = 0` は、私の
`H12A2.mTower_d0_mem` が覆うが**接頭辞なし**だった（team-lead の指摘）。

⚠ **接頭辞つきは既にありました**（今日 8 件目）:

    **`L105.prefixCopies_of_based`（`L105Cap:1294`、**仮定ゼロ**）**
      `A ∈ W u` → `Q ∈ W u` → **`based Q`** → `A ++ (range n).flatMap (fun _ => Q) ∈ W u`

⟹ `mTower Q 0 0 n` は**同一コピーの連結**なので、そのまま当たる。 -/

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


/-! ### 40.1 ★★★ **`d = 0` では機構が反転する** —— ブロック根は塔の中で**孤児**

`ZeroDOK`（`L106:3208`）は `e` が**一般**なので、上の「同一コピー」は `e = 0` の枝しか
覆わない。では `e > 0` はどうか。⟹ **`d = 0` の塔では、行 0 が全ブロックで同じ**:

    `entry (mTower Q 0 e n) 0 (k*|Q| + q) = entry Q 0 q`

⟹ `hr0`（根が狭義最浅）と合わせて、**ブロック根の行 0 は塔全体の最小値**。
⟹ `nextrel0` は狭義増加を要求するので、**ブロック根に入る `nextrel0` は無い**。
⟹ `nextrel1` は `le0` を要求し、`nextrel2` は `le1` を要求するので、
   **どの行でもブロック根に親は無い**（塔の中では）。

⚠ **`0 < d` のときの `blockRoot_hasParent_prev`（`L106`）は、`d = 0` では
   「親がある」どころか「親が無い」に**反転**します。**
⟹ ⟹ ★ だから `ZeroDOK` は `hsnoc_zero` の書き換えではなく、
   **`snoc_orphan_W`（孤児の枝）で処理するのが筋**です。 -/

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


/-! ### 40.2 ★★★★★ **`d = 0` なら、全ブロック根は `Q` の根と同じ親を持つ**

§40.1 は「塔の中では親が無い」。⟹ **親があるとすれば接頭辞 `A` の中**。
⟹ 行 0 が全ブロックで同じで、間の列は全部 `≥ entry Q 0 0` なので、
`nextrel0` の最小性が **どのブロック根についても同じ列を選ぶ**。

⟹ ⟹ ★ だから `ZeroDOK` の `j = 0`（ブロック根）は
「`Q` の根の親がそのまま `(k+1)` 番目のブロック根の親になる」で処理できる。 -/

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


/-! ### 40.3 `d = 0` のブロック根の `srow` と `le0` 祖先

`snoc_orphan_W` は `srow` を要求するので、ブロック根の `srow` を確定させる。
`Lift1` は行 2 を変えず、行 1 は根で `+ e*k` するだけ。 -/

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


/-! ## 41. `ZeroEOK`（`e = 0` の枝、`L106:3213`）

`mTower Q d 0 n = shTower Q d n`。行 1 は全ブロックで `Q` と同じ
（`entry1_mTower_block_e_zero`、§293）。行 2 は `shiftr01` も `Lift1` も変えない。 -/

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


/-! ## 42. ★★★★★★ **`ZeroDOK` の本丸: `d = 0` の行 1 から塔が消える**

§294.3 で分かったこと: `e ≥ 1` なら `k ≥ 1` のブロック根は必ず `srow = 1`。
⟹ **`ZeroDOK` の本体は行 1**。

⟹ ★ ところが §294.2 の 2 本
（`nextrel0_prefix_blockRoot_src_d_zero`: 行 0 の親は必ず `A` の中、
　`le0_prefix_blockRoot_iff_d_zero`: `le0` の祖先集合は全ブロック共通）を合わせると、
`nextrel1` の条件から **塔がまるごと消えます**。残るのは

    S = {j < |A| : le0 M j |A|}      （`Q` の根の行 0 の祖先たち）
    c_k = entry Q 1 0 + e*k           （ブロック根の行 1）

だけ。 -/

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


/-! ### 42.1 ★★★★★★★ **親は `A` の 1 列に固定される**

`nextrel0` の始点は**一意**（最小性から出る）。⟹ `Q` の根の行 0 の親 `a0` があれば、
`a0 < j < |A|` で `le0 M j |A|` を満たす `j` は**存在しない** ⟹ §42 の最小性の条件が
**空虚に成り立つ** ⟹ 閾値 `c_k` が `entry M 1 a0` を超えたとたん、
**ブロック根の行 1 の親は `a0` に決まる**（存在も一意性も）。 -/

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


/-! ### 42.2 残りの枝（閾値を超える前の小さい `k`）

閾値 `c_k = entry Q 1 0 + e*k` は `k` で増える。⟹ 親は `A` の中の `le0` 祖先の鎖を
**上へ動くだけ**で、`c_k` が `entry M 1 a0` を超えた時点で `a0` に着く（§42.1）。 -/

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


/-! ## 43. ★★★ **ブロックの中の行 0 は `Q` と同型**（`d`・`e` に依らない一般の道具）

行 0 は `Lift1` で変わらず、`shiftr01 (d*k) 0` で一様に `+ d*k` されるだけ。
⟹ 同じブロックの中の比較は `Q` の中の比較とまったく同じ。
⟹ `nextrel0` の最小性の区間もブロックの中に収まるので、**そのまま移る**。 -/

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


/-! ## 44. ★★★★★★ **`hsnoc_zero_of_parent` の `0 < d` は「末尾列が非零」だけ**

`L106.hsnoc_zero_of_parent` の中で `hd : 0 < d` が使われているのは**ただ 1 か所**、

    hz : ¬ (entry S 0 (last) = 0 ∧ entry S 1 (last) = 0 ∧ entry S 2 (last) = 0)

を `entry S 0 (last) = entry Q 0 0 + d*(k+1) > 0` から出すところだけ。

⟹ ★ **`0 < d` は「末尾列が非零」に弱められる**。
⟹ ⟹ `d = 0` でも **`0 < e` なら行 1 が `entry Q 1 0 + e*(k+1) ≥ e ≥ 1` で自動的に非零**。 -/

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


/-! ## 45. ★★★★★★★ **`d = 0` なら `e = 0`** —— `wd0 = 0 ⟹ wd1 = 0`

`wd0 P B j p = if 0 < srow(末尾) then entry 0 (末尾) - entry 0 (P.length+p) else 0`
`wd1 P B j p = if 1 < srow(末尾) then entry 1 (末尾) - entry 1 (P.length+p) else 0`

⟹ `wd1 > 0` には `srow = 2` が要る。⟹ そのとき親は `nextrel2` の始点で、
`nextrel2` は `le1` を、`le1` の各段（`nextrel1`）は `le0` を要求する。
⟹ **親は末尾の `le0` 祖先** ⟹ **行 0 が狭義に小さい** ⟹ `wd0 > 0`。

⟹ ⟹ ★★★ **`wd0 = 0` なら `wd1 = 0`**。⟹ 測度の再帰で `d = 0` が出るときは
**必ず `e = 0` も一緒**。⟹ `TowerP''` に `d = 0 → e = 0` を足せば、
`ZeroDOK` は **`d = e = 0`（同一コピー）だけ**でよくなる。 -/

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


/-! ## 46. ★★★★★★★ **`le0` は塔の根を通る** —— L3 の §228.1「次の仕事」

L106 §228.1（`OrphOK`）に:

  「上の 3 本は緑ですが、`OrphOK` を導いてはいません。
   ⟹ **`le0` / `le1` が塔の根を通ることを別に示す必要があります**」

とある。⟹ ★ **行 0 は `hr0`（塔の根が狭義最浅）だけで出る**。
`Column.nextrel0_no_cross`（`Column:192`）は `based T`（`entry T 0 0 = 0`）を要求するが、
**`based` は要らない**。「根が狭義最浅」で足りる。 -/

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


/-! ## 47. ★★★ 塔の「ブロッカー無し」（`hnb`）は **`Q` の条件に降りる**

`no_nextrel1_cross_of_cone` 系が要求する

    hnb : ∀ l, 0 < l → l < T.length → entry T 1 0 < entry T 1 l   （T = mTower Q d e n）

は、`Lift1` が行 1 を**下げない**ので `Q` のブロッカー無しと `0 < e` に落ちる。 -/

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


/-! ## 48. `hnbQ`（ブロッカー無し）の遺伝 —— **`hr0` と同じ手は効かない**

`hr0_wnd`（窓の根が行 0 で狭義最浅、L106、無料）が通るのは、
**`nextrel0` の最小性が「素の区間」上**だから（`∀ j, j0 < j ∧ j < j1 → …`）。

⛔ ところが `nextrel1` の最小性は **`le0` 祖先の上だけ**（`∀ j, j0 < j ∧ le0 M j j1 → …`）。
⟹ 窓の中で `le0` 祖先でない列には**何の制約も付かない** ⟹ 同じ手では出ない。

⟹ 出るのは「`le0` 祖先の上でだけ狭義最小」まで（下、緑）。 -/

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


/-! ### 48.1 ★ 壁の弱め版: **接頭辞からの越境は必ずブロッカーに着く**

`no_nextrel1_cross_of_cone` の対偶。⟹ `hnb` を**全列**について要求しなくても、
「越境先がブロッカーでない」ことさえ言えれば壁が立つ。 -/

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


/-! ## 49. ★★★★★★★ **`h1out` が遺伝しない機構を定理にする**

R2 (s11) の機構: 「`Lift1 X t` は **`le1 X 0 j`（錐の中）の列だけ**に `t` を足す
⟹ 根は必ず錐の中 ⟹ 根は `+t` される ⟹ ⛔ `h1out` の相手は**錐の外** ⟹ 持ち上がらない
⟹ **差が毎段 `t` ずつ縮む**」 ⟹ ★ これを定理にする。「いつ追いつかれるか」が**式で出る**。 -/

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


/-! ### 49.1 ★★★★★★ 塔の行 1 の**閉じた式** ⟹ 「いつ追いつかれるか」が式で出る

索引に `le1_block`（`L105Cap:4556`、`le1 (Lift1 (shiftr01 d0 0 Q) d1) a b ↔ le1 Q a b`）
があった ⟹ **ブロックの錐 ＝ `Q` の錐**。⟹ 塔の行 1 が閉じた式になる。 -/

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


/-! ### 49.2 ★★★★★★★ **4 通りの表** —— 悪くなるのは 1 マスだけ

窓の根が `(k, p)`、的が `(k', j)`（`k ≤ k'`）のとき、「的が窓の根に対してブロッカー」は: -/

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


/-! ### 49.3 ⛔⛔ **`h1out` は塔が高くなると必ず壊れる**（定理）

表の「悪くなるマス」の条件は `entry Q 1 j ≤ entry Q 1 p + e*k`。
⟹ `0 < e` なら `e*k ≥ k` なので、**`k ≥ entry Q 1 j` で必ず成立**する。
⟹ ⟹ ★ **窓の根が第 `k` ブロック（`k` 大）にあり、窓に錐の外の列が 1 つでもあれば、
`h1out`（＝ `hnbQ`）は破れる。** ⟹ 「予算 `e*k` はいくらでも大きくなる」ため。 -/

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


/-! ## 50. ★★★★★★★ (W7) R2 の「型 B」を式で解く

R2 の (BREAK): 破れは 2 型に完全に分かれ、**型 B** は同型:

    V = [(x0, a, 0), (x1, 0, 0), (x2, b, 0)]     x0 < x1 < x2、b ≤ a、**行 2 は全部 0**

⟹ ★ 私の表を当てる。まず「ブロッカー ⟹ 錐の外」を出す。 -/

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


/-! ### 50.1 ★★★★★★★ **行 2 ≡ 0 なら接頭辞つきでも無料**

`mTower_mem_of_zeroRow2`（`L105Cap:5781`）の中身を読んだら、機構は 2 行だった:

    行 2 ≡ 0 ⟹ `Wself` に入る（`zeroRow2_mem_Wself`、`Wtower2:3011`）
    ＋ 根の `lev ≤ u`（`mem_Wself_iff`、`Wtower2:2990`）

⟹ ★ **どちらも接頭辞を付けても壊れない** ⟹ **接頭辞つきの版がそのまま出る**。 -/

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


/-! ## 51. ★★★★★★★ (W8) L3 の問い「窓に錐の外の列はどこから来るのか」に式で答える

L3 の `TowerP''` は **`hnbQ`（全列）**を運んでいる。⟹ `hnbQ` ⟹ **`Q` の全列が根の錐の中**
（`not_le1_zero_iff`、`L105Cap:7149`）⟹ ★ 塔のどの列も `Lift1` で `+e*k` される。

⟹ ★★ そして `j ≥ 1` の段では **親も的も同じブロックの中**（`parent_bound_pos`）。
⟹ ⟹ ★★★ **`e*n` が両辺で消える** ⟹ **`hnbQ(V)` は `n` に依らない**。

⟹ ⟹ ⟹ ★ ですから「錐の外の列がどこから来るか」の答えは:
**`hnbQ(Q)` は**根**についての条件だが、窓の根は**内部の列 `p`** だから。**
`hnbQ(Q)` は `Q[p]` と `Q[x]`（`p < x`）の大小について**何も言わない**。 -/

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


/-! ## 52. ★★★★★★★ (W6) 「ブロック孤児 ⟹ 塔孤児」の機構

`no_nextR_srow_cross` を **`A := mTower Q d e n`、`T := ブロックの接頭辞`** に当てる。
⟹ ★ L3 の §232.2 の教訓に従い、**当てたあとに前提の強さを確かめる**。

    hmin(ブロック) … `entry (block) 0 l = entry Q 0 l + d*n` ⟹ ★ **`hr0` そのもの**（`n` 非依存）
    hz0(ブロック)  … 行 2 は `shiftr01`/`Lift1` で不変 ⟹ ★ **`hz0` そのもの**
    hnb(ブロック)  … `entry (block) 1 l = entry Q 1 l + (if le1 Q 0 l then e*n else 0)`
                    根は `entry Q 1 0 + e*n`
      ⟹ ⛔ 錐の**外**なら `entry Q 1 0 + e*n < entry Q 1 l` ＝ **`n` で強くなる**（L3 の指摘）
      ⟹ ★★★ ですが **`hnbQ` の下では全列が錐の中**（`le1_all_of_hnbQ`）
      ⟹ ⟹ **`e*n` が両辺で消える** ⟹ ★ **`hnbQ` そのもの**（`n` 非依存）

⟹ ★★★ **3 本とも `TowerP''` の中身と同じ強さ**。⟹ **壁の高さの問題は `hnbQ` が消している**。 -/

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


/-! ## 53. ★★★★★★★ (W9) `hlocQ` —— **`hcls` が「危ない 1 マス」をちょうど禁じる**

L3 の `hlocQ` の第 3 条件 `hcls : le1 Q 0 y → le1 Q 0 j` は、
私の 4 通りの表の **「証人が錐の中・的が錐の外」＝ `n` 依存の 1 マス**をちょうど除く。

| 証人 `y` | 的 `j` | ブロックでの比較 |
|---|---|---|
| 錐の中 | 錐の中 | 両辺 `+e*n` ⟹ ★ **`n` が消える** |
| 錐の外 | 錐の中 | 右辺だけ `+e*n` ⟹ ★ **緩む** |
| 錐の外 | 錐の外 | 両辺そのまま ⟹ ★ **`n` が消える** |
| **錐の中** | **錐の外** | ⛔ `entry Q 1 y + e*n < entry Q 1 j` ＝ **`n` 依存** ← `hcls` が禁じる |

⟹ ★★★ ですから **`hcls` の下では `n`・`e` が完全に消える**。 -/

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


/-! ### 53.1 ★★★ (W9c) **証人が窓に残るか** —— 窓は `drop` ＋ `take`

窓 `wnd P B j p = ((P ++ B.take (j+1)).drop (P.length + p)).take (j - p)`。
⟹ ★ `take` 側は `Wset.entry_take` がある。⟹ `drop` 側を作る。 -/

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


/-! ## 54. ★★★★★★★ (W12b) **窓の根は全内部列の `le0` 祖先**

`hr0_wnd`（窓の根が行 0 で狭義最浅、L3 の §221 で**無料**）だけから出る:

    ★ `nextrel0` の親は必ず窓の中（最小性に `x := p` を入れて殴る）
    ★★ しかも **根 `p` 自身が全内部列の `le0` 祖先**（鎖が `p` まで降りる）

⟹ ⟹ ★★★ **`le0` の祖先の鎖は、`p` に着くまで窓の外に出ない。** -/

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


/-! ## 55. ★★★★★★★ **窓（連続部分列）は `nextrel0`・`nextrel1`・`le0` を全部保つ** -/

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


/-! ## 56. ★★★★ (W15) **行 0 は `hr0` だけで封じられる**（`0 < d` も `hnb` も不要）

`nextrel0_src_ge_of_shallow` を **`p := ブロックの根の位置`** に当てる。
⟹ `hshallow` は「ブロックの根がそれ以降の全列より行 0 で狭義に浅い」＝ **`hr0` そのもの**
（ブロックの行 0 は `entry Q 0 x + d*n` で `+d*n` は一様）。

⟹ ★★ **接頭辞も塔も、ブロックの `j` 列目に行 0 の親を供給できない。**
⟹ ⟹ ★ 前提は `hr0` だけ。**`0 < d` も `hnb` も要らない。** -/

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


/-! ## 57. ★★★★★★ 行 2 の壁を **「的の `le1` 祖先」**に縮める -/

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


/-! ## 58. ★★★★★★★ **行 2 の `hanc` は「的が錐の中」1 本に落ちる**

`nextrel1` の始点も**一意**（`nextrel0` と同じ、最小性から）。
⟹ ★ ですから `m` に入る `le1` の鎖は**一意** ⟹ 的の祖先は全部「根からの鎖」の上。
⟹ ⟹ ★★ **`le1 T 0 m`（的が根の錐の中）なら、非根の祖先は全部
`entry T 1 0 < entry T 1 m'`**（`le1` で行 1 は狭義増加）。
⟹ ⟹ ⟹ ★★★ **`hanc` が「的が錐の中」1 本に縮む** ⟹ **行 1 と同じ条件**。 -/

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


/-! ## 59. ★★★★★★ **親の始点はブロックの中**（行 1・行 2 版）

行 0 は `no_row0_parent_from_before_block`（`hr0` だけ、§312）。
⟹ ★ 行 1・行 2 も、**的が「錐の中」なら**同じ形で出る:
`nextrel1` の最小性を **`j := p`（ブロックの根）**に当てる。
（`le0 M p b` は `le0_root_of_shallow`（§310）から**無料**。） -/

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


/-! ## 60. ★★★★★★★ **`hcls` は障害にならない** —— 証人を「本当の親」に取れば自動

R2 の (COMP-b)「クラス条件だけが合わないのは **0 件**」の理由:

    ★ 証人を **`nextrel1` の親**に取ると、`hcls` は**推移律で自動**
      （`le1 V 0 y` ∧ `le1 V y t` ⟹ `le1 V 0 t`）
    ★★ 逆に、証人があれば **`nextrel1` の親も存在する**（`le0` 祖先の中の最大元）

⟹ ⟹ ★★★ **`hlocQ` の行 1 の成分 ⟺ `hasParent V 1 t`** ⟹ **`hcls` は自由**。 -/

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


/-! ## 61. ★★★★★★★ (W18) **`hlocQ` ＋「行 1 が 0 の列が無い」⟹ 全列が錐の中**

`hlocQ` の行 1 の成分は `hasParent V 1 t`（§316）⟹ **`nextrel1` の親が存在**。
⟹ ★ 鎖を下へたどると、**行 1 が 0 の列**（そこでは `hlocQ` の前件が偽）か**根**で止まる。
⟹ ⟹ ★★ ですから **「行 1 が 0 の列が無い」なら鎖は必ず根に届く** ⟹ **全列が錐の中**。

⟹ ★★★ R2 の「破れの形はブロッカー ＝ **行 1 が 0 の列**」「それを封じる前提があれば埋まる」
と**完全に一致**する。 -/

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


/-! ## 62. ★★★★★★★ (NZ) **`hnz` は無条件で遺伝する**

`hnz`（行 1 が 0 の非根の列が無い）は **個々の成分の下限**であって、
`hnbQ` / `h1out` のような**根との比較ではない**。
⟹ ★★ ですから **窓を取っても、塔に積んでも、そのまま生き残る**。
⟹ ⟹ ★★★ **根が変わっても壊れない** ——これが `hnbQ` との決定的な違い。 -/

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


/-! ## 63. ★★★ (W19) **「行 1 = 0 の列」は自動的に錐の外**、そしてブロックでも `Q` でも同じ

team-lead の紙の上の議論を Lean にする。 -/

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


/-! ## 64. ★★★★★ `hlocQ` の行 1 成分は **ブロッカーでしか破れない**

`hr0`（根が行 0 で狭義最浅）の下では **根は全列の `le0` 祖先**（§310）。
⟹ ★ ですから的が**非ブロッカー**（`entry V 1 0 < entry V 1 t`）なら、根が証人の候補になり、
`nextrel1_of_witness` で**本当の親**が取れて、`witness_of_nextrel1` で `hcls` も自動。
⟹ ⟹ ★★ **`hlocQ` の行 1 成分は、的がブロッカーのときしか破れない。**

⚠ 逆は成り立たない（ブロッカーでも、もっと行 1 の小さい証人があれば通る）
⟹ ★ ですから `hlocQ` は `hnbQ` より**真に弱い**。⟹ L3 の設計どおり。 -/

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


/-! ## 65. ⛔ (NZ2) **`hnz` は「錐の遺伝」を救いません**（反例、緑）

team-lead の訂正 2 が正しい: **「全列が錐の中」（`le1 V 0 t`）は根との比較**。
⟹ ★ 私の教訓（「根との比較は遺伝しない」）を**自分の提案に当てる**と、遺伝しないはず。
⟹ ⟹ ★★ そして `hnz` は**成分の下限**しか言わないので、**根との比較を一切制御できない**。

具体的な反例（下、緑）:

    V = [(1,5,0), (2,3,0)]
    `hnz V` … 行 1 は 5 と 3 ⟹ どちらも正 ✅
    ⛔ `le1 V 0 1` … 的の行 1 = 3 ≤ 5 = 根の行 1 ⟹ **ブロッカー** ⟹ **錐の外**

⟹ ★ そして この `V` は `Q = [(0,1,0),(1,5,0),(2,3,0)]` の `p = 1` からの窓で、
   `Q` の側では列 2 は**錐の中**（`nextrel1 Q 0 2`: `1 < 3`、`le0` ✓、
   最小性は `j = 1` で `3 ≤ 5` ✓）。⟹ ⟹ **`Q` で錐の中、`V` で錐の外**。
   （`Q` 側は紙の上。`V` 側は下で緑。） -/

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


/-! ## 66. ★★★★★★★ (W21) **窓は `W` の元です**（1 行、緑）

索引を引いたら**両方ありました**（今日 9 回目の「既にありました」）:

    `Wset.W_take`   （`Wset:2120`）… `M ∈ W u → M.take k ∈ W u`
    `W_drop`（`Wtower2:2870`）… `M ∈ W u → M.drop j ∈ W (lev M j)`

⟹ ★★ 窓は `drop` ＋ `take` なので、**合成するだけ**。
⟹ ⟹ ★★★ **`W u` は連続部分列で閉じています**（水準は `lev M p` に変わる）。 -/

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


/-! ## 67. ★★★★★★★ **C4** —— R2 の新条件（「行 1 は `le0` の向きに狭義増加」）

    C4 Q :⟺ ∀ y j, y < j → j < |Q| → le0 Q y j → entry Q 1 y < entry Q 1 j

★ これは私の型の分類でいうと **「`le0` の親との比較」**:

    「根との比較」…………… ⛔ 遺伝しない（根が変わるから）
    「成分の下限」…………… ✅ 遺伝する（`hnz`）
    ★★★ 「`le0` の親との比較」… ✅ **遺伝する**（親子関係が窓で変わらないから）← **C4** -/

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


/-! ## 68. ⛔⛔ **(C4-W1) `W ⟹ C4` は偽です**（反例、緑）

`Aop` の帰納法に入る前に、**反例を先に探しました**（教訓 45）。⟹ ★ すぐ出ました。

    M = [(0,0,0), (1,0,0)]
    ★ 行 2 が全部 0 ⟹ `zeroRow2_mem_Wself` で `Wself`、`lev M 0 = 0` ⟹ **∀ u, M ∈ W u**
    ⛔ C4: `le0 M 0 1` は成り立つ（行 0 が 0 < 1、最小性は空虚）が
       **`entry M 1 0 = 0` と `entry M 1 1 = 0`** ⟹ `0 < 0` は偽 ⟹ **C4 M は偽**

⟹ ★★★ ですから **「`W` ⟹ C4」は偽**。⟹ ⟹ **`Aop` の帰納法に入る必要はありません**。 -/

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


/-! ## 69. ★★★★★ (H-ORPH2) 行 2 の壁 —— **錐の外では原理的に立たない**（機構）

`hz0`（`Q` の根の行 2 が 0）より、**塔の全ブロックの根は行 2 = 0**（下、緑）。
⟹ ★ L3 の `hasParent_two_iff_of_z1`（`hz1` の下で
`hasParent M 2 j ↔ ∃ y < j, le1 M y j ∧ entry M 2 y = 0`）と合わせると:

    **`le1` の鎖が前のブロックの根に届けば、その根が行 2 の親になってしまう**

⟹ ⟹ ★★ ですから行 2 の壁に要るのは「**鎖が前のブロックに戻らない**」ことで、
それは私の `hanc`（＝ **的が錐の中**）と**同値**（私の §316.2）。
⟹ ⟹ ⟹ ⛔ **錐の外では原理的に立ちません。** -/

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


/-! ## 70. ⛔⛔⛔ (H-KILL) **`W ∧ hnz ⟹ C4` も偽**（留保なしの反証、緑）

R2 の 2 手の鎖の終点 `[(0,0,0),(1,1,0),(2,1,0)]` は

    行 2 が全部 0 ⟹ `zeroRow2_mem_Wself` ＋ `lev = 0` ⟹ **∀ u, ∈ W u**（`D_1 ∈ W u` は不要）
    行 1 = 0, 1, 1 ⟹ 非根は 1 と 1 ⟹ **`hnz` は真**
    ⛔ `le0` は 1→2（隣接、最小性は空虚）で、行 1 は **1 と 1** ⟹ **C4 は偽**

⟹ ★★★ ですから **C4 の道は留保なしで終わり**です。 -/

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


/-! ## 71. ★★★★★★ (H-ORPH2) **錐の中なら、接頭辞は `srow` の行で親を供給しない** -/

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


/-! ### 71.1 ★ L3 の `hasParent_peel_of_noCross` に直に嵌まる形 -/

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


/-! ## 72. ★★★★★ (W23) **錐の外の的の構造**

R2（シート、分母 353）: **孤児の `srow` は 100% が 1**。⟹ ★ ですから行 1 の孤児だけを見る。

    (1) `T` の中で行 1 の孤児 ⟹ **的は `T` の根に対してブロッカー**
        ⟹ ★ 私の §320 を `hasParent` の形に言い換えたもの
    (2) ⟹ 接頭辞から行 1 の親が来るなら、**その親の行 1 は `T` の根の行 1 より小さい** -/

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


/-! ### 72.1 ★★★★★★ (W23)(2) を **完全な特徴づけ**にする

`T` の中で行 1 の孤児 ⟹ **`T` の中の `le0` 祖先は全部「的以上」**（`nextrel1_of_witness` の対偶）。
⟹ ★ ですから `nextrel1` の最小性のうち **`T` 側は自動で満たされ**、
残るのは**接頭辞側だけ**。⟹ ⟹ **接頭辞の親の存在が、単純な条件と同値**になる。 -/

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


/-! ## 73. ★★★★★★★ (W24) **`entry T 1 0 = 0` だけで、行 1 の孤児の枝が空になる**

team-lead の 1 行（`0 ≤ 何でも` なので `rsum1` は自動）から、**もっと強い**ことが出る:

    私の `row1_orphan_is_blocker`: 孤児 ⟹ `entry T 1 m ≤ entry T 1 0`
    ⟹ ★ 根の行 1 = 0 なら **`entry T 1 m = 0`** ⟹ ⛔ `srow = 1`（行 1 が正）と矛盾
    ⟹ ⟹ ★★★★ **行 1 の孤児はそもそも存在しない** ⟹ **壁を立てるまでもない** -/

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


/-! ## 74. ★★★★★★ (W25) **`le0` の道は必ず `p` を通る**（一般形）

`p` より後ろの列が全部「行 0 で `p` より深い」とき（＝ ブロックの根の状況）、
`p` より前から `p` より後ろへの `le0` の道は、**必ず `p` を経由する**。
⟹ ★ 私の `nextrel0_src_ge_of_shallow`（親は必ず `p` 以降）から、鎖をたどるだけ。 -/

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


/-! ## 75. ⛔⛔ (W25) の帰結: **接頭辞に「行 1 = 0 の最浅の列」があると、必ず親ができる**

(W25) で証人を「`T` の根の `le0` 祖先」に絞ったが、⟹ ⛔ **全体の根（添字 0）は常にその鎖の上**
（`le0_root_of_shallow` を `p := 0` に当てるだけ）。
⟹ ★ そして **全体の根の行 1 が 0** なら、⟹ ⟹ ★★ **それがそのまま証人**になる。

⟹ ⟹ ★★★ ですから **行 1 の孤児がある限り、接頭辞は必ず親を供給します**。
⟹ ⟹ ⟹ ⛔ **`OrphOK` の行 1 は「証明できていない」ではなく「偽」**です（この状況では）。 -/

/-- ⛔⛔ **全体の根が行 1 = 0 で最浅なら、行 1 の孤児には必ず接頭辞から親が来る**。 -/
theorem prefix_parent_of_low_root {A T : TrioSeq} {m : ℕ}
    (hr0M : ∀ l, 0 < l → l < (A ++ T).length → entry (A ++ T) 0 0 < entry (A ++ T) 0 l)
    (hA : 0 < A.length) (hroot1 : entry (A ++ T) 1 0 = 0)
    (hm : m < T.length) (hm0 : 0 < m) (hnp : ¬ hasParent T 1 m)
    (hpos : 0 < entry T 1 m) :
    ∃ c, c < A.length ∧ nextrel1 (A ++ T) c (A.length + m) := by
  have hMlen : 0 < (A ++ T).length := by rw [List.length_append]; omega
  have htgt : A.length + m < (A ++ T).length := by rw [List.length_append]; omega
  refine (prefix_parent_iff_of_orphan hm hnp).mpr ⟨0, hA, ?_, ?_⟩
  · exact le0_root_of_shallow hMlen hr0M (A.length + m) (by omega) htgt
  · rw [hroot1]; omega

/-- ⛔⛔⛔ ⟹ **`OrphOK` の行 1 は、この状況では偽**。 -/
theorem orphOK_row1_fails_of_low_root {A T : TrioSeq} {m : ℕ}
    (hr0M : ∀ l, 0 < l → l < (A ++ T).length → entry (A ++ T) 0 0 < entry (A ++ T) 0 l)
    (hA : 0 < A.length) (hroot1 : entry (A ++ T) 1 0 = 0)
    (hm : m < T.length) (hm0 : 0 < m) (hnp : ¬ hasParent T 1 m)
    (hpos : 0 < entry T 1 m) :
    ¬ (∀ c, c < A.length → ¬ nextrel1 (A ++ T) c (A.length + m)) := by
  intro h
  obtain ⟨c, hc, hcn⟩ := prefix_parent_of_low_root hr0M hA hroot1 hm hm0 hnp hpos
  exact h c hc hcn


/-! ## 76. ★★★★★★★ **`amin` で行 1 の親の存在が完全に特徴づけられる**

索引を引いたら **`amin`（`Cgraft:848`）があった**（今日 10 回目の「既にありました」）:

    `amin A j` ＝ **行 0 祖先鎖（自身を含む）の行 1 値の最小値**
    `amin_le`  … 祖先なら `amin ≤ その列の行 1`
    `amin_mem` … 最小値を実現する祖先が存在する

⟹ ★★★ ですから **`hasParent M 1 j ⟺ amin M j < entry M 1 j`**。
⟹ ⟹ ★ 量化子なし。しかも **`hr0` すら要りません**。 -/

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
    obtain ⟨y', hy'⟩ := nextrel1_of_witness hylt hle0 (by omega)
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


/-! ## 77. ⛔ (W27) **正規化版 `R1<=R0` は「弱め」ではありません。むしろ強い**

R2 の候補: **`∀ i, entry T 1 i ≤ entry T 0 i - entry T 0 0`**（正規化した `R1<=R0`）。
⟹ ⛔ **`i = 0` を入れると `entry T 1 0 ≤ 0`** ⟹ **`entry T 1 0 = 0`**。
⟹ ⟹ ★★ ですから **私の前提 `entry T 1 0 = 0` を含意します** ⟹ **弱めではなく強めです**。

⚠ そして実測の数字も一致します: **正規化版の窓への遺伝 19.0409%** ＝
**`entry Q 1 0 = 0` の窓での率 19.04%**。⟹ ★ **同じ条件**を測っていたことになります。 -/

/-- ⛔ **正規化版 `R1<=R0` ⟹ `entry T 1 0 = 0`**（`i = 0` を入れるだけ）。 -/
theorem root_row1_zero_of_normR1R0 {T : TrioSeq} (hT : 0 < T.length)
    (h : ∀ i, i < T.length → entry T 1 i ≤ entry T 0 i - entry T 0 0) :
    entry T 1 0 = 0 := by
  have h0 := h 0 hT
  omega


/-! ## 78. ★★★★★★ (W33) **`amin` の極値の正体**

R2 の保存量「`amin` の最大・最小が `oper` 不変」の**正体を先に同定する**:

    ★ **最大** ＝ **根の行 1**（`amin M 0 = entry M 1 0`、かつ `hr0` の下で全部それ以下）
    ★ **最小** ＝ **行 1 の大域最小**（全列は自分の祖先なので）

⟹ ★★ ですから保存量は「根の行 1」と「行 1 の大域最小」です。 -/

/-- ★★★ **根の `amin` は根の行 1**（根の祖先は自分だけ）。 -/
theorem amin_root {M : TrioSeq} : amin M 0 = entry M 1 0 := by
  obtain ⟨y, hrt, heq⟩ := amin_mem M 0
  have hy : y = 0 := by have := rtg0_index_le hrt; omega
  rw [← heq, hy]

/-- ★★★★ **`hr0` の下では `amin` の最大は根の行 1**。 -/
theorem amin_le_root_of_shallow {M : TrioSeq} (hM : 0 < M.length)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    {j : ℕ} (hj : j < M.length) : amin M j ≤ entry M 1 0 := by
  rcases Nat.eq_zero_or_pos j with h0 | hp
  · rw [h0, amin_root]
  · have hle0 := le0_root_of_shallow hM hr0 j hp hj
    have := amin_mono (A := M) (j := j) (y := 0) hle0.2.2
    rw [amin_root] at this
    exact this

/-- ★★★★ **行 1 の下限は `amin` にそのまま移る**（＝ `amin` の最小は行 1 の大域最小）。 -/
theorem amin_ge_of_row1_ge {M : TrioSeq} {c : ℕ}
    (h : ∀ i, i < M.length → c ≤ entry M 1 i)
    {j : ℕ} (hj : j < M.length) : c ≤ amin M j := by
  obtain ⟨y, hrt, heq⟩ := amin_mem M j
  have hy : y ≤ j := rtg0_index_le hrt
  rw [← heq]
  exact h y (by omega)

/-- ★★★★★ ⟹ **`amin` は「行 1 の大域最小」と「根の行 1」の間に閉じ込められる**。 -/
theorem amin_bounds {M : TrioSeq} {c : ℕ} (hM : 0 < M.length)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlow : ∀ i, i < M.length → c ≤ entry M 1 i)
    {j : ℕ} (hj : j < M.length) : c ≤ amin M j ∧ amin M j ≤ entry M 1 0 :=
  ⟨amin_ge_of_row1_ge hlow hj, amin_le_root_of_shallow hM hr0 hj⟩


/-! ### 78.1 ★★★★★★ ⟹ **`amin` の最大は `oper` で不変**（＝ R2 の保存量の max 側）

索引に **`oper_headD`（`Wset:1509`）**があった（今日 12 回目）:
**`oper` は先頭の列をそのまま保つ**。⟹ ★ 行 1 版を作れば max 側が閉じる。 -/

theorem entry_one_headD (X : TrioSeq) : entry X 1 0 = (X.headD (0, 0, 0)).2.1 := by
  cases X <;> simp [entry]

/-- ★★★ **`oper` は先頭列の行 1 を保つ**。 -/
theorem oper_head_row1 {B : TrioSeq} {n : ℕ} (hn : 1 ≤ n) :
    entry (B⟦n⟧) 1 0 = entry B 1 0 := by
  by_cases hL : 1 < B.length
  · rw [entry_one_headD, entry_one_headD, oper_headD B hL hn]
  · rw [oper_eq_self_of_short n (by omega)]

/-- ★★★★★★ **(W33) max 側: `amin` の最大は `oper` で不変**。
（`hr0` の下で最大 ＝ 根の行 1、そして `oper` は先頭列を保つ。） -/
theorem amin_max_oper_invariant {B : TrioSeq} {n : ℕ} (hn : 1 ≤ n)
    (hr0' : ∀ l, 0 < l → l < (B⟦n⟧).length → entry (B⟦n⟧) 0 0 < entry (B⟦n⟧) 0 l)
    (hB' : 0 < (B⟦n⟧).length) :
    (∀ j, j < (B⟦n⟧).length → amin (B⟦n⟧) j ≤ amin B 0) ∧
      amin (B⟦n⟧) 0 = amin B 0 := by
  constructor
  · intro j hj
    rw [amin_root]
    have := amin_le_root_of_shallow hB' hr0' hj
    rw [oper_head_row1 hn] at this
    exact this
  · rw [amin_root, amin_root, oper_head_row1 hn]


/-! ## 79. ★★★★★★★ (W35) **行 2 が正の列の個数**は、窓で減る

`d = wd0`・`e = wd1` は「今の末尾列と親」から作られ、**前の `d`・`e` と漸化式を持たない**
⟹ ⛔ そのままでは減る量にならない。

⟹ ★ ですが **`e > 0` には `srow = 2` が要る**（私の §300）。⟹ ⟹ ★★ そして:

    ★ **行 2 は `Lift1` でも `shiftr01` でも変わらない**（`entry2_mTower_block`）
    ★★ **窓は連続部分列** ⟹ 行 2 の値は増えない
    ★★★ **`srow = 2` の段では、行 2 が正の末尾列が窓から外れる**
    ⟹ ⟹ ★★★★ **`srow = 2` の段ごとに「行 2 が正の列の個数」が狭義に減る**
    ⟹ ⟹ ⟹ ★ ですから **`e > 0` は有限回しか起きない**。 -/

/-- 行 2 が正の列の個数。 -/
def row2pos (M : TrioSeq) : ℕ := M.countP (fun p => 0 < p.2.2)

/-- ★★★ **連続部分列で増えない**（`Sublist` の単調性）。 -/
theorem row2pos_sublist_le {M N : TrioSeq} (h : M.Sublist N) : row2pos M ≤ row2pos N :=
  h.countP_le

/-- ★★★ `take` で増えない。 -/
theorem row2pos_take_le (M : TrioSeq) (k : ℕ) : row2pos (M.take k) ≤ row2pos M :=
  row2pos_sublist_le (List.take_sublist k M)

/-- ★★★ `drop` で増えない。 -/
theorem row2pos_drop_le (M : TrioSeq) (p : ℕ) : row2pos (M.drop p) ≤ row2pos M :=
  row2pos_sublist_le (List.drop_sublist p M)

/-- ★★★ 窓（`drop` ＋ `take`）で増えない。 -/
theorem row2pos_window_le (M : TrioSeq) (p k : ℕ) :
    row2pos ((M.drop p).take k) ≤ row2pos M :=
  le_trans (row2pos_take_le _ k) (row2pos_drop_le M p)

/-- ★★★★★ **行 2 が正の末尾列を落とすと狭義に減る**。 -/
theorem row2pos_dropLast_lt {M : TrioSeq} {q : ℕ × ℕ × ℕ} (hq : 0 < q.2.2) :
    row2pos M < row2pos (M ++ [q]) := by
  unfold row2pos
  rw [List.countP_append]
  have h1 : List.countP (fun p => decide (0 < p.2.2)) [q] = 1 := by
    simp [hq]
  omega


/-! ### 79.1 ⚠ (W35') **塔では減りません**（`Q` が第 0 ブロックそのものなので）

`mTower Q d e n` の第 0 ブロックは `Lift1 (shiftr01 (d*0) 0 Q) (e*0) = Lift1 Q 0 = Q`。
⟹ ★ ですから **`Q` は塔の接頭辞** ⟹ ⟹ **`row2pos Q ≤ row2pos (mTower Q d e n)`**。

⚠ **正確な `n` 倍の式は書けませんでした**（`Lift1` が `(range |X|).map` の形で、
`countP` を添字の形に直す補題が要り、30 分に収まりませんでした）。
⟹ ★ ですが **要点（塔で減らない）は下で足ります**。 -/

/-- 第 0 ブロックは `Q` そのもの。 -/
theorem mTower_block_zero (Q : TrioSeq) (d e : ℕ) :
    Lift1 (shiftr01 (d * 0) 0 Q) (e * 0) = Q := by
  simp only [Nat.mul_zero, Lift1_zero]
  exact h12_shiftr01_zero_zero Q


/-! ## 80. ★★★★★★ (W40) **行 0 の親なら `|V| < |Q|`**（`hr0` だけ）

L3 の `hsnoc_gen`（`8bf7990`）で残った義務 (O-B) は **`|V| < |Q|`**。
⟹ ★ 行 0 は私の `no_row0_parent_from_before_block`（`hr0` だけ、緑）の**3 行の系**:

    親 `c ≥ (A ++ mTower Q d e n).length`
    ⟹ **`|V| = (A ++ mTower).length + j - c ≤ j < |Q|`** ✓ -/

theorem window_lt_of_row0_parent {A Q : TrioSeq} {d e n j c : ℕ}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hj : j < Q.length) (hj0 : 0 < j)
    (h : nextrel0 (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      c ((A ++ mTower Q d e n).length + j)) :
    (A ++ mTower Q d e n).length + j - c < Q.length := by
  rcases Nat.lt_or_ge c (A ++ mTower Q d e n).length with hc | hc
  · exact absurd h (no_row0_parent_from_before_block hr0 hj hj0 hc)
  · omega

/-- ★★★ 同じことを「親の位置」の形で。 -/
theorem row0_parent_ge_block {A Q : TrioSeq} {d e n j c : ℕ}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hj : j < Q.length) (hj0 : 0 < j)
    (h : nextrel0 (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      c ((A ++ mTower Q d e n).length + j)) :
    (A ++ mTower Q d e n).length ≤ c := by
  by_contra hc
  push Not at hc
  exact absurd h (no_row0_parent_from_before_block hr0 hj hj0 hc)


/-! ## 81. ★★★★★★ 行 1（錐の中）: **親は今のブロックの中**

的が `Q` の錐の中なら、**錐の鎖の最後の 1 歩 `nextrel1 Q y j`** が
**今のブロックの中の証人 `(n, y)`** をくれる。
⟹ ★ `nextrel1` の最小性をそこに当てると、**親は `n|Q| + y` 以降**。
⟹ ⟹ ★★ **前のブロックにも接頭辞にも行きません**（`hr0` も `hnbQ` も不要）。 -/

/-- `le0` はブロックの中で `Q` と同型（`nextrel0_mTower_intra_block` の鎖版）。 -/
theorem rtg0_mTower_intra_block (Q : TrioSeq) {d e n k : ℕ} (hk : k < n)
    {a b : ℕ} (_ha : a < Q.length) (hb : b < Q.length)
    (h : Relation.ReflTransGen (nextrel0 Q) a b) :
    Relation.ReflTransGen (nextrel0 (mTower Q d e n)) (k * Q.length + a) (k * Q.length + b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c b hac hcb ih =>
      have hc : c < Q.length := hcb.1
      exact (ih hc).tail ((nextrel0_mTower_intra_block Q hk hc hb).mpr hcb)

open Classical in
/-- ★★★★★★ **行 1 の親は「錐の鎖の最後の 1 歩」以降**。
⟹ ★ 仮定は `nextrel1 Q y j` **だけ**（`hr0` も `hnbQ` も `0 < e` も要りません）。
⟹ ⟹ ★★ **証人が錐の中なら的も錐の中**（鎖が伸びる）⟹ ★ **両方が `+e*n` で相殺**、
証人が錐の外なら **持ち上げが無いぶん低い** ⟹ ★ **どちらでも最小性に反します**。 -/
theorem nextrel1_src_ge_of_cone_witness (Q : TrioSeq)
    {d e n N j y c : ℕ} (hn : n < N) (hj : j < Q.length) (hy : nextrel1 Q y j)
    (h : nextrel1 (mTower Q d e N) c (n * Q.length + j)) :
    n * Q.length + y ≤ c := by
  have hylt : y < j := hy.2.2.1
  have hyQ : y < Q.length := by omega
  have hlt : entry Q 1 y < entry Q 1 j := hy.2.2.2.1
  have hle0 : le0 (mTower Q d e N) (n * Q.length + y) (n * Q.length + j) := by
    have hlen : (mTower Q d e N).length = N * Q.length := mTower_length Q d e N
    have hNq : (n + 1) * Q.length ≤ N * Q.length := Nat.mul_le_mul_right _ (by omega)
    have hsk : (n + 1) * Q.length = n * Q.length + Q.length := Nat.succ_mul n Q.length
    exact ⟨by omega, by omega,
      rtg0_mTower_intra_block Q hn hyQ hj hy.2.2.2.2.1.2.2⟩
  by_contra hc
  push Not at hc
  have hmin := h.2.2.2.2.2 (n * Q.length + y) ⟨by omega, hle0⟩
  rw [entry1_mTower_block_formula Q hn hj, entry1_mTower_block_formula Q hn hyQ] at hmin
  by_cases hcy : le1 Q 0 y
  · have hcj : le1 Q 0 j := ⟨by omega, hj, hcy.2.2.tail hy⟩
    rw [if_pos hcy, if_pos hcj] at hmin; omega
  · rw [if_neg hcy] at hmin
    split_ifs at hmin <;> omega

/-- ★★★★★ ⟹ **親は今のブロックの中**（系）。接頭辞にも前のブロックにも行きません。 -/
theorem nextrel1_src_in_block_of_cone (Q : TrioSeq)
    {d e n N j y c : ℕ} (hn : n < N) (hj : j < Q.length) (hy : nextrel1 Q y j)
    (h : nextrel1 (mTower Q d e N) c (n * Q.length + j)) :
    n * Q.length ≤ c :=
  le_trans (by omega) (nextrel1_src_ge_of_cone_witness Q hn hj hy h)


/-! ## 82. ★★★★★★ 接頭辞つきの行 1 —— **`MeasOK` の行 1**（錐の証人があるとき）

`snoc` の形 `A ++ mTower Q d e n ++ (最後のブロック).take (j+1)` で、
**`j` が `Q` の中で行 1 の親を持つ**なら ⟹ ★ **親は最後のブロックの中**。
⟹ ⟹ ★★ **`|T| - 1 - 親 ≤ j < |Q|`** ＝ **`MeasOK`**。 -/

open Classical in
/-- 最後の（部分）ブロックの行 1 の値。 -/
theorem entry1_prefixTake (A Q : TrioSeq) {d e n j i : ℕ} (hj : j < Q.length) (hi : i < j + 1) :
    entry (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 1
        ((A ++ mTower Q d e n).length + i)
      = entry Q 1 i + (if le1 Q 0 i then e * n else 0) := by
  rw [entry_append_right, Wset.entry_take hi,
    Wset.entry1_Lift1 (by rw [shiftr01_length]; omega), entry1_shiftr01]
  congr 1
  by_cases hc : le1 Q 0 i
  · rw [if_pos hc, if_pos ((le1_shiftr01 (d0 := d * n)).mpr hc)]
  · rw [if_neg hc, if_neg (fun hx => hc ((le1_shiftr01 (d0 := d * n)).mp hx))]

/-- ★★★★★★ **`MeasOK` の行 1**: `j` が `Q` の中で行 1 の親 `y` を持つなら、
`snoc` の形での行 1 の親は **`|A| + n|Q| + y` 以降**。⟹ ★ **接頭酸にも前のブロックにも行きません**。
⟹ ⚠ 仮定は `nextrel1 Q y j` **だけ**（`hr0` も `hnbQ` も `0 < e` も `0 < d` も不要）。 -/
theorem prefixTake_nextrel1_src_ge {A Q : TrioSeq} {d e n j y c : ℕ}
    (hj : j < Q.length) (hy : nextrel1 Q y j)
    (h : nextrel1 (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        c ((A ++ mTower Q d e n).length + j)) :
    (A ++ mTower Q d e n).length + y ≤ c := by
  have hylt : y < j := hy.2.2.1
  have hlt : entry Q 1 y < entry Q 1 j := hy.2.2.2.1
  have hle0Q : le0 Q y j := hy.2.2.2.2.1
  have hle0 : le0 (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      ((A ++ mTower Q d e n).length + y) ((A ++ mTower Q d e n).length + j) := by
    refine le0_append_right_of _ _ ?_
    rw [Wset.le0_take (by rw [Lift1_length, shiftr01_length]; omega) (by omega),
      Wset.le0_Lift1, le0_shiftr01]
    exact hle0Q
  by_contra hc
  push Not at hc
  have hmin := h.2.2.2.2.2 ((A ++ mTower Q d e n).length + y) ⟨by omega, hle0⟩
  rw [entry1_prefixTake A Q hj (by omega), entry1_prefixTake A Q hj (by omega)] at hmin
  by_cases hcy : le1 Q 0 y
  · have hcj : le1 Q 0 j := ⟨by omega, hj, hcy.2.2.tail hy⟩
    rw [if_pos hcy, if_pos hcj] at hmin; omega
  · rw [if_neg hcy] at hmin
    split_ifs at hmin <;> omega

/-- ★★★★★★★ ⟹ **`MeasOK` の行 1 そのもの**: 窓が `Q` より真に短い。 -/
theorem window_lt_of_row1_parent {A Q : TrioSeq} {d e n j y c : ℕ}
    (hj : j < Q.length) (hy : nextrel1 Q y j)
    (h : nextrel1 (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        c ((A ++ mTower Q d e n).length + j)) :
    (A ++ mTower Q d e n).length + j - c < Q.length := by
  have := prefixTake_nextrel1_src_ge hj hy h
  omega

/-- ★★★★★ ⟹ **`j` が行 1 の孤児でなければ良い**（`amin` での言い換え）。 -/
theorem window_lt_of_row1_parent' {A Q : TrioSeq} {d e n j c : ℕ}
    (hj : j < Q.length) (hpar : hasParent Q 1 j)
    (h : nextrel1 (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        c ((A ++ mTower Q d e n).length + j)) :
    (A ++ mTower Q d e n).length + j - c < Q.length := by
  obtain ⟨y, hy, -⟩ := hpar
  exact window_lt_of_row1_parent hj (by simpa [nextR] using hy) h


/-! ## 83. ★★★★★★ **`MeasOK` の行 2** —— 行 1 と同じ筋、しかも**もっと簡単**

行 2 の値は `Lift1` でも `shiftr01` でも**動きません**。
⟹ ★ ですから **`if` の場合分けすら要りません**。 -/

/-- 最後の（部分）ブロックの行 2 の値 ＝ `Q` の値そのもの。 -/
theorem entry2_prefixTake (A Q : TrioSeq) {d e n j i : ℕ} (hi : i < j + 1) :
    entry (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 2
        ((A ++ mTower Q d e n).length + i) = entry Q 2 i := by
  rw [entry_append_right, Wset.entry_take hi, Wset.entry2_Lift1, entry2_shiftr01]

/-- ★★★★★★ **`MeasOK` の行 2**: `j` が `Q` の中で行 2 の親 `y` を持つなら、
`snoc` の形での行 2 の親は **`|A| + n|Q| + y` 以降**。⟹ ★ **仮定は `nextrel2 Q y j` だけ**。 -/
theorem prefixTake_nextrel2_src_ge {A Q : TrioSeq} {d e n j y c : ℕ}
    (hj : j < Q.length) (hy : nextrel2 Q y j)
    (h : nextrel2 (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        c ((A ++ mTower Q d e n).length + j)) :
    (A ++ mTower Q d e n).length + y ≤ c := by
  have hylt : y < j := hy.2.2.1
  have hlt : entry Q 2 y < entry Q 2 j := hy.2.2.2.1
  have hle1Q : le1 Q y j := hy.2.2.2.2.1
  have hle1 : le1 (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      ((A ++ mTower Q d e n).length + y) ((A ++ mTower Q d e n).length + j) := by
    refine (le1_append_right _ _ _ _).mpr ?_
    rw [Wset.le1_take (by rw [Lift1_length, shiftr01_length]; omega) (by omega),
      Wset.le1_Lift1, le1_shiftr01]
    exact hle1Q
  by_contra hc
  push Not at hc
  have hmin := h.2.2.2.2.2 ((A ++ mTower Q d e n).length + y) ⟨by omega, hle1⟩
  rw [entry2_prefixTake A Q (by omega), entry2_prefixTake A Q (by omega)] at hmin
  omega

/-- ★★★★★★★ ⟹ **`MeasOK` の行 2 そのもの**: 窓が `Q` より真に短い。 -/
theorem window_lt_of_row2_parent {A Q : TrioSeq} {d e n j y c : ℕ}
    (hj : j < Q.length) (hy : nextrel2 Q y j)
    (h : nextrel2 (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        c ((A ++ mTower Q d e n).length + j)) :
    (A ++ mTower Q d e n).length + j - c < Q.length := by
  have := prefixTake_nextrel2_src_ge hj hy h
  omega

/-- ★★★★★ ⟹ `hasParent` 版。 -/
theorem window_lt_of_row2_parent' {A Q : TrioSeq} {d e n j c : ℕ}
    (hj : j < Q.length) (hpar : hasParent Q 2 j)
    (h : nextrel2 (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        c ((A ++ mTower Q d e n).length + j)) :
    (A ++ mTower Q d e n).length + j - c < Q.length := by
  obtain ⟨y, hy, -⟩ := hpar
  exact window_lt_of_row2_parent hj (by simpa [nextR] using hy) h


/-! ## 84. ★★★★★★★ (W46): **`j = 0` の形 ＝ 1 段高い塔の接頭辞** —— 既に §7 にありました

`mTower_append_take`（§7、`H12Export` に export 済み）の `j = 0` の場合そのものです。
⟹ ★ 接頭辞 `A` つきの形も `take_append_add` で出ます。 -/

/-- ★★★★★★★ **(W46)**: `snoc` の形（`j = 0`）は **1 段高い塔の take**。 -/
theorem mTower_snoc_zero_eq_take (Q : TrioSeq) (d e n : ℕ) :
    mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take 1
      = (mTower Q d e (n + 1)).take (n * Q.length + 1) :=
  mTower_append_take Q d e n 0

/-- ★★★★★★★ **接頭辞つきの (W46)**: `A ++ (1 段高い塔)` の take そのもの。
⟹ ★ ⟹ **`Wset.W_take` がそのまま効きます**（`j = 0` の枝が無料）。 -/
theorem prefix_mTower_snoc_eq_take (A Q : TrioSeq) (d e n j : ℕ) :
    A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)
      = (A ++ mTower Q d e (n + 1)).take (A.length + (n * Q.length + (j + 1))) := by
  rw [List.append_assoc, mTower_append_take, take_append_add]

/-- ★★★★★★★ ⟹ **`j = 0` の枝は `W_take` で無料**。 -/
theorem prefix_mTower_snoc_mem_W {u : ℕ} {A Q : TrioSeq} {d e n j : ℕ}
    (h : A ++ mTower Q d e (n + 1) ∈ W u) :
    A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1) ∈ W u := by
  rw [prefix_mTower_snoc_eq_take]
  exact Wset.W_take h _

/-! ## 85. ★★★★★★ (W45): **越境するなら、的はブロック根より低い** -/

/-- 最後の（部分）ブロックの根は、そこから先で **`hr0` により浅い**。 -/
theorem prefixTake_shallow {A Q : TrioSeq} {d e n j : ℕ}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hj : j < Q.length) :
    ∀ x, (A ++ mTower Q d e n).length < x →
      x < (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length →
      entry (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 0
          (A ++ mTower Q d e n).length
        < entry (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 0 x := by
  set P := A ++ mTower Q d e n with hP
  set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
  have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
  have hTlen : (B.take (j + 1)).length = j + 1 := by rw [List.length_take, hBlen]; omega
  intro x hx1 hx2
  rw [List.length_append, hTlen] at hx2
  obtain ⟨r, rfl⟩ : ∃ r, x = P.length + r := ⟨x - P.length, by omega⟩
  have e0 : entry (P ++ B.take (j + 1)) 0 P.length = entry Q 0 0 + d * n := by
    have h : entry (P ++ B.take (j + 1)) 0 P.length = entry (B.take (j + 1)) 0 0 := by
      simpa using entry_append_right P (B.take (j + 1)) 0 0
    rw [h, Wset.entry_take (show (0:ℕ) < j + 1 by omega), hB, entry0_Lift1,
      entry0_shiftr01 (W := Q) (d0 := d * n) (d1 := 0) (p := 0)
        (by simpa using (show 0 < Q.length by omega))]
  have er : entry (P ++ B.take (j + 1)) 0 (P.length + r) = entry Q 0 r + d * n := by
    rw [entry_append_right, Wset.entry_take (show r < j + 1 by omega), hB, entry0_Lift1,
      entry0_shiftr01 (W := Q) (d0 := d * n) (d1 := 0) (p := r)
        (by simpa using (show r < Q.length by omega))]
  rw [e0, er]
  have := hr0 r (by omega) (by omega)
  omega

/-- ★★★★★ **ブロック根は、そのブロックの全列の `le0` 祖先**（`hr0` から）。 -/
theorem prefixTake_le0_root {A Q : TrioSeq} {d e n j : ℕ}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) (hj : j < Q.length) (hj0 : 0 < j) :
    le0 (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
      (A ++ mTower Q d e n).length ((A ++ mTower Q d e n).length + j) := by
  have hTlen : ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length = j + 1 := by
    rw [List.length_take, Lift1_length, shiftr01_length]; omega
  refine le0_root_of_shallow (by simp only [List.length_append, hTlen]; omega)
    (prefixTake_shallow hr0 hj) _ (by omega) ?_
  simp only [List.length_append, hTlen]; omega

open Classical in
/-- ★★★★★★ **(W45) の芯**: `hr0` ∧ `j ≥ 1` で **行 1 の親が最後のブロックの外にある**なら、
**的の行 1 はブロック根の行 1 以下**（ブロック根も `e*n` だけ持ち上がることに注意）。
⟹ ★ ⟹ **的が錐の中なら `entry Q 1 j ≤ entry Q 1 0`** —— **`n` にも `e` にも依りません**。 -/
theorem row1_cross_implies_le_blockRoot {A Q : TrioSeq} {d e n j c : ℕ}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hj : j < Q.length) (hj0 : 0 < j)
    (hc : c < (A ++ mTower Q d e n).length)
    (h : nextrel1 (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        c ((A ++ mTower Q d e n).length + j)) :
    entry Q 1 j + (if le1 Q 0 j then e * n else 0) ≤ entry Q 1 0 + e * n := by
  have hz : le1 Q 0 0 := ⟨by omega, by omega, Relation.ReflTransGen.refl⟩
  have hmin := h.2.2.2.2.2 (A ++ mTower Q d e n).length ⟨hc, prefixTake_le0_root hr0 hj hj0⟩
  have e0 : entry (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 1
      (A ++ mTower Q d e n).length = entry Q 1 0 + e * n := by
    have := entry1_prefixTake A Q (d := d) (e := e) (n := n) (i := 0) hj (by omega)
    rw [if_pos hz] at this
    simpa using this
  rw [e0, entry1_prefixTake A Q hj (show j < j + 1 by omega)] at hmin
  exact hmin

/-- ★★★★★ ⟹ **的が錐の中なら、越境は `entry Q 1 j ≤ entry Q 1 0` を強制**（`n`・`e` 非依存）。 -/
theorem row1_cross_incone_le_root {A Q : TrioSeq} {d e n j c : ℕ}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hj : j < Q.length) (hj0 : 0 < j) (hcone : le1 Q 0 j)
    (hc : c < (A ++ mTower Q d e n).length)
    (h : nextrel1 (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        c ((A ++ mTower Q d e n).length + j)) :
    entry Q 1 j ≤ entry Q 1 0 := by
  have := row1_cross_implies_le_blockRoot hr0 hj hj0 hc h
  rw [if_pos hcone] at this
  omega

/-- ★★★★★★★ ⟹ **行 1 の越境は「的が `Q` の中で行 1 の孤児」のときだけ**。
⟹ ★ 対偶が私の `window_lt_of_row1_parent`。⟹ ★★ **`hr0` ＋ `j ≥ 1` で穴が 1 点に絞れます**。 -/
theorem row1_cross_implies_orphan {A Q : TrioSeq} {d e n j c : ℕ}
    (hj : j < Q.length)
    (hc : c < (A ++ mTower Q d e n).length)
    (h : nextrel1 (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        c ((A ++ mTower Q d e n).length + j)) :
    ¬ hasParent Q 1 j := by
  intro hpar
  obtain ⟨y, hy, -⟩ := hpar
  have hy' : nextrel1 Q y j := by simpa [nextR] using hy
  have := prefixTake_nextrel1_src_ge (A := A) (d := d) (e := e) hj hy' h
  omega

/-- ★★★★★★★ ⟹ **行 2 も同じ**: 越境は「的が `Q` の中で行 2 の孤児」のときだけ。 -/
theorem row2_cross_implies_orphan {A Q : TrioSeq} {d e n j c : ℕ}
    (hj : j < Q.length)
    (hc : c < (A ++ mTower Q d e n).length)
    (h : nextrel2 (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        c ((A ++ mTower Q d e n).length + j)) :
    ¬ hasParent Q 2 j := by
  intro hpar
  obtain ⟨y, hy, -⟩ := hpar
  have hy' : nextrel2 Q y j := by simpa [nextR] using hy
  have := prefixTake_nextrel2_src_ge (A := A) (d := d) (e := e) hj hy' h
  omega


/-! ## 86. ★★★★★★★ (W44): **`rankDE = srow(末尾)`** —— ちょうど一致します

`wd0` / `wd1` を展開した形で書きます（L3 は `unfold wd0 wd1` でそのまま当てられます）。

    `srow = 0` ⟹ `wd0 = 0`, `wd1 = 0` ⟹ **`rankDE = 0`**
    `srow = 1` ⟹ `wd0 > 0`（親は `le0` 祖先）, `wd1 = 0` ⟹ **`rankDE = 1`**
    `srow = 2` ⟹ `wd0 > 0`, `wd1 > 0`（親は `le1` 祖先）⟹ **`rankDE = 2`**

⟹ ★★★★★ **`≤` ではなく `=` です。** -/

/-- `srow` は 0, 1, 2 のいずれか。 -/
theorem srow_le_two (M : TrioSeq) (j : ℕ) : srow M j ≤ 2 := by
  unfold srow; split_ifs <;> omega

/-- ★★★ `srow = 2` の親は **行 1 でも狭義に小さい**（⟹ `wd1 > 0`）。 -/
theorem entry1_parent_lt_of_srow2 {M : TrioSeq} {a b : ℕ}
    (h : nextR M 2 a b) : entry M 1 a < entry M 1 b := by
  unfold nextR at h
  rw [if_neg (by omega), if_neg (by omega)] at h
  exact entry1_lt_of_le1_ne h.2.2.2.2.1 (by have := h.2.2.1; omega)

/-- ★★★★★★★ **(W44)**: **`rankDE (wd0) (wd1) = srow(末尾)`**。
⟹ ★ ですから **`srow` が下がる段では `rankDE` が真に減ります**。 -/
theorem rankDE_eq_srow {T : TrioSeq} {par last : ℕ}
    (hpar : nextR T (srow T last) par last) :
    rankDE (if 0 < srow T last then entry T 0 last - entry T 0 par else 0)
        (if 1 < srow T last then entry T 1 last - entry T 1 par else 0)
      = srow T last := by
  have hle : srow T last ≤ 2 := srow_le_two T last
  rcases (by omega : srow T last = 0 ∨ srow T last = 1 ∨ srow T last = 2) with hs | hs | hs
  · rw [hs] at hpar ⊢; simp [rankDE]
  · rw [hs] at hpar ⊢
    have h0 : entry T 0 par < entry T 0 last := entry0_parent_lt_of_srow1 hpar
    simp only [rankDE, if_pos (show 0 < 1 by omega), if_neg (show ¬ 1 < 1 by omega),
      if_pos (show 0 < entry T 0 last - entry T 0 par by omega),
      if_neg (show ¬ 0 < (0:ℕ) by omega)]
  · rw [hs] at hpar ⊢
    have h0 : entry T 0 par < entry T 0 last := entry0_parent_lt_of_srow2 hpar
    have h1 : entry T 1 par < entry T 1 last := entry1_parent_lt_of_srow2 hpar
    simp only [rankDE, if_pos (show 0 < 2 by omega), if_pos (show 1 < 2 by omega),
      if_pos (show 0 < entry T 0 last - entry T 0 par by omega),
      if_pos (show 0 < entry T 1 last - entry T 1 par by omega)]

/-- ★★★★★ ⟹ **`srow` が下がれば `rankDE` も下がる**（測度が減る側）。 -/
theorem rankDE_lt_of_srow_lt {T T' : TrioSeq} {par par' last last' : ℕ}
    (hpar : nextR T (srow T last) par last) (hpar' : nextR T' (srow T' last') par' last')
    (hlt : srow T' last' < srow T last) :
    rankDE (if 0 < srow T' last' then entry T' 0 last' - entry T' 0 par' else 0)
        (if 1 < srow T' last' then entry T' 1 last' - entry T' 1 par' else 0)
      < rankDE (if 0 < srow T last then entry T 0 last - entry T 0 par else 0)
        (if 1 < srow T last then entry T 1 last - entry T 1 par else 0) := by
  rw [rankDE_eq_srow hpar, rankDE_eq_srow hpar']; exact hlt


/-! ## 87. ★★★★★★★★ (W49): **孤児は `Aop` 節 3 の入口になりません** —— そして窓の形

`domT M m := lev M (|M|-1) = m+1 ∧ ¬ hasParent M (srow M (|M|-1)) (|M|-1)`（`Wset:61`）。
⟹ ⛔ **`¬ hasParent` は `M` 全体について**です。⟹ ★ 残差は「**`Q` の中で孤児**」であって、
`T` の中では **親を持ちます**（接頭辞 `A` の中に）。⟹ ⟹ ⛔ **`domT T m` は偽** ⟹ **節 3 に入れません**。

★★★ 代わりに言えるのは **窓の形**です: **親が `A` の中なら、窓は「接頭辞を縮めた同じ塔」**。 -/

/-- ⛔ **末尾が親を持つなら `domT` は偽**（節 3 に入れない）。1 行。 -/
theorem not_domT_of_hasParent {T : TrioSeq} {m : ℕ}
    (h : hasParent T (srow T (T.length - 1)) (T.length - 1)) : ¬ domT T m := fun hd => hd.2 h

/-- ★★★★★★★★ **親が接頭辞の中なら、窓は「接頭辞を縮めた、同じ塔」**。
⟹ ★ ⟹ **帰納の対象は `Q` ではなく `A`** になります。 -/
theorem prefixTake_drop_of_le_prefix {A Q : TrioSeq} {d e n j c : ℕ} (hc : c ≤ A.length) :
    (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).drop c
      = A.drop c ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1) := by
  rw [List.drop_append_of_le_length (by rw [List.length_append]; omega),
    List.drop_append_of_le_length hc]

/-- ★★★★★ ⟹ **窓の長さ**: 塔がまるごと入るので **`|Q|` より真に長い**（`0 < n`）。 -/
theorem prefixTake_window_length_of_prefix {A Q : TrioSeq} {d e n j c : ℕ} (hc : c ≤ A.length) :
    ((A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).drop c).length
      = (A.length - c) + n * Q.length + min (j + 1) Q.length := by
  rw [prefixTake_drop_of_le_prefix hc]
  simp only [List.length_append, List.length_drop, List.length_take, Lift1_length,
    shiftr01_length, mTower_length]

/-- ★★★★★★ ⟹ **接頭辞が減る**: 新しい接頭辞は `A.drop c`。
⟹ ★ **`0 < c` なら真に短く**なります。⟹ ⛔ **`c = 0` では減りません**（そこが本当の残差）。 -/
theorem prefixTake_new_prefix_length {A : TrioSeq} {c : ℕ} (hc : c ≤ A.length) (hc0 : 0 < c) :
    (A.drop c).length < A.length := by
  rw [List.length_drop]; omega


/-! ## 88. ★★★★★★★ (W50): **`lev(親) < lev(的)` は `srow` ごとに違います**

`lev M j = 2 * entry M 1 j + entry M 2 j`（`Wset.lean:57`、逐語で確認）。

| `srow(的)` | 結論 |
|---|---|
| **0** | ⛔ **偽**（`lev(的) = 0`、`lev` は非負なので `<` はあり得ない） |
| **1** | ★ **`zle1 M`（行 2 ≤ 1）が要ります**。⟹ z < 2 の断片では真 |
| **2** | ✅ **無条件で真**（`nextrel2` は行 2 も行 1 も真に下げる） |

⟹ ★★★ **team-lead の「`nextrel1` は行 2 に何も言わない」という読みが正しい**です。
⟹ ⟹ ★ ただし **`zle1` で埋まります**（行 2 が 1 下がる余地しかないので、行 1 の 1 下がり（＝ 2）が勝つ）。 -/

/-- `zle1` なら行 2 の値は（範囲外も含めて）常に `≤ 1`。 -/
theorem entry2_le_one_of_zle1 {M : TrioSeq} (h : zle1 M) (c : ℕ) : entry M 2 c ≤ 1 := by
  show (M.getD c (0, 0, 0)).2.2 ≤ 1
  rw [List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge c M.length with hc | hc
  · rw [List.getElem?_eq_getElem hc]; exact h _ (List.getElem_mem hc)
  · rw [List.getElem?_eq_none (by omega)]; simp

/-- ✅ **`srow = 2`: 無条件**。`nextrel2` は行 2 を真に下げ、`le1` が行 1 も真に下げます。 -/
theorem lev_parent_lt_of_srow2 {M : TrioSeq} {c x : ℕ} (h : nextR M 2 c x) :
    lev M c < lev M x := by
  unfold nextR at h
  rw [if_neg (by omega), if_neg (by omega)] at h
  have h2 : entry M 2 c < entry M 2 x := h.2.2.2.1
  have h1 : entry M 1 c < entry M 1 x := entry1_lt_of_le1_ne h.2.2.2.2.1 (by have := h.2.2.1; omega)
  unfold lev; omega

/-- ★ **`srow = 1`: `zle1 M` が要ります**（行 2 ≤ 1）。⟹ z < 2 の断片では真。 -/
theorem lev_parent_lt_of_srow1 {M : TrioSeq} {c x : ℕ}
    (hz : zle1 M) (hx : srow M x = 1) (h : nextR M 1 c x) : lev M c < lev M x := by
  unfold nextR at h
  rw [if_neg (by omega), if_pos rfl] at h
  have h1 : entry M 1 c < entry M 1 x := h.2.2.2.1
  have hx2 : entry M 2 x = 0 := by
    unfold srow at hx; split_ifs at hx <;> omega
  have hc2 : entry M 2 c ≤ 1 := entry2_le_one_of_zle1 hz c
  unfold lev; omega

/-- ⛔ **`srow = 0`: 偽**。`lev(的) = 0` なので `lev(親) < 0` はあり得ません。 -/
theorem lev_parent_not_lt_of_srow0 {M : TrioSeq} {c x : ℕ} (hx : srow M x = 0) :
    ¬ lev M c < lev M x := by
  have h1 : entry M 1 x = 0 := by unfold srow at hx; split_ifs at hx; omega
  have h2 : entry M 2 x = 0 := by unfold srow at hx; split_ifs at hx; omega
  unfold lev; omega

/-- ★★★★★★★ ⟹ **まとめ**: `zle1 M` の下で、**`srow(的) ≥ 1` なら `lev(親) < lev(的)`**。 -/
theorem lev_parent_lt_of_srow_pos {M : TrioSeq} {c x : ℕ}
    (hz : zle1 M) (hx : 0 < srow M x) (h : nextR M (srow M x) c x) : lev M c < lev M x := by
  have hle : srow M x ≤ 2 := srow_le_two M x
  rcases (by omega : srow M x = 1 ∨ srow M x = 2) with hs | hs
  · exact lev_parent_lt_of_srow1 hz hs (by rwa [hs] at h)
  · exact lev_parent_lt_of_srow2 (by rwa [hs] at h)

/-- ★★★ ⟹ **`srow(的) = 0` の段では、そもそも `lev(的) = 0`**。⟹ ★ 測度の底です。 -/
theorem lev_eq_zero_of_srow0 {M : TrioSeq} {x : ℕ} (hx : srow M x = 0) : lev M x = 0 := by
  have h1 : entry M 1 x = 0 := by unfold srow at hx; split_ifs at hx; omega
  have h2 : entry M 2 x = 0 := by unfold srow at hx; split_ifs at hx; omega
  unfold lev; omega


/-! ## 89. ★★★★★★ (W51): **孤児でも `srow` は下がりません**

`srow` は **`j` の行 1・行 2 の値だけ**の関数です。⟹ ⛔ **孤児かどうか（＝ 関係の話）は入りません**。
⟹ ★ そして **`j ≥ 1` なら `srow(T の末尾) = srow Q j`**（持ち上げは行 1 を 0 から起こせない）。
⟹ ⟹ ⛔ ですから **`rankDE` で吸収できません**。⟹ ★★ **そこが本当の残差**です。 -/

/-- ★★★ `hr0` の下では、**`j ≥ 1` の列は必ず行 0 の親を持つ**（根が祖先なので）。
⟹ ★ ⟹ **`srow = 0` の列は（`j ≥ 1` では）孤児になれません**。 -/
theorem hasParent0_of_hr0 {Q : TrioSeq} {j : ℕ}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hj : j < Q.length) (hj0 : 0 < j) : hasParent Q 0 j := by
  have hle : le0 Q 0 j :=
    le0_root_of_shallow (by omega) (fun x hx hxl => hr0 x (by omega) hxl) j hj0 hj
  obtain ⟨-, -, hrt⟩ := hle
  rcases Relation.ReflTransGen.cases_tail hrt with h1 | ⟨c, hc1, hc2⟩
  · omega
  · exact ⟨c, by simpa [nextR] using hc2,
      fun y hy => nextrel0_src_unique (by simpa [nextR] using hy) hc2⟩

open Classical in
/-- ★★★★★★ **(W51)**: `j ≥ 1` なら **`srow`（`T` の末尾）＝ `srow Q j`**。
⟹ ⛔ **持ち上げ `e*n` は行 1 を 0 から起こせません**（`le1 Q 0 j` は `entry Q 1 j > 0` を含意）。 -/
theorem srow_prefixTake_last (A Q : TrioSeq) {d e n j : ℕ} (hj : j < Q.length) (hj0 : 0 < j) :
    srow (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        ((A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1)
      = srow Q j := by
  have hTlen : ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length = j + 1 := by
    rw [List.length_take, Lift1_length, shiftr01_length]; omega
  have hlen : (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1
      = (A ++ mTower Q d e n).length + j := by
    rw [List.length_append, hTlen]; omega
  rw [hlen]
  have h2 := entry2_prefixTake A Q (d := d) (e := e) (n := n) (j := j) (i := j) (by omega)
  have h1 := entry1_prefixTake A Q (d := d) (e := e) (n := n) hj (i := j) (by omega)
  have hlift : (0 < entry Q 1 j + (if le1 Q 0 j then e * n else 0)) ↔ (0 < entry Q 1 j) := by
    constructor
    · intro hpos
      by_contra hz
      have hzj : entry Q 1 j = 0 := by omega
      by_cases hc : le1 Q 0 j
      · exact absurd (entry1_lt_of_le1_ne hc (by omega)) (by omega)
      · rw [if_neg hc] at hpos; omega
    · intro hpos; omega
  unfold srow
  rw [h1, h2]
  by_cases hq2 : 0 < entry Q 2 j
  · rw [if_pos hq2, if_pos hq2]
  · rw [if_neg hq2, if_neg hq2]
    by_cases hq1 : 0 < entry Q 1 j
    · rw [if_pos (hlift.mpr hq1), if_pos hq1]
    · rw [if_neg (fun hx => hq1 (hlift.mp hx)), if_neg hq1]


/-! ## 90. ★★★★★★★ (C1): **`u` の帳簿は無料** —— 右に足しても `lev(根)` は動きません

`mem_Wself_iff u M : M ∈ W u ↔ M ∈ Wself ∧ lev M 0 ≤ u`（`Wtower2:2990`）で、
**`Wself` は `u` を含みません**（`Wself = {M | M ∈ W (lev M 0)}`、`Wtower2:2988`）。
⟹ ★ そして **右に何を足しても `lev(根)` は動きません**（下記）。
⟹ ⟹ ★★★★★ ⟹ **塔を何段積んでも、要る `u` は増えません**。⟹ **帳簿は無料**です。 -/

/-- ★★★★★ **右に足しても根の `lev` は動かない**（`A ≠ []`）。 -/
theorem lev_append_left_zero (A B : TrioSeq) (hA : A ≠ []) : lev (A ++ B) 0 = lev A 0 := by
  have h0 : 0 < A.length := List.length_pos_iff.mpr hA
  unfold lev
  rw [entry_append_left A B h0, entry_append_left A B h0]

/-- ★★★★★★★ ⟹ **塔を積んでも要る `u` は増えません**。
⟹ ★ ⟹ **`Wself` さえ出れば、`W u` は `lev(根) ≤ u` だけで全段いっぺんに出ます**。 -/
theorem mem_W_of_Wself_append {u : ℕ} {A B : TrioSeq} (hA : A ≠ [])
    (hself : A ++ B ∈ Wself) (hu : lev A 0 ≤ u) : A ++ B ∈ W u :=
  (mem_Wself_iff u (A ++ B)).mpr ⟨hself, by rw [lev_append_left_zero A B hA]; exact hu⟩

/-- ★★★★★ ⟹ **`n` に依らない**: 塔の段数がいくつでも、必要な `u` は `lev A 0` のまま。 -/
theorem mem_W_of_Wself_tower {u : ℕ} {A Q : TrioSeq} {d e n : ℕ} (hA : A ≠ [])
    (hself : A ++ mTower Q d e n ∈ Wself) (hu : lev A 0 ≤ u) : A ++ mTower Q d e n ∈ W u :=
  mem_W_of_Wself_append hA hself hu


/-! ## 91. ★★★★★★★★ (C2): **`argOK` は `hr0` そのもの** —— 私の `hr0` 系が `CoreCap` に全部効きます

`argOK R := ∀ p ∈ R, 0 < p.1`（`Wset:1314`）。
`CoreCap` の対象は **`(0,v,z) :: M`（`argOK M`）**。
⟹ ★★★★★ **根の行 0 は 0、他は全部 > 0** ⟹ **`hr0` の仮定そのもの**です。 -/

/-- ★★★★★★★★ **`argOK M` ⟹ `(0,v,z) :: M` は `hr0`**。
⟹ ★ ⟹ **私の `hr0` 系（`window_lt_of_row0_parent`、`prefixTake_le0_root`、
`hasParent0_of_hr0`、`no_row0_parent_from_before_block`）が `CoreCap` の文脈に全部効きます**。 -/
theorem hr0_of_argOK {M : TrioSeq} {v z : ℕ} (h : argOK M) :
    ∀ l, 0 < l → l < (((0, v, z) : ℕ × ℕ × ℕ) :: M).length →
      entry (((0, v, z) : ℕ × ℕ × ℕ) :: M) 0 0 < entry (((0, v, z) : ℕ × ℕ × ℕ) :: M) 0 l := by
  intro l hl0 hl
  have h0 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: M) 0 0 = 0 := rfl
  rw [h0]
  obtain ⟨r, rfl⟩ : ∃ r, l = r + 1 := ⟨l - 1, by omega⟩
  have hr : r < M.length := by simpa using hl
  show 0 < ((((0, v, z) : ℕ × ℕ × ℕ) :: M).getD (r + 1) (0, 0, 0)).1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hl),
    List.getElem_cons_succ]
  exact h _ (List.getElem_mem hr)

/-- ★★★★★ ⟹ **`CoreCap` の文脈では、末尾以外の全列が根の `le0` 子孫**。 -/
theorem le0_root_of_argOK {M : TrioSeq} {v z : ℕ} (h : argOK M) :
    ∀ j, 0 < j → j < (((0, v, z) : ℕ × ℕ × ℕ) :: M).length →
      le0 (((0, v, z) : ℕ × ℕ × ℕ) :: M) 0 j :=
  le0_root_of_shallow (by simp) (fun x hx hxl => hr0_of_argOK (v := v) (z := z) h x hx hxl)

/-- ★★★★★★ ⟹ **`CoreCap` の末尾列は必ず行 0 の親を持つ** ⟹ ⛔ **`snoc_orphan` は使えません**
（`srow = 0` の場合）。⟹ ★ **`cap` の末尾は `argOK` により根より深い**からです。 -/
theorem hasParent0_of_argOK {M : TrioSeq} {v z j : ℕ} (h : argOK M)
    (hj0 : 0 < j) (hj : j < (((0, v, z) : ℕ × ℕ × ℕ) :: M).length) :
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: M) 0 j :=
  hasParent0_of_hr0 (fun l hl0 hl => hr0_of_argOK (v := v) (z := z) h l hl0 (by simpa using hl))
    (by simpa using hj) hj0


/-! ## 92. ★★★★★★★★ (W52): **行 0 の祖先に行 1 が小さいものがあれば、行 1 の親がある**

`hasParent1_iff_amin_lt`（§333、前提なし）＋ `Cgraft.amin_le` の 2 行の系。
⟹ ★★★ **トリオ版の `DbmsStd.hasParent0_of_exists`（行 1 版）**です。
⟹ ⟹ ★ ⟹ **(W52)（残差の次は良い群）を、証人 1 本に還元する道具**。 -/

/-- ★★★★★★★★ **証人があれば行 1 の親がある**（前提は証人だけ）。 -/
theorem hasParent1_of_le0_witness {M : TrioSeq} {j y : ℕ} (hj : j < M.length)
    (hanc : Relation.ReflTransGen (nextrel0 M) y j) (hlt : entry M 1 y < entry M 1 j) :
    hasParent M 1 j :=
  (hasParent1_iff_amin_lt hj).mpr (lt_of_le_of_lt (amin_le hanc) hlt)

/-- ★★★★★ `le0` 版（`le0` は `RTG` を第 3 成分に持ちます）。 -/
theorem hasParent1_of_le0 {M : TrioSeq} {j y : ℕ} (hj : j < M.length)
    (hanc : le0 M y j) (hlt : entry M 1 y < entry M 1 j) : hasParent M 1 j :=
  hasParent1_of_le0_witness hj hanc.2.2 hlt

/-- ★★★★★★★ ⟹ **(W52) の行 1**: 証人があれば **越境しません**（`row1_cross_implies_orphan` の対偶）。 -/
theorem no_row1_cross_of_le0_witness {A Q : TrioSeq} {d e n j y c : ℕ}
    (hj : j < Q.length) (hanc : le0 Q y j) (hlt : entry Q 1 y < entry Q 1 j)
    (h : nextrel1 (A ++ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
        c ((A ++ mTower Q d e n).length + j)) :
    (A ++ mTower Q d e n).length ≤ c := by
  by_contra hc
  push Not at hc
  exact row1_cross_implies_orphan hj hc h (hasParent1_of_le0 hj hanc hlt)

/-- ★★★★★★ ⟹ **塔の中の証人**: 第 `k` ブロック（`k ≥ 1`）の錐の中の列は、
**1 つ前のブロックの同じ相対位置**が行 1 の証人になります（`0 < e`）。
⚠⚠ **適用条件: 両方が錐の中のときだけ**です（仮定 `hcone : le1 Q 0 r` が両側に効きます）。
⛔ **的が錐の外なら、的は持ち上がらないので「前が低い」ことに意味がありません**
（R2 の指摘、2026-08-30）。⟹ ★ 私は「前が低い」と「相手が高い」を混同して (W74) を誤りました。 -/
theorem entry1_prevBlock_lt (Q : TrioSeq) {d e n k r : ℕ}
    (hk : k < n) (hk0 : 0 < k) (hr : r < Q.length) (hcone : le1 Q 0 r) (he : 0 < e) :
    entry (mTower Q d e n) 1 ((k - 1) * Q.length + r)
      < entry (mTower Q d e n) 1 (k * Q.length + r) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [entry1_mTower_block_formula Q (by omega) hr, entry1_mTower_block_formula Q hk hr,
    if_pos hcone, if_pos hcone, Nat.mul_succ]
  omega


/-! ## 93. ★★★★★★★★ (W53): **`PrefixCopiesOpen` の親は、`Q` の根の高さの列で必ず `A` に落ちます**

`d = e = 0` なので持ち上げが一切なく、**写しは完全に同じ**。
⟹ ★★★★★ ですから **行 0 が `Q` の根と同じ高さの列**（＝ `entry Q 0 r = entry Q 0 0`）は、
**どの写しにも、より浅い候補がありません** ⟹ ⛔ **親は必ず `A` の中**。
⟹ ⟹ ★★★★★★★★ **しかも `n` にも `k`（第何写しか）にも依りません**。 -/

/-- 行 0 のブロックの式（`L106:476` と同じもの。`H12Export` は `L106` を import しないので再掲）。 -/
theorem entry0_mTower_block' (Q : TrioSeq) {d e n k i : ℕ} (hk : k < n) (hi : i < Q.length) :
    entry (mTower Q d e n) 0 (k * Q.length + i) = entry Q 0 i + d * k := by
  rw [mTower_entry hk hi, entry0_Lift1,
    entry0_shiftr01 (W := Q) (d0 := d * k) (d1 := 0) (p := i) (by simpa using hi)]

/-- ★★★★★★★★ **(W53) の行 0**: `d = 0`（持ち上げ無し）で、`Q` の全列が根以上、
かつ **的の行 0 が `Q` の根と同じ**なら、**行 0 の親は接頭辞 `A` の中にしかいません**。
⟹ ★ **`n` にも `k` にも依りません**。⟹ ⟹ ★★ **これが `PrefixCopiesOpen` の開いている理由**です。 -/
theorem nextrel0_src_lt_prefix_of_root_height {A Q : TrioSeq} {e n k r c : ℕ}
    (hQmin : ∀ i, i < Q.length → entry Q 0 0 ≤ entry Q 0 i)
    (hk : k < n) (hr : r < Q.length) (hreq : entry Q 0 r = entry Q 0 0)
    (h : nextrel0 (A ++ mTower Q 0 e n) c (A.length + (k * Q.length + r))) :
    c < A.length := by
  by_contra hc
  push Not at hc
  have hQpos : 0 < Q.length := by omega
  have hlt : c < A.length + (k * Q.length + r) := h.2.2.1
  have hval : entry (A ++ mTower Q 0 e n) 0 c
      < entry (A ++ mTower Q 0 e n) 0 (A.length + (k * Q.length + r)) := h.2.2.2.1
  obtain ⟨s, rfl⟩ : ∃ s, c = A.length + s := ⟨c - A.length, by omega⟩
  have hs : s < n * Q.length := by
    have hkn : (k + 1) * Q.length ≤ n * Q.length := Nat.mul_le_mul_right _ (by omega)
    have : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
    omega
  have hk' : s / Q.length < n := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm] at hs; exact hs)
  have hi' : s % Q.length < Q.length := Nat.mod_lt _ hQpos
  have hsplit : s = (s / Q.length) * Q.length + s % Q.length := (Nat.div_add_mod' s Q.length).symm
  rw [entry_append_right, entry_append_right, hsplit,
    entry0_mTower_block' Q hk' hi', entry0_mTower_block' Q hk hr, hreq] at hval
  have := hQmin _ hi'
  omega

/-- ★★★★★ ⟹ **ブロック根は必ずこの場合**（`r = 0`）。
⟹ ⛔ **どの写しのブロック根も、行 0 の親は `A` の中**。 -/
theorem nextrel0_blockRoot_src_lt_prefix {A Q : TrioSeq} {e n k c : ℕ}
    (hQmin : ∀ i, i < Q.length → entry Q 0 0 ≤ entry Q 0 i)
    (hQ : 0 < Q.length) (hk : k < n)
    (h : nextrel0 (A ++ mTower Q 0 e n) c (A.length + (k * Q.length + 0))) :
    c < A.length :=
  nextrel0_src_lt_prefix_of_root_height hQmin hk hQ rfl h


/-! ## 94. ★★★★★★★★ (W54): **行 2 ≡ 0 の `PrefixCopiesOpen` は、既に緑でした**

`zeroRow2_mem_Wself`（`Wtower2:3011`）は **2 行プロジェクト `YAPSS.Wset.mem_W_maxr1` を借りて**、
**行 2 ≡ 0 の列は無条件で `Wself`** と言います。⟹ ★★★★★ **前提が一切要りません**。
⟹ ⟹ ★★★ そして私の §306 `prefix_mem_of_zeroRow2` が **`A ++ T`（`T` は任意）**を出します。
⟹ ⟹ ⟹ ★★★★★★★★ **`PrefixCopiesOpen` の行 2 ≡ 0 版は、その系（1 行）**です。 -/

/-- `zeroRow2` は `entry` の言葉でも（範囲外も含めて）成り立ちます。 -/
theorem entry2_eq_zero_of_zeroRow2 {M : TrioSeq} (h : ∀ p ∈ M, p.2.2 = 0) (i : ℕ) :
    entry M 2 i = 0 := by
  show (M.getD i (0, 0, 0)).2.2 = 0
  rw [List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge i M.length with hi | hi
  · rw [List.getElem?_eq_getElem hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getElem?_eq_none (by omega)]; simp

/-- 写しの列も行 2 ≡ 0。 -/
theorem zeroRow2_flatMap {Q : TrioSeq} {n : ℕ} (hz : ∀ p ∈ Q, p.2.2 = 0) :
    ∀ p ∈ ((List.range n).flatMap fun _ => Q), p.2.2 = 0 := by
  intro p hp
  rw [List.mem_flatMap] at hp
  obtain ⟨-, -, hk⟩ := hp
  exact hz p hk

/-- ★★★★★ **塔も行 2 ≡ 0**（`Lift1` も `shiftr01` も行 2 を動かしません）。 -/
theorem zeroRow2_mTower {Q : TrioSeq} {d e n : ℕ} (hz : ∀ p ∈ Q, p.2.2 = 0) :
    ∀ p ∈ mTower Q d e n, p.2.2 = 0 := by
  intro p hp
  unfold mTower at hp
  rw [List.mem_flatMap] at hp
  obtain ⟨k, -, hk⟩ := hp
  unfold Lift1 at hk
  rw [List.mem_map] at hk
  obtain ⟨i, -, rfl⟩ := hk
  show entry (shiftr01 (d * k) 0 Q) 2 i = 0
  rw [entry2_shiftr01]
  exact entry2_eq_zero_of_zeroRow2 hz i

/-- ★★★★★★★★ **(W54)**: **行 2 ≡ 0 の `PrefixCopiesOpen` は真**（`A ∈ W u` だけで出ます）。
⟹ ★ **`Q ∈ W u` も、`Q` の根の条件も、`n` も要りません**。 -/
theorem prefixCopiesOpen_of_zeroRow2 {u n : ℕ} {A Q : TrioSeq}
    (hzA : ∀ p ∈ A, p.2.2 = 0) (hzQ : ∀ p ∈ Q, p.2.2 = 0)
    (hA : A ∈ W u) (hopen : ∃ q ∈ A, q.1 < entry Q 0 0) :
    A ++ ((List.range n).flatMap fun _ => Q) ∈ W u := by
  obtain ⟨q, hq, -⟩ := hopen
  exact prefix_mem_of_zeroRow2 hzA (zeroRow2_flatMap hzQ) hA (by rintro rfl; simp at hq)

/-- ★★★★★★★★ ⟹ **一般の塔でも同じ**（`d`, `e` は何でもよい）。
⟹ ★ ⟹ **行 2 ≡ 0 の断片では、塔閉包が完全に無料**です。 -/
theorem prefix_mTower_of_zeroRow2 {u : ℕ} {A Q : TrioSeq} {d e n : ℕ}
    (hzA : ∀ p ∈ A, p.2.2 = 0) (hzQ : ∀ p ∈ Q, p.2.2 = 0)
    (hA : A ∈ W u) (hAne : A ≠ []) : A ++ mTower Q d e n ∈ W u :=
  prefix_mem_of_zeroRow2 hzA (zeroRow2_mTower hzQ) hA hAne


/-! ## 95. ★★★★★★★★ (W53 続き): **(あ) の側 —— 根より深い列の親は、同じ写しの中**

(W53) が **(い)（`entry Q 0 r = entry Q 0 0`）⟹ 親は必ず `A`** を言いました。
⟹ ★ その裏側 **(あ)（`entry Q 0 0 < entry Q 0 r`）⟹ 親は同じ写しの中**を書きます。
⟹ ⟹ ★★★★★ **ブロック根が「同じ写しの中の、より浅い列」**だからです（持ち上げが相殺）。 -/

/-- ★★★★★★★★ **(あ)**: 的の行 0 が `Q` の根より深いなら、**行 0 の親は同じ写しの中**。
⟹ ★ **`A` にも前の写しにも行きません**。⟹ ⟹ ★★ **`d` は何でもよい**（持ち上げが相殺）。 -/
theorem nextrel0_src_ge_block_of_deep {A Q : TrioSeq} {d e n k r c : ℕ}
    (hk : k < n) (hr : r < Q.length) (hdeep : entry Q 0 0 < entry Q 0 r)
    (h : nextrel0 (A ++ mTower Q d e n) c (A.length + (k * Q.length + r))) :
    A.length + k * Q.length ≤ c := by
  have hQpos : 0 < Q.length := by omega
  have hr0 : 0 < r := by rcases Nat.eq_zero_or_pos r with rfl | hp; · omega
                         · exact hp
  by_contra hc
  push Not at hc
  have hmin := h.2.2.2.2 (A.length + (k * Q.length + 0)) ⟨by omega, by omega⟩
  rw [entry_append_right, entry_append_right,
    entry0_mTower_block' Q hk hQpos, entry0_mTower_block' Q hk hr] at hmin
  omega

/-- ★★★★★★★ ⟹ **`PrefixCopiesOpen` の二分法（行 0）**:
的の行 0 が `Q` の根と同じなら **必ず `A`**、深いなら **必ず同じ写しの中**。
⟹ ★★★ **中間はありません**（`Q` の全列が根以上、という前提の下で）。 -/
theorem prefixCopies_row0_dichotomy {A Q : TrioSeq} {e n k r c : ℕ}
    (hQmin : ∀ i, i < Q.length → entry Q 0 0 ≤ entry Q 0 i)
    (hk : k < n) (hr : r < Q.length)
    (h : nextrel0 (A ++ mTower Q 0 e n) c (A.length + (k * Q.length + r))) :
    (entry Q 0 r = entry Q 0 0 ∧ c < A.length)
      ∨ (entry Q 0 0 < entry Q 0 r ∧ A.length + k * Q.length ≤ c) := by
  rcases Nat.lt_or_ge (entry Q 0 0) (entry Q 0 r) with hd | hd
  · exact Or.inr ⟨hd, nextrel0_src_ge_block_of_deep hk hr hd h⟩
  · have heq : entry Q 0 r = entry Q 0 0 := le_antisymm hd (hQmin r hr)
    exact Or.inl ⟨heq, nextrel0_src_lt_prefix_of_root_height hQmin hk hr heq h⟩

/-- ★★★★★ ⟹ **`hr0 Q` の下では、`nextrel0`（行 0）の越境はブロック根だけ**（`r = 0`）。
⚠⚠ **これは行 0 の親についてのみ**です。⛔ **`srow = 1` では偽**——
R2 の実測で **`hr0(Q)` 真の残差 11,778 件のうち `j ≥ 1` が 44.9312%**、
反例 `A = [(0,0,0),(1,0,0)]`、`Q = [(2,1,0),(3,1,0)]`、`n = 1`、`j = 1`、`srow = 1`。
⟹ ★ `srow = 1` の側は (W56) `prefix_mTower_row1_cross_implies_orphan` を見てください。 -/
theorem prefixCopies_row0_residual_only_blockRoot {A Q : TrioSeq} {e n k r c : ℕ}
    (hr0Q : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hk : k < n) (hr : r < Q.length) (hr0 : 0 < r)
    (h : nextrel0 (A ++ mTower Q 0 e n) c (A.length + (k * Q.length + r))) :
    A.length + k * Q.length ≤ c :=
  nextrel0_src_ge_block_of_deep hk hr (hr0Q r hr0 hr) h


/-! ## 96. ★★★★★★★★ (W56): **`srow = 1` の的 —— 越境 ⟺ `Q` の中で行 1 の孤児**

(W53) の行 1 版。⟹ ★ 私の `prefixTake_nextrel1_src_ge`（部分ブロック版）を、
**`A ++ mTower Q d e n`（完全ブロックだけ）**に移したものです。
⟹ ⟹ ★★★★★ **`d`, `e` は何でもよく、`hr0` も要りません**。 -/

/-- ★★★★★★★★ **証人 `nextrel1 Q y j` があれば、行 1 の親は同じ写しの中**。
⟹ ★ **`A` にも前の写しにも行きません**。⟹ ⟹ ★★ **仮定は証人だけ**です。 -/
theorem prefix_mTower_nextrel1_src_ge {A Q : TrioSeq} {d e n k j y c : ℕ}
    (hk : k < n) (hj : j < Q.length) (hy : nextrel1 Q y j)
    (h : nextrel1 (A ++ mTower Q d e n) c (A.length + (k * Q.length + j))) :
    A.length + (k * Q.length + y) ≤ c := by
  have hylt : y < j := hy.2.2.1
  have hyQ : y < Q.length := by omega
  have hlt : entry Q 1 y < entry Q 1 j := hy.2.2.2.1
  have hlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have hkn : (k + 1) * Q.length ≤ n * Q.length := Nat.mul_le_mul_right _ (by omega)
  have hsk : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
  have hle0 : le0 (A ++ mTower Q d e n)
      (A.length + (k * Q.length + y)) (A.length + (k * Q.length + j)) := by
    refine le0_append_right_of _ _ ⟨by omega, by omega, ?_⟩
    exact rtg0_mTower_intra_block Q hk hyQ hj hy.2.2.2.2.1.2.2
  by_contra hc
  push Not at hc
  have hmin := h.2.2.2.2.2 (A.length + (k * Q.length + y)) ⟨by omega, hle0⟩
  rw [entry_append_right, entry_append_right,
    entry1_mTower_block_formula Q hk hj, entry1_mTower_block_formula Q hk hyQ] at hmin
  by_cases hcy : le1 Q 0 y
  · have hcj : le1 Q 0 j := ⟨by omega, hj, hcy.2.2.tail hy⟩
    rw [if_pos hcy, if_pos hcj] at hmin; omega
  · rw [if_neg hcy] at hmin
    split_ifs at hmin <;> omega

/-- ★★★★★★★★ ⟹ **(W56) の片側**: **越境 ⟹ `Q` の中で行 1 の孤児**。
⟹ ★ 対偶: **`Q` の中で親を持てば、越境しません**（＝ **良い群**）。 -/
theorem prefix_mTower_row1_cross_implies_orphan {A Q : TrioSeq} {d e n k j c : ℕ}
    (hk : k < n) (hj : j < Q.length) (hc : c < A.length)
    (h : nextrel1 (A ++ mTower Q d e n) c (A.length + (k * Q.length + j))) :
    ¬ hasParent Q 1 j := by
  intro hpar
  obtain ⟨y, hy, -⟩ := hpar
  have hy' : nextrel1 Q y j := by simpa [nextR] using hy
  have := prefix_mTower_nextrel1_src_ge hk hj hy' h
  omega

/-- ★★★★★★★ ⟹ **良い群の側**（対偶、使う形）。 -/
theorem prefix_mTower_row1_src_ge_of_hasParent {A Q : TrioSeq} {d e n k j c : ℕ}
    (hk : k < n) (hj : j < Q.length) (hpar : hasParent Q 1 j)
    (h : nextrel1 (A ++ mTower Q d e n) c (A.length + (k * Q.length + j))) :
    A.length ≤ c := by
  by_contra hc
  push Not at hc
  exact prefix_mTower_row1_cross_implies_orphan hk hj hc h hpar

/-- ★★★★★★★ **行 2 版も同じ**（`nextrel2` は `le1` 祖先の上の最小性）。 -/
theorem prefix_mTower_row2_cross_implies_orphan {A Q : TrioSeq} {d e n k j c : ℕ}
    (hk : k < n) (hj : j < Q.length) (hc : c < A.length)
    (hcone : ∀ y, nextrel2 Q y j → le1 (A ++ mTower Q d e n)
      (A.length + (k * Q.length + y)) (A.length + (k * Q.length + j)))
    (h : nextrel2 (A ++ mTower Q d e n) c (A.length + (k * Q.length + j))) :
    ¬ hasParent Q 2 j := by
  intro hpar
  obtain ⟨y, hy, -⟩ := hpar
  have hy' : nextrel2 Q y j := by simpa [nextR] using hy
  have hylt : y < j := hy'.2.2.1
  have hlt : entry Q 2 y < entry Q 2 j := hy'.2.2.2.1
  have hmin := h.2.2.2.2.2 (A.length + (k * Q.length + y)) ⟨by omega, hcone y hy'⟩
  rw [entry_append_right, entry_append_right, mTower_entry hk hj,
    mTower_entry hk (show y < Q.length by omega), entry2_Lift1, entry2_Lift1,
    entry2_shiftr01, entry2_shiftr01] at hmin
  omega


/-! ## 97. ★★★★★★★★ (W57): **最小形 `|Q| = 1`** —— 二重帰納法なら回ります

`Q = [(x,0,0)]` ⟹ 写しは `List.replicate n (x,0,0)`。
⟹ ★ **`entry Q 0 r = entry Q 0 0` が常に真**（`r = 0` しかない）⟹ ⟹ ★★ **(W53) の (い) のみ**
⟹ ⟹ ⟹ ★★★ **親は必ず `A` の中** ＝ **常に残差**。
⟹ ★★★★★ そして **末尾の `srow = 0`** ⟹ **`wd0 = wd1 = 0`**（(W44)）⟹ **後継も純粋な写し**。 -/

/-- 1 列の写しは `List.replicate`。 -/
theorem flatMap_singleton_eq_replicate (q : ℕ × ℕ × ℕ) (n : ℕ) :
    ((List.range n).flatMap fun _ => [q]) = List.replicate n q := by
  induction n with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.flatMap_append, ih]; simp [List.replicate_succ']

/-- ★★★ **後継の窓は、写しが 1 つ減っただけ**。 -/
theorem dropLast_append_replicate_succ (Y : TrioSeq) (q : ℕ × ℕ × ℕ) (n : ℕ) :
    (Y ++ List.replicate (n + 1) q).dropLast = Y ++ List.replicate n q := by
  rw [List.replicate_succ', ← List.append_assoc, List.dropLast_concat]

/-- ★★★ **接頭辞を削っても写しは残る**。 -/
theorem drop_append_replicate (A : TrioSeq) (q : ℕ × ℕ × ℕ) (n c : ℕ) (hc : c ≤ A.length) :
    (A ++ List.replicate n q).drop c = A.drop c ++ List.replicate n q :=
  List.drop_append_of_le_length hc

/-- ★★★★★ **最小形の末尾は `srow = 0`**（行 1 も行 2 も 0）。
⟹ ★ ⟹ **`wd0 = wd1 = 0`**（`if 0 < srow` の番人）⟹ ⟹ ★★ **後継の塔も持ち上げ 0**。 -/
theorem srow_last_of_append_replicate (A : TrioSeq) (x n : ℕ) :
    srow (A ++ List.replicate (n + 1) ((x, 0, 0) : ℕ × ℕ × ℕ))
      ((A ++ List.replicate (n + 1) ((x, 0, 0) : ℕ × ℕ × ℕ)).length - 1) = 0 := by
  have hlen : (A ++ List.replicate (n + 1) ((x, 0, 0) : ℕ × ℕ × ℕ)).length - 1
      = A.length + n := by
    rw [List.length_append, List.length_replicate]; omega
  have hget : ∀ i, entry (A ++ List.replicate (n + 1) ((x, 0, 0) : ℕ × ℕ × ℕ)) i (A.length + n)
      = entry (List.replicate (n + 1) ((x, 0, 0) : ℕ × ℕ × ℕ)) i n := fun i => by
    rw [entry_append_right]
  have hr : ∀ i, entry (List.replicate (n + 1) ((x, 0, 0) : ℕ × ℕ × ℕ)) i n
      = (if i = 0 then x else 0) := by
    intro i
    show (if i = 0 then _ else if i = 1 then _ else _) = _
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [List.length_replicate]; omega),
      List.getElem_replicate]
    split_ifs <;> rfl
  rw [hlen]
  unfold srow
  rw [hget 2, hget 1, hr 2, hr 1]
  simp

/-- ★★★★★★★★ **(W57) の骨格**: 最小形の後継は **接頭辞が真に短い、同じ形**。
⟹ ★ **`A' = A.take c`（`c < |A|`）**、**新しい基底 `V = A.drop c ++ replicate n (x,0,0)`**。
⟹ ⟹ ★★★ ⟹ **`|A|` の帰納で外側が回ります**。
⟹ ⟹ ⟹ ⛔ **ただし `V ∈ W u` を出すのに `n` の帰納が要ります**（`V` も同じ形）。 -/
theorem minimal_successor_shape (A : TrioSeq) (x n c : ℕ) (hc : c ≤ A.length) :
    ((A ++ List.replicate (n + 1) ((x, 0, 0) : ℕ × ℕ × ℕ)).drop c).dropLast
      = A.drop c ++ List.replicate n ((x, 0, 0) : ℕ × ℕ × ℕ) := by
  rw [drop_append_replicate A _ _ _ hc, dropLast_append_replicate_succ]


/-! ## 98. ★★★★★★★★ (W57 続き): **`srow = 1` の最小形は、族をまたぎます**

`Q = [(x,1,0)]`、`d = e = 0` ⟹ 写しは全部 `(x,1,0)`。
⟹ ★ **行 1 が 1 未満の候補が塔に無い** ⟹ **常に残差**（(W56) と整合）。
⟹ ⟹ ★★★★★ そして **`srow = 1` ⟹ `wd0 > 0`, `wd1 = 0`**（(W44)）
⟹ ⟹ ⟹ ★★★ **後継は純粋な写しではなく `shTower`（`d0 > 0`）**になります。 -/

/-- 一般の `q` での末尾の `srow`。 -/
theorem srow_last_of_append_replicate_gen (A : TrioSeq) (q : ℕ × ℕ × ℕ) (n : ℕ) :
    srow (A ++ List.replicate (n + 1) q) ((A ++ List.replicate (n + 1) q).length - 1)
      = if 0 < q.2.2 then 2 else if 0 < q.2.1 then 1 else 0 := by
  have hlen : (A ++ List.replicate (n + 1) q).length - 1 = A.length + n := by
    rw [List.length_append, List.length_replicate]; omega
  have hget : ∀ i, entry (A ++ List.replicate (n + 1) q) i (A.length + n)
      = entry (List.replicate (n + 1) q) i n := fun i => by rw [entry_append_right]
  have hr : ∀ i, entry (List.replicate (n + 1) q) i n
      = (if i = 0 then q.1 else if i = 1 then q.2.1 else q.2.2) := by
    intro i
    show (if i = 0 then _ else if i = 1 then _ else _) = _
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [List.length_replicate]; omega),
      List.getElem_replicate]
    split_ifs <;> rfl
  rw [hlen]
  unfold srow
  rw [hget 2, hget 1, hr 2, hr 1]
  simp

/-- ★★★★★ **`srow = 1` の最小形**: `q = (x, 1, 0)` なら末尾の `srow = 1`。 -/
theorem srow_last_of_append_replicate_one (A : TrioSeq) (x v n : ℕ) (hv : 0 < v) :
    srow (A ++ List.replicate (n + 1) ((x, v, 0) : ℕ × ℕ × ℕ))
      ((A ++ List.replicate (n + 1) ((x, v, 0) : ℕ × ℕ × ℕ)).length - 1) = 1 := by
  rw [srow_last_of_append_replicate_gen]
  simp [hv]

/-- ★★★★★★★★ **後継の形は `q` に依りません**（写しが 1 つ減るだけ）。 -/
theorem minimal_successor_shape_gen (A : TrioSeq) (q : ℕ × ℕ × ℕ) (n c : ℕ)
    (hc : c ≤ A.length) :
    ((A ++ List.replicate (n + 1) q).drop c).dropLast
      = A.drop c ++ List.replicate n q := by
  rw [drop_append_replicate A _ _ _ hc, dropLast_append_replicate_succ]

/-- ★★★★★★★★ ⟹ **`srow = 1` の最小形では `rankDE = 1`** ⟹ **`d0 > 0`**
⟹ ★ ⟹ **後継は純粋な写し（`PrefixCopies`）ではなく `shTower`**。
⟹ ⟹ ★★★ **＝ 最小形が族をまたぎます**（三分割は独立ではありません）。 -/
theorem rankDE_one_of_srow1_minimal {A : TrioSeq} {x v n : ℕ} {par : ℕ} (hv : 0 < v)
    (hpar : nextR (A ++ List.replicate (n + 1) ((x, v, 0) : ℕ × ℕ × ℕ))
      (srow (A ++ List.replicate (n + 1) ((x, v, 0) : ℕ × ℕ × ℕ))
        ((A ++ List.replicate (n + 1) ((x, v, 0) : ℕ × ℕ × ℕ)).length - 1))
      par ((A ++ List.replicate (n + 1) ((x, v, 0) : ℕ × ℕ × ℕ)).length - 1)) :
    rankDE
      (if 0 < srow (A ++ List.replicate (n + 1) ((x, v, 0) : ℕ × ℕ × ℕ))
            ((A ++ List.replicate (n + 1) ((x, v, 0) : ℕ × ℕ × ℕ)).length - 1) then
        entry (A ++ List.replicate (n + 1) ((x, v, 0) : ℕ × ℕ × ℕ)) 0
            ((A ++ List.replicate (n + 1) ((x, v, 0) : ℕ × ℕ × ℕ)).length - 1)
          - entry (A ++ List.replicate (n + 1) ((x, v, 0) : ℕ × ℕ × ℕ)) 0 par else 0)
      (if 1 < srow (A ++ List.replicate (n + 1) ((x, v, 0) : ℕ × ℕ × ℕ))
            ((A ++ List.replicate (n + 1) ((x, v, 0) : ℕ × ℕ × ℕ)).length - 1) then
        entry (A ++ List.replicate (n + 1) ((x, v, 0) : ℕ × ℕ × ℕ)) 1
            ((A ++ List.replicate (n + 1) ((x, v, 0) : ℕ × ℕ × ℕ)).length - 1)
          - entry (A ++ List.replicate (n + 1) ((x, v, 0) : ℕ × ℕ × ℕ)) 1 par else 0)
      = 1 := by
  rw [rankDE_eq_srow hpar, srow_last_of_append_replicate_one A x v n hv]


/-! ## 99. ★★★★★★★★ (W59)(a): **最小形では良い枝が起きません** —— 親は必ず `A`

写しは全部同じ列なので、**行 0 も行 1 も等号**。
⟹ ★ `nextrel0` / `nextrel1` は **狭義に小さい**列を要求 ⟹ ⛔ **塔に候補が 1 つも無い**
⟹ ⟹ ★★★★★ **親は必ず接頭辞 `A` の中** ＝ **常に残差**。 -/

/-- 写しの部分の値は、どこを見ても `q` そのもの。 -/
theorem entry_replicate_of_lt {q : ℕ × ℕ × ℕ} {m i : ℕ} (hi : i < m) (r : ℕ) :
    entry (List.replicate m q) r i = (if r = 0 then q.1 else if r = 1 then q.2.1 else q.2.2) := by
  show (if r = 0 then _ else if r = 1 then _ else _) = _
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [List.length_replicate]; omega), List.getElem_replicate]
  split_ifs <;> rfl

/-- ★★★★★★★★ **`srow = 0` の最小形: 行 0 の親は必ず `A` の中**。 -/
theorem nextrel0_src_lt_prefix_of_replicate {A : TrioSeq} {q : ℕ × ℕ × ℕ} {n c : ℕ}
    (h : nextrel0 (A ++ List.replicate (n + 1) q)
      c ((A ++ List.replicate (n + 1) q).length - 1)) : c < A.length := by
  have hlen : (A ++ List.replicate (n + 1) q).length = A.length + (n + 1) := by
    rw [List.length_append, List.length_replicate]
  have hlt : entry (A ++ List.replicate (n + 1) q) 0 c
      < entry (A ++ List.replicate (n + 1) q) 0 ((A ++ List.replicate (n + 1) q).length - 1) :=
    h.2.2.2.1
  have hclt : c < (A ++ List.replicate (n + 1) q).length := h.1
  by_contra hc
  push Not at hc
  obtain ⟨s, rfl⟩ : ∃ s, c = A.length + s := ⟨c - A.length, by omega⟩
  rw [show (A ++ List.replicate (n + 1) q).length - 1 = A.length + n from by omega,
    entry_append_right, entry_append_right,
    entry_replicate_of_lt (show s < n + 1 by omega) 0,
    entry_replicate_of_lt (show n < n + 1 by omega) 0] at hlt
  omega

/-- ★★★★★★★★ **`srow = 1` の最小形: 行 1 の親も必ず `A` の中**。
⟹ ★ ⟹ **写しは全部行 1 が等しい** ⟹ ⛔ **塔に候補が無い**。 -/
theorem nextrel1_src_lt_prefix_of_replicate {A : TrioSeq} {q : ℕ × ℕ × ℕ} {n c : ℕ}
    (h : nextrel1 (A ++ List.replicate (n + 1) q)
      c ((A ++ List.replicate (n + 1) q).length - 1)) : c < A.length := by
  have hlen : (A ++ List.replicate (n + 1) q).length = A.length + (n + 1) := by
    rw [List.length_append, List.length_replicate]
  have hlt : entry (A ++ List.replicate (n + 1) q) 1 c
      < entry (A ++ List.replicate (n + 1) q) 1 ((A ++ List.replicate (n + 1) q).length - 1) :=
    h.2.2.2.1
  have hclt : c < (A ++ List.replicate (n + 1) q).length := h.1
  by_contra hc
  push Not at hc
  obtain ⟨s, rfl⟩ : ∃ s, c = A.length + s := ⟨c - A.length, by omega⟩
  rw [show (A ++ List.replicate (n + 1) q).length - 1 = A.length + n from by omega,
    entry_append_right, entry_append_right,
    entry_replicate_of_lt (show s < n + 1 by omega) 1,
    entry_replicate_of_lt (show n < n + 1 by omega) 1] at hlt
  omega

/-- ★★★★★★★★ **行 2 も同じ** ⟹ ⟹ ★★★ **`srow` が何であれ、最小形の親は `A` の中**。 -/
theorem nextrel2_src_lt_prefix_of_replicate {A : TrioSeq} {q : ℕ × ℕ × ℕ} {n c : ℕ}
    (h : nextrel2 (A ++ List.replicate (n + 1) q)
      c ((A ++ List.replicate (n + 1) q).length - 1)) : c < A.length := by
  have hlen : (A ++ List.replicate (n + 1) q).length = A.length + (n + 1) := by
    rw [List.length_append, List.length_replicate]
  have hlt : entry (A ++ List.replicate (n + 1) q) 2 c
      < entry (A ++ List.replicate (n + 1) q) 2 ((A ++ List.replicate (n + 1) q).length - 1) :=
    h.2.2.2.1
  have hclt : c < (A ++ List.replicate (n + 1) q).length := h.1
  by_contra hc
  push Not at hc
  obtain ⟨s, rfl⟩ : ∃ s, c = A.length + s := ⟨c - A.length, by omega⟩
  rw [show (A ++ List.replicate (n + 1) q).length - 1 = A.length + n from by omega,
    entry_append_right, entry_append_right,
    entry_replicate_of_lt (show s < n + 1 by omega) 2,
    entry_replicate_of_lt (show n < n + 1 by omega) 2] at hlt
  omega

/-- ★★★★★★★★★ ⟹ **最小形では、どの行でも良い枝が起きません**（まとめ）。 -/
theorem nextR_src_lt_prefix_of_replicate {A : TrioSeq} {q : ℕ × ℕ × ℕ} {n c : ℕ} {i : ℕ}
    (h : nextR (A ++ List.replicate (n + 1) q) i
      c ((A ++ List.replicate (n + 1) q).length - 1)) : c < A.length := by
  unfold nextR at h
  split_ifs at h
  · exact nextrel0_src_lt_prefix_of_replicate h
  · exact nextrel1_src_lt_prefix_of_replicate h
  · exact nextrel2_src_lt_prefix_of_replicate h


/-! ## 100. ★★★★★★★★ (W60): **`row2pos Q = 0` の世界では `srow ≤ 1` が永久に保たれます**

行 2 は **`Lift1` でも `shiftr01` でも動きません**。
⟹ ★ ですから **塔を何段積んでも、窓を取っても、行 2 は 0 のまま**。
⟹ ⟹ ★★★★★ **`srow = 2` は出ません** ⟹ **2 族だけで閉じます**。 -/

/-- `row2pos M = 0` ⟺ **行 2 ≡ 0**。 -/
theorem row2pos_eq_zero_iff (M : TrioSeq) : row2pos M = 0 ↔ ∀ p ∈ M, p.2.2 = 0 := by
  unfold row2pos
  rw [List.countP_eq_zero]
  constructor
  · intro h p hp; have := h p hp; simp at this; omega
  · intro h p hp; simp [h p hp]

/-- ★★★ **行 2 ≡ 0 なら `srow ≤ 1`**（どの列でも）。 -/
theorem srow_le_one_of_zeroRow2 {M : TrioSeq} (h : ∀ p ∈ M, p.2.2 = 0) (j : ℕ) :
    srow M j ≤ 1 := srow_le_one_of_row2_zero (entry2_eq_zero_of_zeroRow2 h j)

/-- 行 2 ≡ 0 は **部分列**に遺伝します（窓・接頭辞・接尾辞すべて）。 -/
theorem zeroRow2_sublist {M N : TrioSeq} (hs : M.Sublist N) (h : ∀ p ∈ N, p.2.2 = 0) :
    ∀ p ∈ M, p.2.2 = 0 := fun p hp => h p (hs.mem hp)

/-- 行 2 ≡ 0 は **連結**でも保たれます。 -/
theorem zeroRow2_append {A B : TrioSeq} (hA : ∀ p ∈ A, p.2.2 = 0) (hB : ∀ p ∈ B, p.2.2 = 0) :
    ∀ p ∈ A ++ B, p.2.2 = 0 := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hA p h
  · exact hB p h

/-- ★★★★★★★★ **(W60)**: `row2pos A = 0` ∧ `row2pos Q = 0` なら、
**接頭辞つき塔のどの列も `srow ≤ 1`**。⟹ ★ **`n`, `d`, `e` に依りません**。 -/
theorem srow_le_one_prefix_mTower {A Q : TrioSeq} {d e n : ℕ}
    (hA : row2pos A = 0) (hQ : row2pos Q = 0) (j : ℕ) :
    srow (A ++ mTower Q d e n) j ≤ 1 :=
  srow_le_one_of_zeroRow2
    (zeroRow2_append ((row2pos_eq_zero_iff A).mp hA)
      (zeroRow2_mTower ((row2pos_eq_zero_iff Q).mp hQ))) j

/-- ★★★★★★★★ ⟹ **窓を取っても保たれます**（`drop` も `take` も部分列）。 -/
theorem srow_le_one_window {A Q : TrioSeq} {d e n p k : ℕ}
    (hA : row2pos A = 0) (hQ : row2pos Q = 0) (j : ℕ) :
    srow (((A ++ mTower Q d e n).drop p).take k) j ≤ 1 :=
  srow_le_one_of_zeroRow2
    (zeroRow2_sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))
      (zeroRow2_append ((row2pos_eq_zero_iff A).mp hA)
        (zeroRow2_mTower ((row2pos_eq_zero_iff Q).mp hQ)))) j

/-- ★★★★★ ⟹ **`row2pos` は窓で増えません**（部分列なので）。
⟹ ★ ⟹ **`row2pos = 0` の世界からは、出られません**。 -/
theorem row2pos_eq_zero_window {A Q : TrioSeq} {d e n p k : ℕ}
    (hA : row2pos A = 0) (hQ : row2pos Q = 0) :
    row2pos (((A ++ mTower Q d e n).drop p).take k) = 0 :=
  (row2pos_eq_zero_iff _).mpr
    (zeroRow2_sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))
      (zeroRow2_append ((row2pos_eq_zero_iff A).mp hA)
        (zeroRow2_mTower ((row2pos_eq_zero_iff Q).mp hQ))))


/-! ## 101. ★★★★★★★★ (W61): **良い枝の親は「最後の写し」の中** —— 既存の 2 本の具体化

末尾列は **第 `n−1` ブロックの相対位置 `|Q|−1`** です。
⟹ ★ **行 0**: `nextrel0_src_ge_block_of_deep`（(W53 続き)）を `k = n−1`, `r = |Q|−1` で。
⟹ ★ **行 1**: `prefix_mTower_nextrel1_src_ge`（(W56)）を同じ添字で。
⟹ ⟹ ★★★★★ **どちらも `d`, `e` に依りません**（team-lead の「`d, e > 0` で壊れそう」は杞憂でした）。 -/

/-- 末尾の添字の分解。 -/
theorem prefix_mTower_last_index (A Q : TrioSeq) (d e n : ℕ) (hQ : 0 < Q.length) (hn : 0 < n) :
    (A ++ mTower Q d e n).length - 1
      = A.length + ((n - 1) * Q.length + (Q.length - 1)) := by
  have h1 : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have h2 : (n - 1) * Q.length + Q.length = n * Q.length := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [Nat.succ_mul]
  rw [List.length_append, h1]; omega

/-- ★★★★★★★★ **(W61) の行 0**: `hr0 Q` ∧ `|Q| ≥ 2` なら、末尾の行 0 の親は **最後の写しの中**。
⟹ ★ **`d`, `e` は何でもよい**。 -/
theorem nextrel0_last_src_ge_last_block {A Q : TrioSeq} {d e n c : ℕ}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hQ2 : 2 ≤ Q.length) (hn : 0 < n)
    (h : nextrel0 (A ++ mTower Q d e n) c ((A ++ mTower Q d e n).length - 1)) :
    A.length + (n - 1) * Q.length ≤ c := by
  rw [prefix_mTower_last_index A Q d e n (by omega) hn] at h
  exact nextrel0_src_ge_block_of_deep (by omega) (by omega)
    (hr0 (Q.length - 1) (by omega) (by omega)) h

/-- ★★★★★★★★ **(W61) の行 1**: `Q` の末尾が `Q` の中で行 1 の親 `y` を持つなら、
末尾の行 1 の親は **`|A| + (n−1)|Q| + y` 以降**（＝ **最後の写しの中**）。 -/
theorem nextrel1_last_src_ge_last_block {A Q : TrioSeq} {d e n y c : ℕ}
    (hQ : 0 < Q.length) (hn : 0 < n) (hy : nextrel1 Q y (Q.length - 1))
    (h : nextrel1 (A ++ mTower Q d e n) c ((A ++ mTower Q d e n).length - 1)) :
    A.length + ((n - 1) * Q.length + y) ≤ c := by
  rw [prefix_mTower_last_index A Q d e n hQ hn] at h
  exact prefix_mTower_nextrel1_src_ge (by omega) (by omega) hy h

/-- ★★★★★ ⟹ **窓は最後の写しの中に収まります** ⟹ ★ **`|V| ≤ |Q|`**（行 0 版）。 -/
theorem window_le_of_last_row0 {A Q : TrioSeq} {d e n c : ℕ}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hQ2 : 2 ≤ Q.length) (hn : 0 < n)
    (h : nextrel0 (A ++ mTower Q d e n) c ((A ++ mTower Q d e n).length - 1)) :
    (A ++ mTower Q d e n).length - 1 - c < Q.length := by
  have hge := nextrel0_last_src_ge_last_block hr0 hQ2 hn h
  rw [prefix_mTower_last_index A Q d e n (by omega) hn]
  omega

/-- ★★★★★ ⟹ **行 1 版**（証人 `y` があれば、窓は `|Q| − 1 − y` 以下）。 -/
theorem window_le_of_last_row1 {A Q : TrioSeq} {d e n y c : ℕ}
    (hQ : 0 < Q.length) (hn : 0 < n) (hy : nextrel1 Q y (Q.length - 1))
    (h : nextrel1 (A ++ mTower Q d e n) c ((A ++ mTower Q d e n).length - 1)) :
    (A ++ mTower Q d e n).length - 1 - c < Q.length := by
  have hge := nextrel1_last_src_ge_last_block hQ hn hy h
  have hylt : y < Q.length - 1 := hy.2.2.1
  rw [prefix_mTower_last_index A Q d e n hQ hn]
  omega


/-! ## 102. ★★★★★★★★ 行 2 ＝ 1 の最小形 —— **(W59) がそのまま覆っています**

`Q = [(x,v,1)]` ⟹ **`srow = 2`** ⟹ **`rankDE = 2`**（(W44)）。
⟹ ★ そして **(W59) の `nextR_src_lt_prefix_of_replicate` は全行・全 `q`** なので、
⟹ ⟹ ★★★ **良い枝は起きず、`(|A|, n)` の二重帰納がそのまま回ります**。 -/

/-- ★★★★★ **`rankDE = srow` の使いやすい形**（`srow` の値を外から与える）。 -/
theorem rankDE_eq_of_srow_value {T : TrioSeq} {par s : ℕ}
    (hs : srow T (T.length - 1) = s) (hpar : nextR T s par (T.length - 1)) :
    rankDE (if 0 < s then entry T 0 (T.length - 1) - entry T 0 par else 0)
        (if 1 < s then entry T 1 (T.length - 1) - entry T 1 par else 0) = s := by
  subst hs; exact rankDE_eq_srow hpar

/-- ★★★★★ **行 2 ＝ 1 の最小形の末尾は `srow = 2`**。 -/
theorem srow_last_of_append_replicate_two (A : TrioSeq) (x v z n : ℕ) (hz : 0 < z) :
    srow (A ++ List.replicate (n + 1) ((x, v, z) : ℕ × ℕ × ℕ))
      ((A ++ List.replicate (n + 1) ((x, v, z) : ℕ × ℕ × ℕ)).length - 1) = 2 := by
  rw [srow_last_of_append_replicate_gen]
  simp [hz]

/-- ★★★★★★★★ ⟹ **行 2 ＝ 1 の最小形では `rankDE = 2`**（`d0 > 0`, `d1 > 0`）。
⟹ ★ ですが **(W59) より良い枝は起きない**ので、⟹ ★★ **`(|A|, n)` の帰納は同じように回ります**。 -/
theorem rankDE_two_of_srow2_minimal {A : TrioSeq} {x v z n par : ℕ} (hz : 0 < z)
    (hpar : nextR (A ++ List.replicate (n + 1) ((x, v, z) : ℕ × ℕ × ℕ)) 2 par
      ((A ++ List.replicate (n + 1) ((x, v, z) : ℕ × ℕ × ℕ)).length - 1)) :
    rankDE
      (if 0 < 2 then
        entry (A ++ List.replicate (n + 1) ((x, v, z) : ℕ × ℕ × ℕ)) 0
            ((A ++ List.replicate (n + 1) ((x, v, z) : ℕ × ℕ × ℕ)).length - 1)
          - entry (A ++ List.replicate (n + 1) ((x, v, z) : ℕ × ℕ × ℕ)) 0 par else 0)
      (if 1 < 2 then
        entry (A ++ List.replicate (n + 1) ((x, v, z) : ℕ × ℕ × ℕ)) 1
            ((A ++ List.replicate (n + 1) ((x, v, z) : ℕ × ℕ × ℕ)).length - 1)
          - entry (A ++ List.replicate (n + 1) ((x, v, z) : ℕ × ℕ × ℕ)) 1 par else 0)
      = 2 :=
  rankDE_eq_of_srow_value (srow_last_of_append_replicate_two A x v z n hz) hpar

/-- ★★★★★★★★★ ⟹ **最小形のまとめ**: `srow` は `q` の行 1・行 2 だけで決まり、
**どの値でも良い枝は起きず**（(W59)）、**後継の形は同じ**（`minimal_successor_shape_gen`）。
⟹ ★ ですから **`(|A|, n)` の二重帰納は、行 2 ＝ 1 でも回ります**。 -/
theorem minimal_form_summary (A : TrioSeq) (q : ℕ × ℕ × ℕ) (n c : ℕ) (hc : c ≤ A.length) :
    srow (A ++ List.replicate (n + 1) q) ((A ++ List.replicate (n + 1) q).length - 1)
        = (if 0 < q.2.2 then 2 else if 0 < q.2.1 then 1 else 0)
      ∧ ((A ++ List.replicate (n + 1) q).drop c).dropLast = A.drop c ++ List.replicate n q
      ∧ ∀ i c', nextR (A ++ List.replicate (n + 1) q) i c'
          ((A ++ List.replicate (n + 1) q).length - 1) → c' < A.length :=
  ⟨srow_last_of_append_replicate_gen A q n, minimal_successor_shape_gen A q n c hc,
    fun _ _ h => nextR_src_lt_prefix_of_replicate h⟩


/-! ## 103. ★★★★★★★★ `le1` の写し内移送 —— **`e = 0` なら通ります**

`nextrel1` の最小性は **`le0` 祖先すべて**の上ですが、
⟹ ★ 候補 `x` は **`k|Q|+u < x ≤ k|Q|+v`** に閉じ込められます（`u < v < |Q|`）
⟹ ⟹ ★★ **同じ写しの中**です ⟹ ★ **逆向きの `le0` 移送**があれば最小性が移ります。

⚠ **`e > 0` では詰まります**（下の注記）。 -/

/-- `nextrel0` の鎖は添字を増やします。 -/
theorem rtg0_le {M : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 M) a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl a
  | @tail c d _ hcd ih => exact le_trans ih (le_of_lt hcd.2.2.1)

/-- ★★★★★ **逆向きの `le0` 移送**: 写しの中に閉じた鎖は、`Q` の鎖に戻せます。 -/
theorem rtg0_mTower_intra_block_rev (Q : TrioSeq) {d e n k : ℕ} (hk : k < n)
    {x y : ℕ} (hx : k * Q.length ≤ x) (hy : y < (k + 1) * Q.length)
    (h : Relation.ReflTransGen (nextrel0 (mTower Q d e n)) x y) :
    Relation.ReflTransGen (nextrel0 Q) (x - k * Q.length) (y - k * Q.length) := by
  have hsk : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
  revert hy
  induction h with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | @tail c y' hxc hcy ih =>
      intro hy'
      have hcy' : c < y' := hcy.2.2.1
      have hxc2 : x ≤ c := rtg0_le hxc
      have hstep : nextrel0 Q (c - k * Q.length) (y' - k * Q.length) := by
        have hcv : k * Q.length + (c - k * Q.length) = c := by omega
        have hyv : k * Q.length + (y' - k * Q.length) = y' := by omega
        refine (nextrel0_mTower_intra_block Q (d := d) (e := e) hk
          (show c - k * Q.length < Q.length by omega)
          (show y' - k * Q.length < Q.length by omega)).mp ?_
        rw [hcv, hyv]; exact hcy
      exact (ih (by omega)).tail hstep

/-- ★★★★★★★★ **`nextrel1` の写し内移送（`e = 0`）**。
⟹ ★ 最小性の候補は **同じ写しの中**に閉じるので、`Q` の最小性がそのまま移ります。 -/
theorem nextrel1_mTower_intra_block_of_e_zero (Q : TrioSeq) {d n k : ℕ} (hk : k < n)
    {u v : ℕ} (h : nextrel1 Q u v) :
    nextrel1 (mTower Q d 0 n) (k * Q.length + u) (k * Q.length + v) := by
  have hu : u < Q.length := h.1
  have hv : v < Q.length := h.2.1
  have huv : u < v := h.2.2.1
  have hlen : (mTower Q d 0 n).length = n * Q.length := mTower_length Q d 0 n
  have hkn : (k + 1) * Q.length ≤ n * Q.length := Nat.mul_le_mul_right _ (by omega)
  have hsk : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
  have hent : ∀ i, i < Q.length →
      entry (mTower Q d 0 n) 1 (k * Q.length + i) = entry Q 1 i := by
    intro i hi
    rw [entry1_mTower_block_formula Q hk hi]
    split_ifs <;> omega
  refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
  · rw [hent u hu, hent v hv]; exact h.2.2.2.1
  · exact ⟨by omega, by omega, rtg0_mTower_intra_block Q hk hu hv h.2.2.2.2.1.2.2⟩
  · intro x hx
    obtain ⟨hlt, hle0⟩ := hx
    have hxle : x ≤ k * Q.length + v := rtg0_le hle0.2.2
    obtain ⟨w, rfl⟩ : ∃ w, x = k * Q.length + w := ⟨x - k * Q.length, by omega⟩
    have hw : w < Q.length := by omega
    have hle0Q : le0 Q w v := by
      refine ⟨hw, hv, ?_⟩
      have := rtg0_mTower_intra_block_rev Q hk (x := k * Q.length + w)
        (y := k * Q.length + v) (by omega) (by omega) hle0.2.2
      simpa using this
    rw [hent v hv, hent w hw]
    exact h.2.2.2.2.2 w ⟨by omega, hle0Q⟩

/-- ★★★★★★★★ ⟹ **`le1` の写し内移送（`e = 0`）**。
⟹ ★ ⟹ **(W56) の `hcone` と (W61) の行 2 の穴が、`e = 0` では埋まります**。 -/
theorem rtg1_mTower_intra_block_of_e_zero (Q : TrioSeq) {d n k : ℕ} (hk : k < n) {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel1 Q) a b) :
    Relation.ReflTransGen (nextrel1 (mTower Q d 0 n)) (k * Q.length + a) (k * Q.length + b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c b' _ hcb ih => exact ih.tail (nextrel1_mTower_intra_block_of_e_zero Q hk hcb)

/-- ★★★★★★★★ ⟹ **`le1` の写し内移送（`e = 0`）**。
⟹ ★ ⟹ **(W56) の `hcone` と (W61) の行 2 の穴が、`e = 0` では埋まります**。 -/
theorem le1_mTower_intra_block_of_e_zero (Q : TrioSeq) {d n k : ℕ} (hk : k < n)
    {a b : ℕ} (h : le1 Q a b) :
    le1 (mTower Q d 0 n) (k * Q.length + a) (k * Q.length + b) := by
  have hlen : (mTower Q d 0 n).length = n * Q.length := mTower_length Q d 0 n
  have hkn : (k + 1) * Q.length ≤ n * Q.length := Nat.mul_le_mul_right _ (by omega)
  have hsk : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
  obtain ⟨ha, hb, hrt⟩ := h
  exact ⟨by omega, by omega, rtg1_mTower_intra_block_of_e_zero Q hk hrt⟩


/-- ★★★★★★★★ ⟹ **(W56) の行 2 の穴が `e = 0` で埋まりました**（仮定 `hcone` が消えます）。 -/
theorem prefix_mTower_row2_cross_implies_orphan_of_e_zero {A Q : TrioSeq} {d n k j c : ℕ}
    (hk : k < n) (hj : j < Q.length) (hc : c < A.length)
    (h : nextrel2 (A ++ mTower Q d 0 n) c (A.length + (k * Q.length + j))) :
    ¬ hasParent Q 2 j := by
  refine prefix_mTower_row2_cross_implies_orphan hk hj hc ?_ h
  intro y hy
  exact (le1_append_right _ _ _ _).mpr
    (le1_mTower_intra_block_of_e_zero Q hk hy.2.2.2.2.1)

/-- ★★★★★★★ ⟹ **良い枝の側（対偶）**: `Q` の中で行 2 の親を持てば、越境しません。 -/
theorem prefix_mTower_row2_src_ge_of_hasParent_e_zero {A Q : TrioSeq} {d n k j c : ℕ}
    (hk : k < n) (hj : j < Q.length) (hpar : hasParent Q 2 j)
    (h : nextrel2 (A ++ mTower Q d 0 n) c (A.length + (k * Q.length + j))) :
    A.length ≤ c := by
  by_contra hcc
  push Not at hcc
  exact prefix_mTower_row2_cross_implies_orphan_of_e_zero hk hj hcc h hpar


/-! ## 104. ★★★★★★★★★ **`window_lt_of_periodic0` の行 1 版**（L3 `L106:10037` の穴）

`nextrel1` の最小性は **`le0` 祖先**の上なので、**`le0 T (c+m) t`** が要ります。
⟹ ★★★★★★★★ **鍵**: **`c+m` は `c` から `t` への `le0` の鎖の上に必ず載っています**。
⟹ ★ 理由: 鎖の上で行 0 は狭義に増えます。⟹ ★★ もし鎖が `c+m` を跨げば、
その 1 歩の**最小性**が `entry T 0 (跨いだ先) ≤ entry T 0 (c+m) = entry T 0 c` を強制し、
⟹ ⟹ ⛔ **`entry T 0 c ≤ entry T 0 (跨ぐ元) < entry T 0 (跨いだ先)`** と矛盾します。 -/

/-- ★★★★★★★★ **鎖は `c+m` を跨げません** ⟹ **`le0 T (c+m) t`**。 -/
theorem rtg0_shift_of_periodic {T : TrioSeq} {a m c t : ℕ} (hm : 0 < m)
    (hper : ∀ x, a ≤ x → x + m ≤ t → entry T 0 (x + m) = entry T 0 x)
    (hc : a ≤ c) (hct : c + m ≤ t)
    (h : Relation.ReflTransGen (nextrel0 T) c t) :
    Relation.ReflTransGen (nextrel0 T) (c + m) t := by
  have hcm : entry T 0 (c + m) = entry T 0 c := hper c hc hct
  have key : ∀ z, Relation.ReflTransGen (nextrel0 T) z t →
      c ≤ z → z ≤ c + m → entry T 0 c ≤ entry T 0 z →
      Relation.ReflTransGen (nextrel0 T) (c + m) t := by
    intro z hz
    induction hz using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro _ h2 _
        have : t = c + m := by omega
        rw [this]
    | @head z b h' hrest ih =>
        intro hcz hzm hval
        rcases eq_or_lt_of_le hzm with heq | hzlt
        · rw [← heq]; exact hrest.head h'
        · have hbm : b ≤ c + m := by
            by_contra hb
            push Not at hb
            have hmin := h'.2.2.2.2 (c + m) ⟨by omega, by omega⟩
            have hgt := h'.2.2.2.1
            omega
          exact ih (by have := h'.2.2.1; omega) hbm (by have := h'.2.2.2.1; omega)
  exact key c h (le_refl c) (by omega) (le_refl _)

/-- ★★★★★★★★★ **(行 1 版)**: 周期部分では **`nextrel1` の窓も周期より短い**。
⟹ ★ 前提は **行 0 と行 1 の周期性**だけ（`le0` の仮定は要りません）。 -/
theorem window_lt_of_periodic1 {T : TrioSeq} {a m c t : ℕ} (hm : 0 < m)
    (hper0 : ∀ x, a ≤ x → x + m ≤ t → entry T 0 (x + m) = entry T 0 x)
    (hper1 : ∀ x, a ≤ x → x + m ≤ t → entry T 1 (x + m) = entry T 1 x)
    (hc : a ≤ c) (h : nextrel1 T c t) : t - c < m := by
  by_contra hcon
  push Not at hcon
  have hlt : c < t := h.2.2.1
  have htlen : t < T.length := h.2.1
  have hct : c + m ≤ t := by omega
  have hle0 : le0 T (c + m) t :=
    ⟨by omega, htlen, rtg0_shift_of_periodic hm hper0 hc hct h.2.2.2.2.1.2.2⟩
  have hmin := h.2.2.2.2.2 (c + m) ⟨by omega, hle0⟩
  rw [hper1 c hc hct] at hmin
  have := h.2.2.2.1
  omega

/-- ★★★★★ **`srow = 1` の親について述べた形**（L3 の `parent_dist_lt_of_periodic0` の行 1 版）。 -/
theorem parent_dist_lt_of_periodic1 {T : TrioSeq} {a m t : ℕ} (hm : 0 < m)
    (hper0 : ∀ x, a ≤ x → x + m ≤ t → entry T 0 (x + m) = entry T 0 x)
    (hper1 : ∀ x, a ≤ x → x + m ≤ t → entry T 1 (x + m) = entry T 1 x)
    (hs : srow T t = 1) (hpar : hasParent T (srow T t) t)
    (hc : a ≤ parent T (srow T t) t) :
    t - parent T (srow T t) t < m := by
  have h1 := parent_nextR hpar
  rw [hs] at h1 hc ⊢
  rw [nextR, if_neg (by omega), if_pos rfl] at h1
  exact window_lt_of_periodic1 hm hper0 hper1 hc h1


/-! ## 105. ★★★★★★★★★ **`PrefixCopies`（`e = 0`）の 3 行を 1 本に** —— `nextR` 版

行 0 も同じ形で書けます（証人 `nextrel0 Q y j` があれば親は同じ写しの中）。
⟹ ★★★★★ **3 行そろえて `nextR` 1 本**にします。⟹ ★ **L3 が `PrefixCopies` で使う形**です。 -/

/-- ★★★★★★★★ **行 0 の写し内証人**（`d`, `e` は何でもよい）。 -/
theorem prefix_mTower_nextrel0_src_ge {A Q : TrioSeq} {d e n k j y c : ℕ}
    (hk : k < n) (hj : j < Q.length) (hy : nextrel0 Q y j)
    (h : nextrel0 (A ++ mTower Q d e n) c (A.length + (k * Q.length + j))) :
    A.length + (k * Q.length + y) ≤ c := by
  have hyQ : y < Q.length := hy.1
  have hylt : y < j := hy.2.2.1
  have hlt : entry Q 0 y < entry Q 0 j := hy.2.2.2.1
  by_contra hc
  push Not at hc
  have hmin := h.2.2.2.2 (A.length + (k * Q.length + y)) ⟨by omega, by omega⟩
  rw [entry_append_right, entry_append_right,
    entry0_mTower_block' Q hk hj, entry0_mTower_block' Q hk hyQ] at hmin
  omega

/-- ★★★★★★★★ **行 0: 越境 ⟹ `Q` の中で行 0 の孤児**。 -/
theorem prefix_mTower_row0_cross_implies_orphan {A Q : TrioSeq} {d e n k j c : ℕ}
    (hk : k < n) (hj : j < Q.length) (hc : c < A.length)
    (h : nextrel0 (A ++ mTower Q d e n) c (A.length + (k * Q.length + j))) :
    ¬ hasParent Q 0 j := by
  intro hpar
  obtain ⟨y, hy, -⟩ := hpar
  have hy' : nextrel0 Q y j := by simpa [nextR] using hy
  have := prefix_mTower_nextrel0_src_ge hk hj hy' h
  omega

/-- ★★★★★★★★★ **(まとめ) `PrefixCopies`（`e = 0`）の 3 行**:
**越境 ⟹ 的は `Q` の中で（その行の）孤児**。⟹ ★ **`i` は 0, 1, 2 のどれでもよい**。 -/
theorem prefix_mTower_nextrel2_src_ge_of_e_zero {A Q : TrioSeq} {d n k j y c : ℕ}
    (hk : k < n) (hj : j < Q.length) (hy : nextrel2 Q y j)
    (h : nextrel2 (A ++ mTower Q d 0 n) c (A.length + (k * Q.length + j))) :
    A.length + (k * Q.length + y) ≤ c := by
  have hylt : y < j := hy.2.2.1
  have hyQ : y < Q.length := by omega
  have hlt : entry Q 2 y < entry Q 2 j := hy.2.2.2.1
  by_contra hc
  push Not at hc
  have hle1 : le1 (A ++ mTower Q d 0 n)
      (A.length + (k * Q.length + y)) (A.length + (k * Q.length + j)) :=
    (le1_append_right _ _ _ _).mpr (le1_mTower_intra_block_of_e_zero Q hk hy.2.2.2.2.1)
  have hmin := h.2.2.2.2.2 (A.length + (k * Q.length + y)) ⟨by omega, hle1⟩
  rw [entry_append_right, entry_append_right, mTower_entry hk hj,
    mTower_entry hk hyQ, entry2_Lift1, entry2_Lift1,
    entry2_shiftr01, entry2_shiftr01] at hmin
  omega

/-- ★★★★★★★★★ **(まとめ) `PrefixCopies`（`e = 0`）の 3 行**:
**越境 ⟹ 的は `Q` の中で（その行の）孤児**。⟹ ★ **`i` は 0, 1, 2 のどれでもよい**。 -/
theorem prefix_mTower_cross_implies_orphan_of_e_zero {A Q : TrioSeq} {d n k j c i : ℕ}
    (hk : k < n) (hj : j < Q.length) (hc : c < A.length)
    (h : nextR (A ++ mTower Q d 0 n) i c (A.length + (k * Q.length + j))) :
    ¬ hasParent Q i j := by
  intro hpar
  obtain ⟨y, hy, -⟩ := hpar
  unfold nextR at h hy
  split_ifs at h hy with h0 h1
  · have := prefix_mTower_nextrel0_src_ge hk hj hy h; omega
  · have := prefix_mTower_nextrel1_src_ge hk hj hy h; omega
  · have := prefix_mTower_nextrel2_src_ge_of_e_zero hk hj hy h; omega

/-- ★★★★★★★★★ ⟹ **対偶（L3 が使う形）**: **`Q` の中で（その行の）親を持てば、越境しません**。 -/
theorem prefix_mTower_src_ge_of_hasParent_of_e_zero {A Q : TrioSeq} {d n k j c i : ℕ}
    (hk : k < n) (hj : j < Q.length) (hpar : hasParent Q i j)
    (h : nextR (A ++ mTower Q d 0 n) i c (A.length + (k * Q.length + j))) :
    A.length ≤ c := by
  by_contra hcc
  push Not at hcc
  exact prefix_mTower_cross_implies_orphan_of_e_zero hk hj hcc h hpar


/-! ## 106. ★★★★★★ **良い枝の連鎖は `|Q|` 回で止まります**

材料は 2 つとも既に緑です:
⟹ ★ **(i) 良い枝は `|Q|` を無条件に真に減らす** … `window_le_of_last_row0` / `window_le_of_last_row1`（(W61)）
⟹ ★ **(ii) `|Q| = 1` では良い枝が起きない** … `nextR_src_lt_prefix_of_replicate`（(W59)）
⟹ ⟹ ★★★ あとは **「真に減る ℕ の列は有限」**を足すだけです。
⚠ ⛔ **測度にはなりません**（`|A|` が良い枝で増えるため）。⟹ ★ **「連鎖が有限」という事実だけ**です。 -/

/-- **真に減る ℕ の列は無限には続きません**。 -/
theorem no_infinite_strict_desc (f : ℕ → ℕ) (hdec : ∀ i, f (i + 1) < f i) : False := by
  have key : ∀ i, f i + i ≤ f 0 := by
    intro i
    induction i with
    | zero => omega
    | succ m ih => have := hdec m; omega
  have := key (f 0 + 1)
  omega

/-- ★★★★★★ **連鎖の長さは初項で抑えられます** ⟹ ★ **良い枝は連続して高々 `|Q|` 回**。 -/
theorem chain_length_le_of_strict_desc (f : ℕ → ℕ) (k : ℕ)
    (hdec : ∀ i, i < k → f (i + 1) < f i) : k ≤ f 0 := by
  have key : ∀ i, i ≤ k → f i + i ≤ f 0 := by
    intro i
    induction i with
    | zero => intro _; omega
    | succ m ih =>
        intro hm
        have h1 := ih (by omega)
        have h2 := hdec m (by omega)
        omega
  have := key k (le_refl k)
  omega

/-- ★★★★★★★ **良い枝の連鎖は有限**（上の 2 本を、良い枝の言葉で）。
`sz i` を第 `i` 段の基底の長さとすると、**良い枝が続く限り `sz` は真に減る**（(W61)）ので、
⟹ ★ **`k` 回続いたなら `k ≤ sz 0`** ⟹ ⟹ ★★ **`|Q|` 回で止まります**。
⟹ ⛔ そして **`sz = 1` では良い枝が起きません**（(W59)）⟹ ★ **底に達したら必ず残差**です。 -/
theorem good_chain_le_initial (sz : ℕ → ℕ) (k : ℕ)
    (hgood : ∀ i, i < k → sz (i + 1) < sz i) : k ≤ sz 0 :=
  chain_length_le_of_strict_desc sz k hgood


/-! ## 107. ★★★★★★★★★ (W62): **`WSnocOpen1` の親は「直前の列」になり得ます**

`WSnocOpen1`（`L53Subst:3727`）の的は **`T = C ++ [p]` の最後の列（添字 `|C|`）**。
⟹ ★★★★★ **その直前の列（添字 `|C|−1`）との間には、何もありません**
⟹ ⟹ ★★★ ですから **`nextrel` の最小性の条件が空虚**になり、
⟹ ⟹ ⟹ ★★★★★★★★ **「直前の列が条件を満たせば、それが親」**です ⟹ **窓が空** ⟹ **`oper` が自明**。

⟹ ★ R2 の実測「**行 2 ＝ 1 の列は `p` のすぐ手前（距離 1 が 47.41%）**」が、ここに刺さります。 -/

/-- ★★★ **`snoc` の末尾の `srow`**（`p` の行 1・行 2 だけで決まります）。 -/
theorem srow_snoc (C : TrioSeq) (p : ℕ × ℕ × ℕ) :
    srow (C ++ [p]) C.length = if 0 < p.2.2 then 2 else if 0 < p.2.1 then 1 else 0 := by
  have h : ∀ i, entry (C ++ [p]) i C.length = entry [p] i 0 := by
    intro i; simpa using entry_append_right C [p] i 0
  have hp : ∀ i, entry [p] i 0 = (if i = 0 then p.1 else if i = 1 then p.2.1 else p.2.2) := by
    intro i; show (if i = 0 then _ else if i = 1 then _ else _) = _; split_ifs <;> rfl
  unfold srow
  rw [h 2, h 1, hp 2, hp 1]
  simp

/-- ★★★★★★★★ **直前の列が浅ければ、それが行 0 の親**（最小性の条件が空虚）。 -/
theorem nextrel0_snoc_prev {C : TrioSeq} {p : ℕ × ℕ × ℕ} (hC : C ≠ [])
    (h : entry C 0 (C.length - 1) < p.1) :
    nextrel0 (C ++ [p]) (C.length - 1) C.length := by
  have hlen : 0 < C.length := List.length_pos_iff.mpr hC
  have hTlen : (C ++ [p]).length = C.length + 1 := by simp
  have hprev : ∀ i, entry (C ++ [p]) i (C.length - 1) = entry C i (C.length - 1) :=
    fun i => entry_append_left C [p] (by omega)
  have hlast : ∀ i, entry (C ++ [p]) i C.length
      = (if i = 0 then p.1 else if i = 1 then p.2.1 else p.2.2) := by
    intro i
    have := entry_append_right C [p] i 0
    simp only [Nat.add_zero] at this
    rw [this]
    show (if i = 0 then _ else if i = 1 then _ else _) = _
    split_ifs <;> rfl
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · rw [hprev 0, hlast 0]; simpa using h
  · intro j hj; omega

/-- ★★★★★★★★★ **`srow = 1` の場合: 直前の列が行 0 でも行 1 でも小さいなら、それが親**。
⟹ ★ ⟹ **窓が空**（`|V| = 0`）⟹ ⟹ ★★ **`oper` は 1 列を繰り返すだけ**になります。 -/
theorem nextrel1_snoc_prev {C : TrioSeq} {p : ℕ × ℕ × ℕ} (hC : C ≠ [])
    (h0 : entry C 0 (C.length - 1) < p.1) (h1 : entry C 1 (C.length - 1) < p.2.1) :
    nextrel1 (C ++ [p]) (C.length - 1) C.length := by
  have hlen : 0 < C.length := List.length_pos_iff.mpr hC
  have hTlen : (C ++ [p]).length = C.length + 1 := by simp
  have hn0 := nextrel0_snoc_prev hC h0
  have hprev : ∀ i, entry (C ++ [p]) i (C.length - 1) = entry C i (C.length - 1) :=
    fun i => entry_append_left C [p] (by omega)
  have hlast1 : entry (C ++ [p]) 1 C.length = p.2.1 := by
    have := entry_append_right C [p] 1 0
    simp only [Nat.add_zero] at this
    rw [this]; rfl
  refine ⟨by omega, by omega, by omega, ?_, ⟨by omega, by omega, Relation.ReflTransGen.single hn0⟩, ?_⟩
  · rw [hprev 1, hlast1]; exact h1
  · rintro x ⟨hx1, hx2⟩
    have hxle : x ≤ C.length := rtg0_le hx2.2.2
    have hxeq : x = C.length := by omega
    subst hxeq
    exact le_refl _

/-- ★★★★★★★★ ⟹ **行 1 の親は直前の列より前には行けません**（証人があるとき）。 -/
theorem nextrel1_snoc_src_ge {C : TrioSeq} {p : ℕ × ℕ × ℕ} {c : ℕ} (hC : C ≠ [])
    (h0 : entry C 0 (C.length - 1) < p.1) (h1 : entry C 1 (C.length - 1) < p.2.1)
    (h : nextrel1 (C ++ [p]) c C.length) : C.length - 1 ≤ c := by
  have hlen : 0 < C.length := List.length_pos_iff.mpr hC
  by_contra hc
  push Not at hc
  have hn0 := nextrel0_snoc_prev hC h0
  have hprev : ∀ i, entry (C ++ [p]) i (C.length - 1) = entry C i (C.length - 1) :=
    fun i => entry_append_left C [p] (by omega)
  have hlast1 : entry (C ++ [p]) 1 C.length = p.2.1 := by
    have := entry_append_right C [p] 1 0
    simp only [Nat.add_zero] at this
    rw [this]; rfl
  have hmin := h.2.2.2.2.2 (C.length - 1)
    ⟨hc, by exact ⟨by simp; omega, by simp, Relation.ReflTransGen.single hn0⟩⟩
  rw [hprev 1, hlast1] at hmin
  omega


/-! ## 108. ★★★★★★★★★ (W62 続き): **直前が親でないとき —— `amin` が決めます**

直前の列が条件を満たさないとき、行 0 の親 `c` はもっと前です。
⟹ ★★★★★ そのとき **`|C|` の行 0 の祖先 ＝ `{|C|} ∪ (c の祖先)`**（`nextrel0` の始点は一意）
⟹ ⟹ ★★★★★★★★ ですから **行 1 の親があるかどうかは `amin (C ++ [p]) c` と `p.2.1` の比較**で決まります。 -/

/-- ★★★★★★★★ **`amin` が `p` の行 1 より小さければ、行 1 の親がある**。
⟹ ★ 前提は **行 0 の親 `c` と、`c` での `amin`** だけ。 -/
theorem hasParent1_snoc_of_amin {C : TrioSeq} {p : ℕ × ℕ × ℕ} {c : ℕ}
    (h : nextrel0 (C ++ [p]) c C.length) (hlt : amin (C ++ [p]) c < p.2.1) :
    hasParent (C ++ [p]) 1 C.length := by
  have hTlen : (C ++ [p]).length = C.length + 1 := by simp
  have hlast1 : entry (C ++ [p]) 1 C.length = p.2.1 := by
    have := entry_append_right C [p] 1 0
    simp only [Nat.add_zero] at this
    rw [this]; rfl
  obtain ⟨y, hy, hey⟩ := amin_mem (C ++ [p]) c
  refine hasParent1_of_le0_witness (by omega) (hy.tail h) ?_
  rw [hey, hlast1]; exact hlt

/-- ★★★★★★★★ ⟹ **対偶: 行 1 の孤児なら `amin` は `p` の行 1 以上**。 -/
theorem amin_ge_of_orphan1_snoc {C : TrioSeq} {p : ℕ × ℕ × ℕ} {c : ℕ}
    (h : nextrel0 (C ++ [p]) c C.length)
    (horph : ¬ hasParent (C ++ [p]) 1 C.length) : p.2.1 ≤ amin (C ++ [p]) c := by
  by_contra hc
  push Not at hc
  exact horph (hasParent1_snoc_of_amin h hc)

/-- ★★★★★ **直前の列は、行 0 の親でなくても `amin` の上界をくれます**
（`c` から `|C|−1` までが `le0` で繋がっているとき）。 -/
theorem amin_snoc_le_of_le0 {C : TrioSeq} {p : ℕ × ℕ × ℕ} {c y : ℕ}
    (hy : Relation.ReflTransGen (nextrel0 (C ++ [p])) y c) :
    amin (C ++ [p]) c ≤ entry (C ++ [p]) 1 y := amin_le hy

/-- ★★★★★★★★★ ⟹ **(W62) のまとめ（行 1）**: `srow = 1` の場合、
**行 1 の親があるかどうかは `amin (C ++ [p]) c < p.2.1` と同値**（`c` ＝ 行 0 の親）。
⟹ ★ **⟸ は上**、⟹ **⟹ は次**（親 `y` は `c` の祖先か `|C|` 自身）。 -/
theorem hasParent1_snoc_iff_amin {C : TrioSeq} {p : ℕ × ℕ × ℕ} {c : ℕ}
    (h : nextrel0 (C ++ [p]) c C.length)
    (huniq : ∀ y, Relation.ReflTransGen (nextrel0 (C ++ [p])) y C.length →
      y = C.length ∨ Relation.ReflTransGen (nextrel0 (C ++ [p])) y c) :
    hasParent (C ++ [p]) 1 C.length ↔ amin (C ++ [p]) c < p.2.1 := by
  have hTlen : (C ++ [p]).length = C.length + 1 := by simp
  have hlast1 : entry (C ++ [p]) 1 C.length = p.2.1 := by
    have := entry_append_right C [p] 1 0
    simp only [Nat.add_zero] at this
    rw [this]; rfl
  constructor
  · intro hpar
    rw [hasParent1_iff_amin_lt (by omega), hlast1] at hpar
    obtain ⟨y, hy, hey⟩ := amin_mem (C ++ [p]) C.length
    rcases huniq y hy with rfl | hyc
    · rw [hlast1] at hey; omega
    · exact lt_of_le_of_lt (amin_le hyc) (by rw [hey]; exact hpar)
  · exact hasParent1_snoc_of_amin h


/-- ★★★★★ **行 0 の祖先の分解**（`nextrel0` の始点の一意性から）:
`t` の祖先は **`t` 自身か、その親 `c` の祖先**です。 -/
theorem rtg0_ancestor_split {M : TrioSeq} {c t y : ℕ} (h : nextrel0 M c t)
    (hy : Relation.ReflTransGen (nextrel0 M) y t) :
    y = t ∨ Relation.ReflTransGen (nextrel0 M) y c := by
  rcases Relation.ReflTransGen.cases_tail hy with h1 | ⟨c', hc1, hc2⟩
  · exact Or.inl h1.symm
  · exact Or.inr (by rw [← nextrel0_src_unique hc2 h]; exact hc1)

/-- ★★★★★★★★★ ⟹ **(W62) の行 1、仮定なしの形**:
**行 1 の親がある ⟺ `amin (C ++ [p]) c < p.2.1`**（`c` ＝ 行 0 の親）。 -/
theorem hasParent1_snoc_iff_amin' {C : TrioSeq} {p : ℕ × ℕ × ℕ} {c : ℕ}
    (h : nextrel0 (C ++ [p]) c C.length) :
    hasParent (C ++ [p]) 1 C.length ↔ amin (C ++ [p]) c < p.2.1 :=
  hasParent1_snoc_iff_amin h (fun _ hy => rtg0_ancestor_split h hy)


/-! ## 109. ★★★★★★★★★★ (W63): **「直前が親」の窓は 1 列** —— ただし `replicate` ではありません

⚠ **自己訂正**: 私は前便で「窓が空（`|V| = 0`）」と書きましたが、**`|V| = 1`** が正しいです
（`|T| − 1 − 親 = (|C|+1) − 1 − (|C|−1) = 1`）。⟹ ★ team-lead の計算が正しいです。

⟹ ⛔ そして **`replicate` の最小形には帰着しません**: `srow = 1` なら **`d0 > 0`**（(W44)）なので、
写しは **行 0 が `d0` ずつ増えます** ⟹ ⟹ ★ **同一ではありません**。
⟹ ★★★★★ **ですが `d1 = 0` なので、行 1 と行 2 は全写しで同じ**です。
⟹ ⟹ ★★★★★★★★ ⟹ **行 1・行 2 の親は、塔の中に絶対にいません** ⟹ **常に接頭辞** ⟹ **`|A|` が減ります**。 -/

/-- 1 列基底の塔の行 1（`d1 = 0` なら全写しで同じ）。 -/
theorem entry1_mTower_singleton {V : TrioSeq} {d0 m s : ℕ} (hV : V.length = 1) (hs : s < m) :
    entry (mTower V d0 0 m) 1 s = entry V 1 0 := by
  have h : s = s * V.length + 0 := by rw [hV]; omega
  rw [h, entry1_mTower_block_formula V hs (by omega)]
  split_ifs <;> omega

/-- 1 列基底の塔の行 2（何をしても同じ）。 -/
theorem entry2_mTower_singleton {V : TrioSeq} {d0 d1 m s : ℕ} (hV : V.length = 1) (hs : s < m) :
    entry (mTower V d0 d1 m) 2 s = entry V 2 0 := by
  have h : s = s * V.length + 0 := by rw [hV]; omega
  rw [h, mTower_entry hs (by omega), entry2_Lift1, entry2_shiftr01]

/-- ★★★★★★★★★★ **(W63) の芯（行 1）**: **1 列基底 ∧ `d1 = 0` なら、行 1 の親は必ず接頭辞の中**。
⟹ ★ ⟹ **良い枝は起きません** ⟹ ⟹ ★★ **`|A|` が真に減ります**。 -/
theorem nextrel1_src_lt_prefix_of_singleton {A V : TrioSeq} {d0 m c t : ℕ}
    (hV : V.length = 1) (ht : t < m)
    (h : nextrel1 (A ++ mTower V d0 0 m) c (A.length + t)) : c < A.length := by
  have hlen : (mTower V d0 0 m).length = m * V.length := mTower_length V d0 0 m
  have hTlen : (A ++ mTower V d0 0 m).length = A.length + m := by
    rw [List.length_append, hlen, hV]; omega
  have hlt := h.2.2.2.1
  have hclt : c < (A ++ mTower V d0 0 m).length := h.1
  by_contra hc
  push Not at hc
  obtain ⟨s, rfl⟩ : ∃ s, c = A.length + s := ⟨c - A.length, by omega⟩
  rw [entry_append_right, entry_append_right,
    entry1_mTower_singleton hV (show s < m by omega),
    entry1_mTower_singleton hV ht] at hlt
  omega

/-- ★★★★★★★★★★ **(W63) の芯（行 2）**: 行 2 は塔で一切動かないので、同じ結論。 -/
theorem nextrel2_src_lt_prefix_of_singleton {A V : TrioSeq} {d0 d1 m c t : ℕ}
    (hV : V.length = 1) (ht : t < m)
    (h : nextrel2 (A ++ mTower V d0 d1 m) c (A.length + t)) : c < A.length := by
  have hlen : (mTower V d0 d1 m).length = m * V.length := mTower_length V d0 d1 m
  have hTlen : (A ++ mTower V d0 d1 m).length = A.length + m := by
    rw [List.length_append, hlen, hV]; omega
  have hlt := h.2.2.2.1
  have hclt : c < (A ++ mTower V d0 d1 m).length := h.1
  by_contra hc
  push Not at hc
  obtain ⟨s, rfl⟩ : ∃ s, c = A.length + s := ⟨c - A.length, by omega⟩
  rw [entry_append_right, entry_append_right,
    entry2_mTower_singleton hV (show s < m by omega),
    entry2_mTower_singleton hV ht] at hlt
  omega

/-- ★★★★★ ⟹ **`srow ≥ 1` なら、1 列基底の塔では常に残差**（`d1 = 0`）。 -/
theorem nextR_src_lt_prefix_of_singleton {A V : TrioSeq} {d0 m c t i : ℕ}
    (hV : V.length = 1) (ht : t < m) (hi : 0 < i)
    (h : nextR (A ++ mTower V d0 0 m) i c (A.length + t)) : c < A.length := by
  unfold nextR at h
  rw [if_neg (by omega)] at h
  split_ifs at h with h1
  · exact nextrel1_src_lt_prefix_of_singleton hV ht h
  · exact nextrel2_src_lt_prefix_of_singleton hV ht h


/-! ## 110. ★★★★★★★★★★ (W64): **`LiftTie` の「タイ」は、必ず錐の外です**

`LiftTie`（`L53Subst:2337`）:
`∀ m d v z R, argOK R → (∃ p ∈ R, p.2.1 = v) → ((0,v,z) :: R) ∈ W m →`
`Lift1 ((0,v,z) :: R) d ∈ W (m + 2*d)`

⟹ ★★★★★ **`argOK R` は私の (C2) で `hr0 ((0,v,z) :: R)` そのもの**でした。
⟹ ★★★★★★★★ そして **「タイ」（行 1 が根と等しい列）は、必ず錐の外**です（2 行）。
⟹ ⟹ ★★★ ですから **`Lift1` はタイの列を持ち上げません** ⟹ ⛔ **根だけが `+d` される**
⟹ ⟹ ⟹ ★★★★★★★★★★ ⟹ **持ち上げ後、根は行 1 で最小でなくなります**。⟹ ★ **それが `LiftTie` の難しさ**です。 -/

/-- ★★★★★★★★ **タイの列は錐の外**（`nextrel1` は行 1 を狭義に増やすので）。 -/
theorem tie_not_in_cone {M : TrioSeq} {j : ℕ} (h : entry M 1 j = entry M 1 0) (hj : 0 < j) :
    ¬ le1 M 0 j := fun hc => absurd (entry1_lt_of_le1_ne hc (by omega)) (by omega)

open Classical in
/-- ★★★★★ ⟹ **`Lift1` はタイの列を持ち上げません**。 -/
theorem entry1_Lift1_of_tie {M : TrioSeq} {d j : ℕ} (hj : j < M.length) (hj0 : 0 < j)
    (h : entry M 1 j = entry M 1 0) : entry (Lift1 M d) 1 j = entry M 1 j := by
  rw [Wset.entry1_Lift1 hj, if_neg (tie_not_in_cone h hj0)]
  omega

/-- ★★★★★★★★★★ ⟹ **`LiftTie` の芯**: **持ち上げ後、タイの列は根より行 1 が真に低い**。
⟹ ★ ⟹ **根が行 1 の最小でなくなる** ⟹ ⟹ ★★ **`mem_Wself_iff` の `lev(根)` の帳簿が効かなくなります**。 -/
theorem tie_below_root_after_lift {M : TrioSeq} {d j : ℕ} (h0 : 0 < M.length)
    (hj : j < M.length) (hj0 : 0 < j) (h : entry M 1 j = entry M 1 0) (hd : 0 < d) :
    entry (Lift1 M d) 1 j < entry (Lift1 M d) 1 0 := by
  rw [entry1_Lift1_of_tie hj hj0 h, entry1_Lift1_root h0]
  omega


/-- ★★★★★★★★★★ **1 列基底の塔では、どの列の `srow` も基底の 1 列の `srow`**（`d1 = 0`）。
⟹ ★ ⟹ **`nextR_src_lt_prefix_of_singleton` の `i` は「`V` の 1 列の `srow`」**であって、
**元の `p` の `srow` ではありません**。⟹ ⟹ ★★ **そこが実測との食い違いの正体**です。 -/
theorem srow_mTower_singleton {A V : TrioSeq} {d0 m s : ℕ} (hV : V.length = 1) (hs : s < m) :
    srow (A ++ mTower V d0 0 m) (A.length + s) = srow V 0 := by
  have hlen : (mTower V d0 0 m).length = m * V.length := mTower_length V d0 0 m
  have h1 : entry (A ++ mTower V d0 0 m) 1 (A.length + s) = entry V 1 0 := by
    rw [entry_append_right, entry1_mTower_singleton hV hs]
  have h2 : entry (A ++ mTower V d0 0 m) 2 (A.length + s) = entry V 2 0 := by
    rw [entry_append_right, entry2_mTower_singleton hV hs]
  unfold srow
  rw [h1, h2]


/-! ## 111. ★★★★★★★★★★ **`LiftTieSelf` は `u` を含みません** —— `Wself` の閉性そのもの

`LiftTieSelf`（`L105Cap:1354`）は段を **`m = 2v+z`** に固定しています。
⟹ ★★★★★ そして **`lev ((0,v,z) :: R) 0 = 2v+z`** ちょうど。
⟹ ⟹ ★★★★★★★★ ですから **`mem_Wself_iff` で `∈ W (2v+z) ⟺ ∈ Wself`**。
⟹ ★ 結論側も **`lev (Lift1 … d) 0 = 2v+z+2d`** ちょうど ⟹ **`∈ W (2v+z+2d) ⟺ ∈ Wself`**。
⟹ ⟹ ⟹ ★★★★★★★★★★ ⟹ **`LiftTieSelf` ＝「`Wself` が `Lift1` で閉じる（タイの場合）」**。 -/

/-- `(0,v,z) :: R` の根の `lev` は `2v + z` ちょうど。 -/
theorem lev_cons_root (v z : ℕ) (R : TrioSeq) :
    lev (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 = 2 * v + z := by
  show 2 * (((((0, v, z) : ℕ × ℕ × ℕ) :: R).getD 0 (0, 0, 0)).2.1)
    + ((((0, v, z) : ℕ × ℕ × ℕ) :: R).getD 0 (0, 0, 0)).2.2 = _
  rfl

open Classical in
/-- 持ち上げ後の根の `lev` は `2v + z + 2d` ちょうど。 -/
theorem lev_Lift1_cons_root (v z d : ℕ) (R : TrioSeq) :
    lev (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d) 0 = 2 * v + z + 2 * d := by
  have h0 : 0 < (((0, v, z) : ℕ × ℕ × ℕ) :: R).length := by simp
  have h1 : entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d) 1 0
      = entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 0 + d := entry1_Lift1_root h0
  have h2 : entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d) 2 0
      = entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2 0 := entry2_Lift1 _ _ _
  have hv : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 0 = v := rfl
  have hz : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2 0 = z := rfl
  unfold lev
  rw [h1, h2, hv, hz]
  omega

/-- ★★★★★★★★ **仮定側の言い換え**: `∈ W (2v+z) ⟺ ∈ Wself`。 -/
theorem mem_W_selfStage_iff_Wself (v z : ℕ) (R : TrioSeq) :
    (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W (2 * v + z)
      ↔ (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ Wself := by
  rw [mem_Wself_iff, lev_cons_root]
  exact ⟨fun h => h.1, fun h => ⟨h, le_refl _⟩⟩

open Classical in
/-- ★★★★★★★★ **結論側の言い換え**: `∈ W (2v+z+2d) ⟺ ∈ Wself`。 -/
theorem mem_W_lift_iff_Wself (v z d : ℕ) (R : TrioSeq) :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d ∈ W (2 * v + z + 2 * d)
      ↔ Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d ∈ Wself := by
  rw [mem_Wself_iff, lev_Lift1_cons_root]
  exact ⟨fun h => h.1, fun h => ⟨h, le_refl _⟩⟩

open Classical in
/-- ★★★★★★★★★★ ⟹ **`LiftTieSelf` は `u` を含みません**:
**「`Wself` がタイのある根の `Lift1` で閉じる」**と同値です。
⟹ ★ ⟹ **段の帳簿がまるごと消えます**（私の (C1) の `mem_Wself_iff` が、ここで効きました）。 -/
theorem liftTieSelf_iff_Wself_closed :
    (∀ (d v z : ℕ) (R : TrioSeq), argOK R → (∃ p ∈ R, p.2.1 = v) →
        (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W (2 * v + z) →
        Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d ∈ W (2 * v + z + 2 * d))
      ↔ (∀ (d v z : ℕ) (R : TrioSeq), argOK R → (∃ p ∈ R, p.2.1 = v) →
        (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ Wself →
        Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d ∈ Wself) := by
  constructor
  · intro h d v z R hR ht hX
    exact (mem_W_lift_iff_Wself v z d R).mp
      (h d v z R hR ht ((mem_W_selfStage_iff_Wself v z R).mpr hX))
  · intro h d v z R hR ht hX
    exact (mem_W_lift_iff_Wself v z d R).mpr
      (h d v z R hR ht ((mem_W_selfStage_iff_Wself v z R).mp hX))


/-! ## 112. ★★★★★★★★★★ (W65): **タイの列の `lev` は根以下 —— ですが再結合で詰まります**

タイの列 `j`（`entry M 1 j = entry M 1 0`）の `lev` は **`2v + entry M 2 j`**。
⟹ ★ **根の `lev` は `2v + z`** ⟹ ⟹ ★★ **行 2 が `z` 以下なら、タイの列の `lev` は根以下**。
⟹ ★★★★★ そして **持ち上げ後は必ず真に小さい**（根だけ `+2d` されるので）。
⟹ ⛔ **ですが「接頭辞と再結合する」ところで `W_add`（`rsum`）に戻ります**。 -/

/-- タイの列の `lev`。 -/
theorem lev_tie_eq {M : TrioSeq} {j : ℕ} (h : entry M 1 j = entry M 1 0) :
    lev M j = 2 * entry M 1 0 + entry M 2 j := by unfold lev; rw [h]

/-- ★★★★★ **行 2 が根以下なら、タイの列の `lev` は根以下**。 -/
theorem lev_tie_le_root {M : TrioSeq} {j : ℕ} (h : entry M 1 j = entry M 1 0)
    (hz : entry M 2 j ≤ entry M 2 0) : lev M j ≤ lev M 0 := by
  rw [lev_tie_eq h]; unfold lev; omega

/-- ★★★★★★★★ ⟹ **タイの列から後ろは、同じ `W u` に入ります**。 -/
theorem tie_drop_mem_W {u : ℕ} {M : TrioSeq} {j : ℕ} (hM : M ∈ W u)
    (h : entry M 1 j = entry M 1 0) (hz : entry M 2 j ≤ entry M 2 0) :
    M.drop j ∈ W u :=
  W_mono (le_trans (lev_tie_le_root h hz) ((mem_Wself_iff u M).mp hM).2)
    (W_drop hM j)

open Classical in
/-- ★★★★★★★★★★ **持ち上げ後、タイの列の `lev` は根より真に小さい**（`0 < d`）。
⟹ ★ ⟹ **帳簿を付け替える余地はあります**。 -/
theorem lev_tie_lt_root_after_lift {M : TrioSeq} {d j : ℕ} (h0 : 0 < M.length)
    (hj : j < M.length) (hj0 : 0 < j) (h : entry M 1 j = entry M 1 0)
    (hz : entry M 2 j ≤ 1) (hd : 0 < d) :
    lev (Lift1 M d) j < lev (Lift1 M d) 0 := by
  have h1 : entry (Lift1 M d) 1 j = entry M 1 j := entry1_Lift1_of_tie hj hj0 h
  have h1r : entry (Lift1 M d) 1 0 = entry M 1 0 + d := entry1_Lift1_root h0
  have h2 : entry (Lift1 M d) 2 j = entry M 2 j := entry2_Lift1 _ _ _
  have h2r : entry (Lift1 M d) 2 0 = entry M 2 0 := entry2_Lift1 _ _ _
  unfold lev
  rw [h1, h1r, h2, h2r, h]
  omega

/-- ★★★★★★★★ ⟹ **持ち上げ後も、タイの列から後ろは元の段に収まります**。
⟹ ⛔ **詰まるのはここから先**（接頭辞との再結合に `W_add`／`rsum` が要ります）。 -/
theorem tie_drop_mem_W_after_lift {u : ℕ} {M : TrioSeq} {d j : ℕ}
    (hL : Lift1 M d ∈ W u) (h0 : 0 < M.length) (hj : j < M.length) (hj0 : 0 < j)
    (h : entry M 1 j = entry M 1 0) (hz : entry M 2 j ≤ 1) (hd : 0 < d) :
    (Lift1 M d).drop j ∈ W u :=
  W_mono (le_of_lt (lt_of_lt_of_le (lev_tie_lt_root_after_lift h0 hj hj0 h hz hd)
    ((mem_Wself_iff u (Lift1 M d)).mp hL).2)) (W_drop hL j)


/-! ## 113. ★★★★★★★★ **`d1 = 0` ⟺ `srow ≤ 1`** —— 私の `e = 0` の仮定の正体

L3 の §295（`entry1_lt_of_nextR_two`）は、私が (W44) で書いた
`entry1_parent_lt_of_srow2` と**同じ文**です。⟹ ★ それを使うと `wd1` の値が決まります。 -/

/-- ★★★★★★★★ **`wd1 = 0` ⟺ `srow ≤ 1`**（`wd1` を展開した形）。
⟹ ★ ⟹ **私の `nextrel1_src_lt_prefix_of_singleton` の `d1 = 0` は、実質「`srow ≤ 1`」**でした。 -/
theorem d1_zero_iff_srow_le_one {T : TrioSeq} {par s : ℕ}
    (hs : srow T (T.length - 1) = s) (hpar : nextR T s par (T.length - 1)) :
    (if 1 < s then entry T 1 (T.length - 1) - entry T 1 par else 0) = 0 ↔ s ≤ 1 := by
  have hle : s ≤ 2 := by rw [← hs]; exact srow_le_two T _
  constructor
  · intro h
    by_contra hc
    have hs2 : s = 2 := by omega
    subst hs2
    rw [if_pos (by omega)] at h
    have := entry1_parent_lt_of_srow2 hpar
    omega
  · intro h; rw [if_neg (by omega)]


/-! ## 114. ⚠⚠ **自己訂正 16 本目: (W64) の「難しさの説明」は誤りでした**

**`Wset.nextrel1_Lift1`（`Wset:1167`）は無条件の iff**:
`nextrel1 (Lift1 X d) a b ↔ nextrel1 X a b`。
**`Wset.hasParent_Lift1`（`Wset:1259`）も無条件の iff**。
⟹ ⛔ ですから **`Lift1` は親の構造を一切変えません**。
⟹ ⚠ 私の (W64)「持ち上げ後、根が行 1 の最小でなくなる ⟹ 帳簿が効かなくなる」は、
**値については真ですが、`nextrel1` には効きません**。
⟹ ★ 理由: **`nextrel1` の辺では錐の所属が連動する**（下記）。 -/

/-- ★★★★★ **`nextrel1` の辺では、始点が錐の中なら終点も錐の中**。
⟹ ★ ⟹ **両端が同じだけ持ち上がる** ⟹ ⟹ ★★ **`nextrel1_Lift1` が無条件で成り立つ理由**です。 -/
theorem cone_mono_along_nextrel1 {X : TrioSeq} {a b : ℕ} (h : nextrel1 X a b)
    (ha : le1 X 0 a) : le1 X 0 b := ⟨ha.1, h.2.1, ha.2.2.tail h⟩

/-- ★★★★★★★★ **行 0 は `Lift1` で動きません** ⟹ **`wd0` は不変**。 -/
theorem wd0_Lift1_invariant {X : TrioSeq} {d : ℕ} (last par : ℕ) :
    entry (Lift1 X d) 0 last - entry (Lift1 X d) 0 par
      = entry X 0 last - entry X 0 par := by
  rw [entry0_Lift1, entry0_Lift1]

/-- ★★★★★★★★★★ ⟹ **`Lift1` は `nextrel{0,1}` も `hasParent` も変えません**（既存の 2 本のまとめ）。
⟹ ★ ですから **`lift_oper_of_noParent`（`Wtower2:525`）の「親なし」の仮定は、
落とせる見込みがあります**。⟹ ⚠ **これは見立てです**。 -/
theorem lift_preserves_parents {X : TrioSeq} {d i b : ℕ} :
    (hasParent (Lift1 X d) i b ↔ hasParent X i b)
      ∧ (∀ a, nextrel1 (Lift1 X d) a b ↔ nextrel1 X a b) :=
  ⟨Wset.hasParent_Lift1, fun _ => Wset.nextrel1_Lift1⟩


/-! ## 115. ★★★★★★★★★★ (W68): **`MTowerClosedS` の残差は `srow ≥ 1` だけ**

`MTowerClosedS`（`L105Cap:5618`）の仮定は **`hr0 Q`**、
`mTower_mem_of_mTowerStep`（`:5449`）の仮定は **`L53.HasParentInBlock Q`**
＝ **「`Q` の末尾列が `Q` の中で親を持つ」**。
⟹ ★★★★★★★★ **`srow = 0` なら、`hr0` だけでそれが出ます**（私の `hasParent0_of_hr0`）。
⟹ ⟹ ★★★ ⟹ **残差は `srow ≥ 1` の孤児だけ**に絞れます。 -/

/-- ★★★★★★★★★★ **`hr0 Q` ∧ `|Q| ≥ 2` ∧ `srow(末尾) = 0` ⟹ 末尾列は段内に親を持つ**。 -/
theorem hasParentInBlock_of_srow0 {Q : TrioSeq}
    (hr0 : ∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j)
    (hQ2 : 2 ≤ Q.length) (hs : srow Q (Q.length - 1) = 0) :
    L53.HasParentInBlock Q := by
  unfold L53.HasParentInBlock
  rw [hs]
  exact hasParent0_of_hr0 (fun l hl0 hl => hr0 l (by omega) hl) (by omega) (by omega)

/-- ★★★★★★★★★★ ⟹ **残差（段内で孤児）は `srow ≥ 1` のときだけ起きます**。 -/
theorem srow_pos_of_not_hasParentInBlock {Q : TrioSeq}
    (hr0 : ∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j)
    (hQ2 : 2 ≤ Q.length) (h : ¬ L53.HasParentInBlock Q) :
    0 < srow Q (Q.length - 1) := by
  by_contra hc
  push Not at hc
  exact h (hasParentInBlock_of_srow0 hr0 hQ2 (by omega))

/-- ★★★★★ ⟹ **`|Q| ≤ 1` なら残差は起きません**（末尾 ＝ 根）。
⟹ ★ ですから **残差は `|Q| ≥ 2` ∧ `srow ≥ 1` ∧ 段内で孤児**の 3 条件です。 -/
theorem residual_needs_len_two {Q : TrioSeq} (hQ1 : Q.length = 1) :
    L53.HasParentInBlock Q ∨ Q.length ≤ 1 := Or.inr (by omega)


/-! ## 116. ★★★★★★★★★★ (W69): **`wd1` も `Lift1` 不変です** —— 錐は `nextrel1` の道に沿う

`nextrel2 X par last` は **`le1 X par last`** を含みます。
⟹ ★★★★★ そして **`nextrel1` の始点は一意**（`Invariant.nextrel1_unique`）なので、
**`last` から後ろへの `nextrel1` の道は 1 本**です。
⟹ ⟹ ★★★★★★★★ ですから **`0` も `par` も同じ道の上** ⟹ **`le1 X 0 last ⟹ le1 X 0 par`**。
⟹ ⟹ ⟹ ★★★★★★★★★★ ⟹ **両端が同じだけ持ち上がる** ⟹ **`wd1` は不変**。 -/

/-- ★★★★★ **行 1 の祖先の分解**（`nextrel1` の始点の一意性から）。 -/
theorem rtg1_ancestor_split {M : TrioSeq} {c t y : ℕ} (h : nextrel1 M c t)
    (hy : Relation.ReflTransGen (nextrel1 M) y t) :
    y = t ∨ Relation.ReflTransGen (nextrel1 M) y c := by
  rcases Relation.ReflTransGen.cases_tail hy with h1 | ⟨c', hc1, hc2⟩
  · exact Or.inl h1.symm
  · exact Or.inr (by rw [← nextrel1_unique hc2 h]; exact hc1)

/-- `nextrel1` の鎖は添字を増やします。 -/
theorem rtg1_le {M : TrioSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel1 M) a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl a
  | @tail c d _ hcd ih => exact le_trans ih (le_of_lt hcd.2.2.1)

/-- ★★★★★★★★ **`le1` の道の上では、錐の所属が後ろへ伝わります**。 -/
theorem cone_of_le1_to_cone {M : TrioSeq} {a b : ℕ} (hab : le1 M a b) (hb : le1 M 0 b)
    (ha0 : 0 < a) : le1 M 0 a := by
  obtain ⟨ha1, hb1, hrt⟩ := hab
  have key : ∀ b', Relation.ReflTransGen (nextrel1 M) a b' → le1 M 0 b' → le1 M 0 a := by
    intro b' h
    induction h with
    | refl => exact fun h0 => h0
    | @tail c b'' hac hcb ih =>
        intro hb''
        refine ih ?_
        have hale : a ≤ c := rtg1_le hac
        rcases rtg1_ancestor_split hcb hb''.2.2 with h1 | h1
        · exact absurd h1 (by have := hcb.2.2.1; omega)
        · exact ⟨hb''.1, hcb.1, h1⟩
  exact key b hrt hb

open Classical in
/-- ★★★★★★★★★★ **(W69) の穴が埋まりました**: `nextrel2 X par last` なら
**`le1 X 0 par ↔ le1 X 0 last`** ⟹ **`wd1` は `Lift1` 不変**。 -/
theorem wd1_Lift1_invariant {X : TrioSeq} {d par last : ℕ} (hpar0 : 0 < par)
    (h : nextrel2 X par last) :
    entry (Lift1 X d) 1 last - entry (Lift1 X d) 1 par
      = entry X 1 last - entry X 1 par := by
  have hle1 : le1 X par last := h.2.2.2.2.1
  have hplen : par < X.length := h.1
  have hllen : last < X.length := h.2.1
  have hiff : le1 X 0 par ↔ le1 X 0 last := by
    constructor
    · intro hp; exact ⟨hp.1, hllen, hp.2.2.trans hle1.2.2⟩
    · intro hl; exact cone_of_le1_to_cone hle1 hl hpar0
  rw [Wset.entry1_Lift1 hllen, Wset.entry1_Lift1 hplen]
  by_cases hc : le1 X 0 par
  · rw [if_pos hc, if_pos (hiff.mp hc)]
    have := h.2.2.2.2.1
    have hlt : entry X 1 par < entry X 1 last := entry1_lt_of_le1_ne hle1 (by have := h.2.2.1; omega)
    omega
  · rw [if_neg hc, if_neg (fun hx => hc (hiff.mpr hx))]
    omega


/-! ## 117. ★★★★★★★★★★ **残差は `domT` そのものです** —— 節 3 が使えます

`domT R m := lev R (|R|−1) = m+1 ∧ ¬ hasParent R (srow R (|R|−1)) (|R|−1)`（`Wset:61`）。
`MTowerClosedS` の残差 ＝ **`¬ L53.HasParentInBlock Q`** ＝ **`domT` の後半そのもの**。
⟹ ★★★★★ そして前半（`lev > 0`）は、私の (W68)（残差 ⟹ `srow ≥ 1`）から出ます。
⟹ ⟹ ★★★★★★★★★★ ⟹ **残差の場合、`domT Q (lev Q (|Q|−1) − 1)` が成り立ちます**。
⟹ ⟹ ⟹ ★ ですから **`parent_cons_eq_zero`（`Wset:2762`、`domT` を要求）は、残差でこそ使えます**。 -/

/-- ★★★ **`srow ≥ 1` なら `lev > 0`**。 -/
theorem lev_pos_of_srow_pos {M : TrioSeq} {j : ℕ} (h : 0 < srow M j) : 0 < lev M j := by
  unfold srow at h
  unfold lev
  split_ifs at h <;> omega

/-- ★★★★★★★★★★ **残差の場合、`Q` は `domT` を満たします**。
⟹ ★ ⟹ **`Aop` の節 3 と、`parent_cons_eq_zero` が使えます**。 -/
theorem domT_of_residual {Q : TrioSeq}
    (hr0 : ∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j)
    (hQ2 : 2 ≤ Q.length) (horph : ¬ L53.HasParentInBlock Q) :
    domT Q (lev Q (Q.length - 1) - 1) := by
  have hs : 0 < srow Q (Q.length - 1) := srow_pos_of_not_hasParentInBlock hr0 hQ2 horph
  have hlev : 0 < lev Q (Q.length - 1) := lev_pos_of_srow_pos hs
  exact ⟨by omega, horph⟩

/-- ★★★★★★★★★★ ⟹ **残差では、`(0,v,z) :: Q` の末尾の親は必ず根**。
⟹ ★ **`parent_cons_eq_zero` の `domT` が、残差から無料で出ます**。 -/
theorem parent_cons_eq_zero_of_residual {v z : ℕ} {Q : TrioSeq}
    (hr0 : ∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j)
    (hQ2 : 2 ≤ Q.length) (horph : ¬ L53.HasParentInBlock Q)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: Q) (srow Q (Q.length - 1)) Q.length) :
    parent (((0, v, z) : ℕ × ℕ × ℕ) :: Q) (srow Q (Q.length - 1)) Q.length = 0 :=
  parent_cons_eq_zero (by intro hc; rw [hc] at hQ2; simp at hQ2)
    (domT_of_residual hr0 hQ2 horph) hpM


/-! ## 118. ★★★★★★★★★★ (W70): **`oper` の入力は全部 `Lift1` 不変** —— 残るのは出力側の錐 1 点

`oper M n`（`Trio.lean:98`）が使う量:
**`|M|` ／ 末尾の行 0・1・2 ／ `srow` ／ `hasParent` ／ `parent` ／ `d0` ／ `d1` ／
`M.take j0` ／ 窓の各列の行 0・1・2 ／ `le0 M j0 j` ／ `le1 M j0 j`**。
⟹ ★★★★★ **このうち `Lift1` で動くのは「行 1 の値」だけ**で、それも**錐の中だけ `+d`**。
⟹ ⟹ ★★★★★★★★★★ ⟹ **残る 1 点は「`X⟦n⟧` の錐が `X` の錐に対応するか」**です。 -/

/-- ★★★★★★★★★★ **`oper` の入力の不変性（まとめ）**。既存 5 本 ＋ 私の (W69) を 1 本に。 -/
theorem oper_inputs_Lift1_invariant {X : TrioSeq} {d : ℕ} :
    (Lift1 X d).length = X.length
      ∧ (∀ j : ℕ, entry (Lift1 X d) 0 j = entry X 0 j)
      ∧ (∀ j : ℕ, entry (Lift1 X d) 2 j = entry X 2 j)
      ∧ (∀ j : ℕ, j ≠ 0 → srow (Lift1 X d) j = srow X j)
      ∧ (∀ i b : ℕ, hasParent (Lift1 X d) i b ↔ hasParent X i b)
      ∧ (∀ i b : ℕ, parent (Lift1 X d) i b = parent X i b)
      ∧ (∀ a b : ℕ, le0 (Lift1 X d) a b ↔ le0 X a b)
      ∧ (∀ a b : ℕ, le1 (Lift1 X d) a b ↔ le1 X a b) :=
  by
  refine ⟨Lift1_length X d, fun j => ?_, fun j => ?_, fun j hj => Wset.srow_Lift1 hj,
    fun _ _ => Wset.hasParent_Lift1, fun _ _ => Wset.parent_Lift1,
    fun _ _ => Wset.le0_Lift1, fun _ _ => Wset.le1_Lift1⟩
  · rw [entry0_Lift1]
  · rw [entry2_Lift1]


/-! ## 119. ★★★★★★★★★★ (W71): **向きは「≤」です** —— 私の `amin` から出るのは団長の読みどおり

`hr0 Q` ⟹ **根は全列の行 0 の祖先**（`le0_root_of_shallow`）⟹ ★ **`amin Q j ≤ entry Q 1 0`**。
そして **`srow = 1` の孤児 ⟹ `amin Q j = entry Q 1 j`**（`orphan_row1_iff_amin_eq`）。
⟹ ⟹ ★★★★★★★★★★ ⟹ **`entry Q 1 (末尾) ≤ entry Q 1 0`** —— **「≥」ではなく「≤」**です。
⟹ ⛔ ですから **(W71) の「末尾の行 1 ≥ 根の行 1」は、`hr0` からは出ません**。
⟹ ★ R2 の 100% は **「＝」** なので、**両側を合わせると等号**になります。 -/

/-- ★★★★★★★★★★ **(W71) の証明できる向き**: `hr0 Q` ∧ `srow(末尾) = 1` ∧ 残差
⟹ **末尾の行 1 は根の行 1 以下**。 -/
theorem orphan_last_row1_le_root {Q : TrioSeq}
    (hr0 : ∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j)
    (hQ2 : 2 ≤ Q.length) (hs : srow Q (Q.length - 1) = 1)
    (horph : ¬ L53.HasParentInBlock Q) :
    entry Q 1 (Q.length - 1) ≤ entry Q 1 0 := by
  have hlast : Q.length - 1 < Q.length := by omega
  have hle0 : le0 Q 0 (Q.length - 1) :=
    le0_root_of_shallow (by omega) (fun x hx hxl => hr0 x (by omega) hxl)
      (Q.length - 1) (by omega) hlast
  have hamin : amin Q (Q.length - 1) ≤ entry Q 1 0 := amin_le hle0.2.2
  have horph1 : ¬ hasParent Q 1 (Q.length - 1) := by
    unfold L53.HasParentInBlock at horph; rwa [hs] at horph
  have heq : amin Q (Q.length - 1) = entry Q 1 (Q.length - 1) :=
    (orphan_row1_iff_amin_eq hlast).mp horph1
  omega

/-- ★★★★★ ⟹ **R2 の 100%（「＝」）と合わせると、残差では等号**になります。
⟹ ★ **逆向き（`≥`）は `hr0` からは出ません** ⟹ ⚠ **`W` の不変量の可能性**（未証明）。 -/
theorem orphan_last_row1_eq_root_of_ge {Q : TrioSeq}
    (hr0 : ∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j)
    (hQ2 : 2 ≤ Q.length) (hs : srow Q (Q.length - 1) = 1)
    (horph : ¬ L53.HasParentInBlock Q)
    (hge : entry Q 1 0 ≤ entry Q 1 (Q.length - 1)) :
    entry Q 1 (Q.length - 1) = entry Q 1 0 :=
  le_antisymm (orphan_last_row1_le_root hr0 hQ2 hs horph) hge

/-- ★★★★★★★★ ⟹ **そして「末尾は根とタイ」＝「末尾は錐の外」**（私の (W64)）。
⟹ ★ ⟹ **`Lift1` は末尾を持ち上げません** ⟹ ⟹ ★★ **`LiftTie` の核と同じ場所**です。 -/
theorem orphan_last_not_in_cone {Q : TrioSeq}
    (hQ2 : 2 ≤ Q.length) (heq : entry Q 1 (Q.length - 1) = entry Q 1 0) :
    ¬ le1 Q 0 (Q.length - 1) := tie_not_in_cone heq (by omega)


/-! ## 120. ⛔⛔ **(W71) の「≥」は偽です** —— 反例（緑）

`Q = [(0,2,0), (1,1,0)]`。⟹ ★ 行 2 ≡ 0 なので **`zeroRow2_mem_Wself` で `Q ∈ W 4`**（`lev Q 0 = 4`）。
⟹ ★ **`hr0 Q`**（`0 < 1`）／ **`srow(末尾) = 1`**（行 1 = 1 > 0、行 2 = 0）
⟹ ★ **末尾は行 1 の孤児**（候補は根だけで、行 1 が `2` なので `< 1` を満たさない）＝ **残差**
⟹ ⟹ ⛔ **`entry Q 1 (末尾) = 1 < 2 = entry Q 1 0`** ⟹ **「末尾の行 1 ≥ 根の行 1」は偽**。

⟹ ★★★ **私の `orphan_last_row1_le_root`（`≤`）とは整合**します（`1 ≤ 2`）。
⟹ ⟹ ★ ですから **R2 の「100% が等号」は母集団の産物**です。 -/

/-- (W71) の反例。 -/
def w71Ctr : TrioSeq := [(0, 2, 0), (1, 1, 0)]

theorem w71Ctr_zeroRow2 : ∀ p ∈ w71Ctr, p.2.2 = 0 := by decide

theorem w71Ctr_lev : lev w71Ctr 0 = 4 := by decide

theorem w71Ctr_mem : w71Ctr ∈ W 4 :=
  (mem_Wself_iff 4 w71Ctr).mpr ⟨zeroRow2_mem_Wself w71Ctr_zeroRow2, by rw [w71Ctr_lev]⟩

theorem w71Ctr_hr0 : ∀ j, 1 ≤ j → j < w71Ctr.length → entry w71Ctr 0 0 < entry w71Ctr 0 j := by
  decide

theorem w71Ctr_srow : srow w71Ctr (w71Ctr.length - 1) = 1 := by decide

theorem w71Ctr_row1_lt : entry w71Ctr 1 (w71Ctr.length - 1) < entry w71Ctr 1 0 := by decide

/-- ⛔⛔ **(W71) の「≥」は偽**（`hr0` ∧ `srow(末尾) = 1` ∧ `Q ∈ W u` でも破れます）。 -/
theorem w71_ge_false :
    ¬ (∀ (u : ℕ) (Q : TrioSeq), Q ∈ W u →
        (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
        srow Q (Q.length - 1) = 1 →
        entry Q 1 0 ≤ entry Q 1 (Q.length - 1)) := by
  intro h
  exact absurd (h 4 w71Ctr w71Ctr_mem w71Ctr_hr0 w71Ctr_srow) (by
    have := w71Ctr_row1_lt; omega)


/-- ⛔⛔ **しかもこれは残差です**（末尾は行 1 の孤児）。
⟹ ★ ですから **R2 の「残差では 100% が等号」も、この例で破れます**。 -/
theorem w71Ctr_orphan : ¬ L53.HasParentInBlock w71Ctr := by
  unfold L53.HasParentInBlock
  rw [w71Ctr_srow]
  have hlen : w71Ctr.length - 1 = 1 := by decide
  rw [hlen]
  rintro ⟨y, hy, -⟩
  have hy' : nextrel1 w71Ctr y 1 := by simpa [nextR] using hy
  have h1 : y < 1 := hy'.2.2.1
  have hy0 : y = 0 := by omega
  subst hy0
  have h2 : entry w71Ctr 1 0 < entry w71Ctr 1 1 := hy'.2.2.2.1
  revert h2
  decide

/-- ⛔⛔ ⟹ **「残差では末尾の行 1 ＝ 根の行 1」も偽**。 -/
theorem w71_eq_false :
    ¬ (∀ (u : ℕ) (Q : TrioSeq), Q ∈ W u →
        (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
        srow Q (Q.length - 1) = 1 → ¬ L53.HasParentInBlock Q →
        entry Q 1 (Q.length - 1) = entry Q 1 0) := by
  intro h
  have := h 4 w71Ctr w71Ctr_mem w71Ctr_hr0 w71Ctr_srow w71Ctr_orphan
  have hlt := w71Ctr_row1_lt
  omega


/-! ## 121. ★★★★★★★★★★ **残差の機構 ＝ `blocker_of_large_k`** —— 1 本に繋ぎました

(W71) の「≤」だけで **「末尾は錐の外」**が出ます（等号は要りません）。
⟹ ★ ⟹ **`Lift1` も塔の `+e*k` も末尾を動かさない**
⟹ ⟹ ★★ 一方 **錐の中の列は `+e*k` で上がる**
⟹ ⟹ ⟹ ★★★★★★★★★★ ⟹ **`blocker_of_large_k`（私の §305）が、そのまま残差の機構**です。 -/

/-- ★★★★★ **行 1 が根以下なら錐の外**（等号でなくてよい、(W64) の一般形）。 -/
theorem not_in_cone_of_row1_le_root {Q : TrioSeq} {j : ℕ} (hj0 : 0 < j)
    (h : entry Q 1 j ≤ entry Q 1 0) : ¬ le1 Q 0 j :=
  fun hc => absurd (entry1_lt_of_le1_ne hc (by omega)) (by omega)

/-- ★★★★★★★★ ⟹ **残差の末尾は錐の外**（`srow = 1` の場合、等号を経由しません）。 -/
theorem orphan_last_not_in_cone_le {Q : TrioSeq}
    (hr0 : ∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j)
    (hQ2 : 2 ≤ Q.length) (hs : srow Q (Q.length - 1) = 1)
    (horph : ¬ L53.HasParentInBlock Q) :
    ¬ le1 Q 0 (Q.length - 1) :=
  not_in_cone_of_row1_le_root (by omega) (orphan_last_row1_le_root hr0 hQ2 hs horph)

/-- ★★★★★★★★★★ **残差の機構（1 本）**: 残差の末尾は、
**錐の中のどの列より行 1 が低くなる**（`k` が十分大きいブロックで）。
⟹ ★ ＝ **私の `blocker_of_large_k` を、残差の言葉で書き直したもの**。 -/
theorem blocker_of_residual_last (Q : TrioSeq) {d e n k k' p : ℕ}
    (hr0 : ∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j)
    (hQ2 : 2 ≤ Q.length) (hs : srow Q (Q.length - 1) = 1)
    (horph : ¬ L53.HasParentInBlock Q)
    (hk : k < n) (hk' : k' < n) (hp : p < Q.length) (hinp : le1 Q 0 p)
    (he : 0 < e) (hbig : entry Q 1 (Q.length - 1) ≤ k) :
    entry (mTower Q d e n) 1 (k' * Q.length + (Q.length - 1))
      ≤ entry (mTower Q d e n) 1 (k * Q.length + p) :=
  blocker_of_large_k Q hk hk' hp (by omega) hinp
    (orphan_last_not_in_cone_le hr0 hQ2 hs horph) he hbig


/-! ## 122. ★★★★★★★★ (W70 続き): **`n = 1` の可換性は無料です**

`oper M 1 = M.dropLast`（親があるとき、`k = 0` なので持ち上げ 0）。
⟹ ★ ですから **`n = 1` の可換性 ＝ `Lift1 (X.dropLast) d = (Lift1 X d).dropLast`**。
⟹ ⟹ ★★★★★ そして **`Wset.le1_take` が「錐は `take` で変わらない」を無料でくれます**。 -/

open Classical in
/-- ★★★★★★★★ **`Lift1` は `dropLast` と可換**（＝ `n = 1` の可換性）。
⟹ ★ 鍵は **`Wset.le1_take`**（錐は `take` で変わらない、前提は `b < l` だけ）。 -/
theorem Lift1_dropLast (X : TrioSeq) (d : ℕ) :
    Lift1 X.dropLast d = (Lift1 X d).dropLast := by
  have hlen : X.dropLast.length = X.length - 1 := by simp
  have hL : (Lift1 X d).length = X.length := Lift1_length X d
  apply List.ext_getElem
  · rw [Lift1_length, hlen, List.length_dropLast, hL]
  · intro i h1 h2
    have hi : i < X.length - 1 := by
      rw [Lift1_length, hlen] at h1; exact h1
    have hiX : i < X.length := by omega
    have e0 : ∀ r, entry X.dropLast r i = entry X r i := by
      intro r
      rw [List.dropLast_eq_take]
      exact Wset.entry_take (by omega)
    have hc : le1 X.dropLast 0 i ↔ le1 X 0 i := by
      rw [List.dropLast_eq_take]
      exact Wset.le1_take (by omega) (by omega)
    have hlhs : (Lift1 X.dropLast d)[i]
        = (entry X.dropLast 0 i, entry X.dropLast 1 i
            + (if le1 X.dropLast 0 i then d else 0), entry X.dropLast 2 i) := by
      have h := Lift1_getD (X := X.dropLast) (d := d) (i := i) (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at h
      exact h
    have hrhs : (Lift1 X d).dropLast[i]
        = (entry X 0 i, entry X 1 i + (if le1 X 0 i then d else 0), entry X 2 i) := by
      rw [List.getElem_dropLast]
      have h := Lift1_getD (X := X) (d := d) (i := i) hiX
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show i < (Lift1 X d).length by rw [hL]; omega)] at h
      exact h
    rw [hlhs, hrhs, e0 0, e0 1, e0 2]
    by_cases hcc : le1 X 0 i
    · rw [if_pos (hc.mpr hcc), if_pos hcc]
    · rw [if_neg (fun hx => hcc (hc.mp hx)), if_neg hcc]


/-! ## 123. ⛔ (W74): **私の予測は外れます** —— 塔でも行 2 の親は得られません

L3 の `hasParent2_iff_zero_in_cone`（`z ≤ 1`、必要十分）:
**`hasParent M 2 t ↔ ∃ c < t, entry M 2 c = 0 ∧ le1 M c t`**。
⟹ ★ ですから **末尾の `le1` 祖先に `z = 0` の列が現れるか**が全てです。
⟹ ⛔ ところが **私の `prefix_mTower_nextrel1_src_ge`（(W56)）**が言うのは
**「証人があれば行 1 の親は同じ写しの中」**——⟹ ★★ **`le1` の鎖はブロックを出ません**。
⟹ ⟹ ⛔ **ですから塔でも `z = 0` の列に届かず、孤児のまま**です。 -/

/-- ★★★★★ **残差（`srow = 2`）の二分法**: **根が `z = 1`** か、**末尾が根の錐の外**か。
⟹ ★ L3 の iff を仮定として受け取り、`c = 0` を入れるだけ（2 行）。 -/
theorem residual_row2_dichotomy {Q : TrioSeq} (hQ2 : 2 ≤ Q.length)
    (hiff : ∀ t, hasParent Q 2 t ↔ ∃ c, c < t ∧ entry Q 2 c = 0 ∧ le1 Q c t)
    (hz1 : ∀ i, entry Q 2 i ≤ 1)
    (horph : ¬ hasParent Q 2 (Q.length - 1)) :
    entry Q 2 0 = 1 ∨ ¬ le1 Q 0 (Q.length - 1) := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  exact horph ((hiff _).mpr ⟨0, by omega, by have := hz1 0; omega, h2⟩)

/-- ⚠⚠ **名前に反して、これは「証人 `hy` があるとき」だけの主張です**（(W56) の再掲）。
⛔ **証人が無い列（＝ `Q` の中で行 1 の孤児）については、何も言いません**。
⟹ ★ そこでは鎖がブロックを出られます（`row1_cross_implies_orphan` の対偶）。
⟹ ⚠ **私は (W74) でこの仮定を落として誤った結論を出しました（自己訂正 18）。**
⟹ ★★★ **本当の理由は (W61)**: **`le1 ⊆ le0` で、`le0` はブロック根で塞がれます**（L3 の指摘）。 -/
theorem row2_parent_stays_in_block {A Q : TrioSeq} {d e n k j y c : ℕ}
    (hk : k < n) (hj : j < Q.length) (hy : nextrel1 Q y j)
    (h : nextrel1 (A ++ mTower Q d e n) c (A.length + (k * Q.length + j))) :
    A.length + (k * Q.length + y) ≤ c :=
  prefix_mTower_nextrel1_src_ge hk hj hy h


/-! ## 124. ★★★★★★★★★★ (W75): **塔の末尾が錐の中なら、親はブロック根以降** —— L3 の理由を型で

L3 の 1 行:「**`le1` は `le0` を含み、`le0` はブロック根で塞がれます**」。
⟹ ★ 行 1 でも同じことが言えます: **ブロック根は `le0` 祖先**（`hr0`）で、
**的が錐の中なら根より行 1 が真に高い** ⟹ ⟹ ★★ **最小性が、根より前の候補を全部落とします**。 -/

/-- ★★★★★ 塔のブロック根は、そのブロックの列の `le0` 祖先（`hr0` から）。 -/
theorem le0_blockRoot_mTower (Q : TrioSeq) {d e n k i : ℕ}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hk : k < n) (hi : i < Q.length) (hi0 : 0 < i) :
    le0 (mTower Q d e n) (k * Q.length) (k * Q.length + i) := by
  have hlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have hkn : (k + 1) * Q.length ≤ n * Q.length := Nat.mul_le_mul_right _ (by omega)
  have hsk : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
  have hQ : le0 Q 0 i :=
    le0_root_of_shallow (by omega) (fun x hx hxl => hr0 x hx hxl) i hi0 hi
  have := rtg0_mTower_intra_block Q (d := d) (e := e) hk (a := 0) (b := i)
    (by omega) hi hQ.2.2
  exact ⟨by omega, by omega, by simpa using this⟩

open Classical in
/-- ★★★★★★★★★★ **(W75) の芯**: `hr0 Q` ∧ **的が `Q` の錐の中** なら、
**塔の行 1 の親はブロック根以降**（＝ **同じブロックの中**）。
⟹ ★ **証人は要りません**（(W56) と違う点）。⟹ ⟹ ★★ **L3 の「`le0` はブロック根で塞がれる」の行 1 版**。 -/
theorem nextrel1_mTower_src_ge_blockRoot (Q : TrioSeq)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    {d e n k i c : ℕ} (hk : k < n) (hi : i < Q.length) (hi0 : 0 < i)
    (hcone : le1 Q 0 i)
    (h : nextrel1 (mTower Q d e n) c (k * Q.length + i)) :
    k * Q.length ≤ c := by
  by_contra hc
  push Not at hc
  have hroot : le1 Q 0 0 := ⟨by omega, by omega, Relation.ReflTransGen.refl⟩
  have hlt : entry Q 1 0 < entry Q 1 i := entry1_lt_of_le1_ne hcone (by omega)
  have hmin := h.2.2.2.2.2 (k * Q.length)
    ⟨by omega, by simpa using le0_blockRoot_mTower Q hr0 hk hi hi0⟩
  rw [entry1_mTower_block_formula Q hk hi,
    show k * Q.length = k * Q.length + 0 from by omega,
    entry1_mTower_block_formula Q hk (by omega), if_pos hcone, if_pos hroot] at hmin
  omega


/-! ## 125. ★★★★★★★★★★ (W75'): **孤児のままなら `oper = dropLast`** —— `n` の帰納の入口

`oper_eq_pred_of_noParent`（`Decrease:37`）＋ `Pred`（`Trio:75`）で、
**「塔の末尾が孤児 ⟹ `oper` は `dropLast`」**が出ます。
⟹ ★★★★★ そして **`dropLast` は `mTower Q d e n ++ (最後のブロックの dropLast)`**
⟹ ⟹ ★★★ **塔の段数が 1 つ減った形**です ⟹ ★ **L3 の `n` の帰納の入口**。 -/

/-- ★★★★★ **末尾の行 0 は正**（`hr0` ∧ `|Q| ≥ 2` ∧ `0 < n`）⟹ **全零テストを外せます**。 -/
theorem entry0_mTower_last_pos {Q : TrioSeq} {d e n : ℕ}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hQ2 : 2 ≤ Q.length) (hn : 0 < n) :
    0 < entry (mTower Q d e n) 0 ((mTower Q d e n).length - 1) := by
  have hlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have hidx : (mTower Q d e n).length - 1 = (n - 1) * Q.length + (Q.length - 1) := by
    have h2 : (n - 1) * Q.length + Q.length = n * Q.length := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp [Nat.succ_mul]
    omega
  rw [hidx, entry0_mTower_block' Q (by omega) (by omega)]
  have := hr0 (Q.length - 1) (by omega) (by omega)
  omega

/-- ★★★★★★★★★★ **(W75') の芯**: **塔の末尾が孤児 ⟹ `oper` は `dropLast`**。 -/
theorem oper_mTower_eq_dropLast {Q : TrioSeq} {d e n m : ℕ}
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hQ2 : 2 ≤ Q.length) (hn : 0 < n)
    (hnp : ¬ hasParent (mTower Q d e n) (srow (mTower Q d e n) ((mTower Q d e n).length - 1))
      ((mTower Q d e n).length - 1)) :
    (mTower Q d e n)⟦m⟧ = (mTower Q d e n).dropLast := by
  have hlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have hnQ : 2 ≤ n * Q.length := by
    have : 1 * Q.length ≤ n * Q.length := Nat.mul_le_mul_right _ (by omega)
    omega
  have hL : (mTower Q d e n).length - 1 ≠ 0 := by omega
  have hz : ¬ (entry (mTower Q d e n) 0 ((mTower Q d e n).length - 1) = 0 ∧
      entry (mTower Q d e n) 1 ((mTower Q d e n).length - 1) = 0 ∧
      entry (mTower Q d e n) 2 ((mTower Q d e n).length - 1) = 0) := by
    intro hc
    have := entry0_mTower_last_pos hr0 hQ2 hn (d := d) (e := e)
    omega
  rw [oper_eq_pred_of_noParent m hL hz hnp]
  unfold Pred
  rw [if_neg (by omega)]

/-- ★★★★★★★★ ⟹ **`dropLast` は「1 段低い塔 ＋ 最後のブロックの `dropLast`」**。
⟹ ★ ⟹ **段数が真に減る形**です。 -/
theorem dropLast_mTower_succ (Q : TrioSeq) (d e n : ℕ) (hQ : 0 < Q.length) :
    (mTower Q d e (n + 1)).dropLast
      = mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).dropLast := by
  have hne : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) ≠ [] := by
    intro hc
    have h : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length = Q.length := by
      rw [Lift1_length, shiftr01_length]
    rw [hc] at h
    simp at h
    omega
  rw [mTower_succ, List.dropLast_append_of_ne_nil hne]


/-! ## 126. ★★★★★★★★★★ (W76): **「錐の外」の越境には、非祖先の低い列が要ります**

`srow = 1` ⟹ `d1 = 0` ⟹ **`e = 0`**（L3 の §295）⟹ ★ **写しの行 1 は全部 `Q` と同じ**。
⟹ ★★★★★ そのとき **越境の始点 `(k', r)` は、`Q` の中で `i` の `le0` 祖先ではあり得ません**:
祖先なら **同じブロックの写し `(k, r)` が最小性で塞ぎます**。
⟹ ⟹ ★★★★★★★★★★ ⟹ **越境には「`i` の祖先でないのに行 1 が低い列」が要ります**。 -/

/-- ★★★★★★★★★★ **(W76)**: `e = 0` の塔で行 1 の越境が起きるなら、
始点は **`entry Q 1 r < entry Q 1 i` かつ `¬ le0 Q r i`** の列（＝ **非祖先で低い列**）。
⟹ ★ ⟹ **`Q` にそういう列が無ければ、越境は起きません**。 -/
theorem cross_needs_nonancestor_low (Q : TrioSeq) {d n k i c : ℕ}
    (hk : k < n) (hi : i < Q.length) (hc : c < k * Q.length)
    (h : nextrel1 (mTower Q d 0 n) c (k * Q.length + i)) :
    ∃ r, r < Q.length ∧ entry Q 1 r < entry Q 1 i ∧ ¬ le0 Q r i := by
  have hQ : 0 < Q.length := by omega
  have hent : ∀ k'' j, k'' < n → j < Q.length →
      entry (mTower Q d 0 n) 1 (k'' * Q.length + j) = entry Q 1 j := by
    intro k'' j hk'' hj
    rw [entry1_mTower_block_formula Q hk'' hj]
    split_ifs <;> omega
  have hk' : c / Q.length < k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm] at hc; exact hc)
  have hr : c % Q.length < Q.length := Nat.mod_lt _ hQ
  have hsplit : c = (c / Q.length) * Q.length + c % Q.length :=
    (Nat.div_add_mod' c Q.length).symm
  have hlt : entry (mTower Q d 0 n) 1 c
      < entry (mTower Q d 0 n) 1 (k * Q.length + i) := h.2.2.2.1
  rw [hsplit, hent _ _ (by omega) hr, hent _ _ hk hi] at hlt
  refine ⟨c % Q.length, hr, hlt, ?_⟩
  intro hanc
  have hrle : c % Q.length ≤ i := rtg0_le hanc.2.2
  have hrlt : c % Q.length < i := by
    rcases Nat.eq_or_lt_of_le hrle with heq | hlt2
    · rw [heq] at hlt; omega
    · exact hlt2
  have hstep : (c / Q.length + 1) * Q.length = (c / Q.length) * Q.length + Q.length :=
    Nat.succ_mul _ _
  have hkq : (c / Q.length + 1) * Q.length ≤ k * Q.length :=
    Nat.mul_le_mul_right _ (by omega)
  have hlen : (mTower Q d 0 n).length = n * Q.length := mTower_length Q d 0 n
  have hkn : (k + 1) * Q.length ≤ n * Q.length := Nat.mul_le_mul_right _ (by omega)
  have hsk : (k + 1) * Q.length = k * Q.length + Q.length := Nat.succ_mul k Q.length
  have hle0 : le0 (mTower Q d 0 n) (k * Q.length + c % Q.length) (k * Q.length + i) :=
    ⟨by omega, by omega, rtg0_mTower_intra_block Q hk hr hi hanc.2.2⟩
  have hmin := h.2.2.2.2.2 (k * Q.length + c % Q.length) ⟨by omega, hle0⟩
  rw [hent _ _ hk hi, hent _ _ hk hr] at hmin
  omega


/-! ## 127. ★★★★★★★★★★ (W77) 第 1 部: **接頭辞の錐は無料で保たれます**

`X⟦n⟧ = X.take j0 ++ (写し)`。⟹ ★ **添字が `j0` 未満の部分**では、
**錐は `X` のものと一致**します。⟹ ⟹ ★★★★★ **`Wset.le1_take` ＋ `List.take_left` の 2 行**。 -/

/-- ★★★★★ **左側の錐は、右に何を足しても変わりません**。 -/
theorem le1_append_left {A B : TrioSeq} {i : ℕ} (hi : i < A.length) :
    le1 (A ++ B) 0 i ↔ le1 A 0 i := by
  have h := Wset.le1_take (X := A ++ B) (l := A.length) (a := 0) (b := i)
    (by rw [List.length_append]; omega) hi
  rw [List.take_left] at h
  exact h.symm

/-- ★★★★★ **行 0 版**。 -/
theorem le0_append_left {A B : TrioSeq} {i : ℕ} (hi : i < A.length) :
    le0 (A ++ B) 0 i ↔ le0 A 0 i := by
  have h := Wset.le0_take (X := A ++ B) (l := A.length) (a := 0) (b := i)
    (by rw [List.length_append]; omega) hi
  rw [List.take_left] at h
  exact h.symm

/-- ★★★★★★★★★★ **(W77) 第 1 部**: `oper` の接頭辞部分では、**錐が `X` と一致**します。
⟹ ★ ⟹ **`Lift1` と `oper` の可換性のうち、接頭辞側は無料**です。 -/
theorem cone_prefix_stable {X : TrioSeq} {j0 : ℕ} (B : TrioSeq) (hj0 : j0 ≤ X.length) {i : ℕ}
    (hi : i < j0) : le1 (X.take j0 ++ B) 0 i ↔ le1 X 0 i := by
  have hlen : (X.take j0).length = j0 := by rw [List.length_take]; omega
  have h1 : le1 (X.take j0 ++ B) 0 i ↔ le1 (X.take j0) 0 i :=
    le1_append_left (by rw [hlen]; exact hi)
  have h2 : le1 (X.take j0) 0 i ↔ le1 X 0 i := Wset.le1_take hj0 hi
  exact h1.trans h2

/-- ★★★★★ **行 0 版**（`oper` の写しの番人 `le0 M j0 j` にも要ります）。 -/
theorem cone0_prefix_stable {X : TrioSeq} {j0 : ℕ} (B : TrioSeq) (hj0 : j0 ≤ X.length) {i : ℕ}
    (hi : i < j0) : le0 (X.take j0 ++ B) 0 i ↔ le0 X 0 i := by
  have hlen : (X.take j0).length = j0 := by rw [List.length_take]; omega
  have h1 : le0 (X.take j0 ++ B) 0 i ↔ le0 (X.take j0) 0 i :=
    le0_append_left (by rw [hlen]; exact hi)
  have h2 : le0 (X.take j0) 0 i ↔ le0 X 0 i := Wset.le0_take hj0 hi
  exact h1.trans h2


/-! ## 128. ★★★★★★★★★★ `LiftOperComm` の易しい分岐（3 本、緑）

`oper` の 4 分岐のうち、**写しを作らない 3 本**は `Lift1` を通り抜けます:
⟹ ★ **(1) `|M| ≤ 1`** ／ **(2) 末尾が全零** ／ **(3) 末尾に親が無い**（既存 `lift_oper_of_noParent`）。
⟹ ⟹ ★★★★★ **残るのは「写しを作る」分岐だけ**です。 -/

open Classical in
/-- ★★★★★ **全零テストは `Lift1` で保たれます**。
⟹ ★ 理由: **`entry M 1 j1 = 0` なら `j1` は錐の外**（`nextrel1` は狭義増加）⟹ **持ち上がらない**。 -/
theorem zeroLast_Lift1_iff {M : TrioSeq} {t : ℕ} (hL : M.length - 1 ≠ 0) :
    (entry (Lift1 M t) 0 (M.length - 1) = 0 ∧ entry (Lift1 M t) 1 (M.length - 1) = 0
        ∧ entry (Lift1 M t) 2 (M.length - 1) = 0)
      ↔ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
        ∧ entry M 2 (M.length - 1) = 0) := by
  have hlt : M.length - 1 < M.length := by omega
  have h0 : entry (Lift1 M t) 0 (M.length - 1) = entry M 0 (M.length - 1) := entry0_Lift1 _ _ _
  have h2 : entry (Lift1 M t) 2 (M.length - 1) = entry M 2 (M.length - 1) := entry2_Lift1 _ _ _
  have h1 : entry (Lift1 M t) 1 (M.length - 1)
      = entry M 1 (M.length - 1) + (if le1 M 0 (M.length - 1) then t else 0) :=
    Wset.entry1_Lift1 hlt
  rw [h0, h2, h1]
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨a, by omega, c⟩
  · rintro ⟨a, b, c⟩
    refine ⟨a, ?_, c⟩
    rw [if_neg (not_in_cone_of_row1_le_root (by omega) (by omega))]
    omega

/-- ★★★★★★★★ **分岐 (2)**: 末尾が全零なら可換。 -/
theorem lift_oper_comm_of_zeroLast {M : TrioSeq} {t n : ℕ} (hL : M.length - 1 ≠ 0)
    (hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
      ∧ entry M 2 (M.length - 1) = 0) :
    (Lift1 M t)⟦n⟧ = Lift1 (M⟦n⟧) t := by
  have hlen : (Lift1 M t).length = M.length := Lift1_length M t
  have hL' : (Lift1 M t).length - 1 ≠ 0 := by rw [hlen]; exact hL
  have hz' : entry (Lift1 M t) 0 ((Lift1 M t).length - 1) = 0 ∧
      entry (Lift1 M t) 1 ((Lift1 M t).length - 1) = 0 ∧
      entry (Lift1 M t) 2 ((Lift1 M t).length - 1) = 0 := by
    rw [hlen]; exact (zeroLast_Lift1_iff hL).mpr hz
  rw [oper_eq_pred_of_zero n hL' hz', oper_eq_pred_of_zero n hL hz]
  unfold Pred
  rw [if_neg (by omega), if_neg (by omega), Lift1_dropLast]

/-- ★★★★★ **分岐 (1)**: `|M| ≤ 1` なら可換。 -/
theorem lift_oper_comm_of_short {M : TrioSeq} {t n : ℕ} (h : M.length - 1 = 0) :
    (Lift1 M t)⟦n⟧ = Lift1 (M⟦n⟧) t := by
  have hlen : (Lift1 M t).length = M.length := Lift1_length M t
  rw [oper_eq_self_of_short n (by rw [hlen]; exact h), oper_eq_self_of_short n h]

/-- ★★★★★★★★★★ ⟹ **まとめ: 写しを作らない 3 分岐は、全部通ります**。
⟹ ⛔ **残るのは「末尾に親があり、全零でなく、`|M| ≥ 2`」の 1 分岐だけ**です。 -/
theorem lift_oper_comm_of_no_copy {M : TrioSeq} {t n : ℕ}
    (h : M.length - 1 = 0 ∨
      (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
        ∧ entry M 2 (M.length - 1) = 0) ∨
      ¬ hasParent M (srow M (M.length - 1)) (M.length - 1)) :
    (Lift1 M t)⟦n⟧ = Lift1 (M⟦n⟧) t := by
  rcases h with h | h | h
  · exact lift_oper_comm_of_short h
  · by_cases hL : M.length - 1 = 0
    · exact lift_oper_comm_of_short hL
    · exact lift_oper_comm_of_zeroLast hL h
  · by_cases hL : M.length - 1 = 0
    · exact lift_oper_comm_of_short hL
    · exact lift_oper_of_noParent (by omega) h


/-! ## 129. ★★★★★★★★★★ (W78): **`liftInner_holds` の一般化** —— 根の形に依存しない版

L3 の `Lcone.liftInner_holds`（`Lcone:507`）は `M = (0,v,z) :: R`（`argOK R`）専用でした。
⟹ ★★★★★ **cons の形が使われているのは「設定」の部分だけ**で、
**本体（`gexp_cone_mir` を使う部分）は `hr0 M` と `0 < j0` しか要りません**。
⟹ ⟹ ★★★★★★★★★★ ⟹ **その 2 つを仮定に置けば、一般の `M` で通ります**。 -/

open Classical in
/-- ★★★★★★★★★★ **(W78)**: **`LiftOperComm` の一般版**（根の形にも `argOK` にも依りません）。
仮定は **`hr0 M`（根が狭義に最浅）** と **`0 < j0`（悪根が根そのものでない）** の 2 つだけ。 -/
theorem lift_oper_comm_of_hr0 {M : TrioSeq} {t n : ℕ}
    (hL : M.length - 1 ≠ 0)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hpM : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hj0pos : 0 < parent M (srow M (M.length - 1)) (M.length - 1)) :
    (Lift1 M t)⟦n⟧ = Lift1 (M⟦n⟧) t := by
  classical
  set j0 := parent M (srow M (M.length - 1)) (M.length - 1) with hj0def
  have hnrM : nextR M (srow M (M.length - 1)) j0 (M.length - 1) := parent_nextR hpM
  have hj0lt : j0 < M.length - 1 := nextR_index_lt hnrM
  set Lb := M.length - 1 - j0 with hLbdef
  have hLbpos : 0 < Lb := by omega
  have hlenM : j0 + Lb + 1 = M.length := by omega
  have hLbe : M.length - 1 - j0 = Lb := rfl
  set N : TrioSeq := Lift1 M t with hNdef
  have hNlen : N.length = M.length := by rw [hNdef]; exact Lift1_length M t
  have hNe0 : ∀ y, entry N 0 y = entry M 0 y := fun y => by
    rw [hNdef]; exact entry0_Lift1 M t y
  have hNe2 : ∀ y, entry N 2 y = entry M 2 y := fun y => by
    rw [hNdef]; exact entry2_Lift1 M t y
  have hNe1 : ∀ y, y < M.length →
      entry N 1 y = entry M 1 y + (if le1 M 0 y then t else 0) := by
    intro y hy; rw [hNdef, Wset.entry1_Lift1 hy]
  have hNlen1 : N.length - 1 = M.length - 1 := by rw [hNlen]
  have hLN : N.length - 1 ≠ 0 := by rw [hNlen1]; exact hL
  have hzN : ¬ (entry N 0 (N.length - 1) = 0 ∧ entry N 1 (N.length - 1) = 0 ∧
      entry N 2 (N.length - 1) = 0) := by
    rw [hNlen1, hNe0, hNe1 _ (by omega), hNe2]
    rintro ⟨h1, h2, h3⟩
    exact hz ⟨h1, by omega, h3⟩
  have hsrN : srow N (N.length - 1) = srow M (M.length - 1) := by
    rw [hNlen1, hNdef]; exact Wset.srow_Lift1 (by omega)
  have hpN : hasParent N (srow N (N.length - 1)) (N.length - 1) := by
    rw [hsrN, hNlen1, hNdef]; exact Wset.hasParent_Lift1.mpr hpM
  have hparN : parent N (srow N (N.length - 1)) (N.length - 1) = j0 := by
    rw [hsrN, hNlen1, hNdef, Wset.parent_Lift1]
  have hlenN : j0 + Lb + 1 = N.length := by rw [hNlen]; exact hlenM
  set D0 : ℕ := (if 0 < srow M (M.length - 1)
    then entry M 0 (M.length - 1) - entry M 0 j0 else 0) with hD0
  set D1 : ℕ := (if 1 < srow M (M.length - 1)
    then entry M 1 (M.length - 1) - entry M 1 j0 else 0) with hD1
  have hrtgx : Relation.ReflTransGen (nextrel0 M) j0 (M.length - 1) := by
    unfold nextR at hnrM
    by_cases h0 : srow M (M.length - 1) = 0
    · rw [if_pos h0] at hnrM; exact Relation.ReflTransGen.single hnrM
    · by_cases h1 : srow M (M.length - 1) = 1
      · rw [if_neg h0, if_pos h1] at hnrM; exact hnrM.2.2.2.2.1.2.2
      · rw [if_neg h0, if_neg h1] at hnrM; exact rtg1_rtg0 hnrM.2.2.2.2.1.2.2
  have hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l := by
    intro l hl0 hl1
    exact window_of_rtg0 hrtgx (by omega) l hl0 (by omega)
  have hD1N : (if 1 < srow N (N.length - 1)
      then entry N 1 (N.length - 1) - entry N 1 j0 else 0) = D1 := by
    rw [hsrN, hNlen1, hD1]
    by_cases h2 : 1 < srow M (M.length - 1)
    · rw [if_pos h2, if_pos h2]
      unfold nextR at hnrM
      rw [if_neg (by omega), if_neg (by omega)] at hnrM
      have hle1jx : le1 M j0 (M.length - 1) := hnrM.2.2.2.2.1
      have hiff : le1 M 0 (M.length - 1) ↔ le1 M 0 j0 :=
        ⟨fun h => le1_of_le1_le1 h hle1jx hj0pos, fun h => le1_trans h hle1jx⟩
      have hlt := le1_entry1_lt hle1jx (by omega)
      rw [hNe1 _ (by omega), hNe1 _ (by omega)]
      by_cases hc : le1 M 0 j0
      · rw [if_pos hc, if_pos (hiff.mpr hc)]; omega
      · rw [if_neg hc, if_neg (fun h => hc (hiff.mp h))]; omega
    · rw [if_neg h2, if_neg h2]
  have hD0N : (if 0 < srow N (N.length - 1)
      then entry N 0 (N.length - 1) - entry N 0 j0 else 0) = D0 := by
    rw [hsrN, hNlen1, hD0]
    by_cases h0 : 0 < srow M (M.length - 1)
    · rw [if_pos h0, if_pos h0, hNe0, hNe0]
    · rw [if_neg h0, if_neg h0]
  have hMe : M⟦n⟧ = gexp M j0 Lb D0 D1 n := by
    have h := oper_eq_gexp_gen (M := M) n hL hz hpM
    rw [← hj0def, hLbe] at h
    rw [h, hD0, hD1]
  have hNe : N⟦n⟧ = gexp N j0 Lb D0 D1 n := by
    have h := oper_eq_gexp_gen (M := N) n hLN hzN hpN
    rw [hparN, show N.length - 1 - j0 = Lb from by rw [hNlen1]] at h
    rw [h, hD0N, hD1N]
  have htrans : ∀ k q, k < n → q < Lb →
      (le1 (gexp M j0 Lb D0 D1 n) 0 (j0 + (k * Lb + q)) ↔ le1 M 0 (j0 + q)) := by
    intro k q hk hq
    by_cases h0 : 0 < srow M (M.length - 1)
    · have hlt0 : entry M 0 j0 < entry M 0 (M.length - 1) :=
        hup (M.length - 1) (by omega) (by omega)
      have hd0pos : 0 < D0 := by rw [hD0, if_pos h0]; omega
      have hd0e : entry M 0 (j0 + Lb) = entry M 0 j0 + D0 := by
        rw [hD0, if_pos h0, show j0 + Lb = M.length - 1 from by omega]
        omega
      have hlp : le1 M j0 (j0 + Lb) := by
        rw [show j0 + Lb = M.length - 1 from by omega]
        unfold nextR at hnrM
        by_cases h1 : srow M (M.length - 1) = 1
        · rw [if_neg (by omega), if_pos h1] at hnrM
          exact ⟨hnrM.1, hnrM.2.1, Relation.ReflTransGen.single hnrM⟩
        · rw [if_neg (by omega), if_neg h1] at hnrM
          exact hnrM.2.2.2.2.1
      exact gexp_cone_mir hlenM hj0pos hLbpos hk hq hup hd0pos hd0e hr0 hlp
    · have hD0z : D0 = 0 := by rw [hD0, if_neg h0]
      have hD1z : D1 = 0 := by rw [hD1, if_neg (by omega)]
      rw [hD0z, hD1z]
      exact gexp_cone_mir_flat hlenM hj0pos hLbpos hk hq hup hr0
  rw [hNe, hMe]
  have hXlenM : (gexp M j0 Lb D0 D1 n).length = j0 + n * Lb := gexp_length hlenM
  have hXlenN : (gexp N j0 Lb D0 D1 n).length = j0 + n * Lb := gexp_length hlenN
  refine list_ext_getD (by rw [hXlenN, Lift1_length, hXlenM]) ?_
  intro i hi
  rw [hXlenN] at hi
  rw [Lift1_getD (by rw [hXlenM]; exact hi)]
  rcases Nat.lt_or_ge i j0 with hij | hij
  · rw [gexp_getD_low hlenN hij, hNdef, Lift1_getD (by omega),
      gexp_entry_low hlenM hij, gexp_entry_low hlenM hij,
      gexp_entry_low hlenM hij]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    dsimp only
    rw [if_congr (gexp_cone_low hlenM hij) rfl rfl]
  · obtain ⟨k, q, hk, hq, rfl⟩ := gexp_pos_decomp hLbpos hij hi
    rw [gexp_getD_mir hlenN hk hq, gexp_entry0_mir hlenM hk hq,
      gexp_entry1_mir hlenM hk hq, gexp_entry2_mir hlenM hk hq,
      hNe0, hNe2, hNe1 _ (by omega)]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    dsimp only
    rw [if_congr (Wset.le1_Lift1 (X := M) (d := t) (a := j0) (b := j0 + q)) rfl rfl,
      if_congr (htrans k q hk hq) rfl rfl]
    omega


open Classical in
/-- ★★★★★★★★★★ ⟹ **4 分岐すべてを合わせた形**:
**`hr0 M`** ∧ **「親があるなら悪根は根でない」** ⟹ **`LiftOperComm` が成り立ちます**。
⟹ ⛔ **残るのは `j0 = 0`（悪根が根そのもの）の場合だけ**です。 -/
theorem lift_oper_comm_of_hr0_full {M : TrioSeq} {t n : ℕ}
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hj0 : hasParent M (srow M (M.length - 1)) (M.length - 1) →
      0 < parent M (srow M (M.length - 1)) (M.length - 1)) :
    (Lift1 M t)⟦n⟧ = Lift1 (M⟦n⟧) t := by
  by_cases hL : M.length - 1 = 0
  · exact lift_oper_comm_of_short hL
  · by_cases hz : (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
        entry M 2 (M.length - 1) = 0)
    · exact lift_oper_comm_of_zeroLast hL hz
    · by_cases hp : hasParent M (srow M (M.length - 1)) (M.length - 1)
      · exact lift_oper_comm_of_hr0 hL hz hp hr0 (hj0 hp)
      · exact lift_oper_of_noParent (by omega) hp


/-! ## 130. ★★★★★★★★★★ (W79): **ブロック根の行 0 の親** —— `d > 0` なら 1 つ前のブロックの中

第 `k` ブロックの根の行 0 は **`entry Q 0 0 + d*k`**（`entry0_mTower_block'`）。
⟹ ★ **`d > 0`** なら **狭義に増える等差列** ⟹ ⟹ ★★★ **親は 1 つ前のブロックの中**。
⟹ ★★★★★ **さらに `entry Q 0 0 + d ≤ entry Q 0 r`（すべての `r > 0`）なら、親は 1 つ前の「根」**。
⟹ ⛔ **`d = 0` なら、行 0 の親はありません**（＝ 孤児）。 -/

/-- ★★★★★★★★★★ **(W79)(a)**: `d > 0` なら、第 `n` ブロックの根の行 0 の親は
**第 `n−1` ブロックの中**（＝ `(n−1)|Q|` 以降）。 -/
theorem nextrel0_blockRoot_src_ge_prev (Q : TrioSeq) {d e n c : ℕ}
    (hQ : 0 < Q.length) (hd : 0 < d) (hn : 0 < n)
    (h : nextrel0 (mTower Q d e (n + 1)) c (n * Q.length)) :
    (n - 1) * Q.length ≤ c := by
  have hnq : (n - 1) * Q.length + Q.length = n * Q.length := by
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    subst hm; simp [Nat.succ_mul]
  have hdlt : d * (n - 1) < d * n := by
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    subst hm; simp [Nat.mul_succ]; omega
  have e1 : entry (mTower Q d e (n + 1)) 0 (n * Q.length) = entry Q 0 0 + d * n := by
    simpa using entry0_mTower_block' Q (d := d) (e := e) (n := n + 1) (k := n) (i := 0)
      (by omega) hQ
  have e2 : entry (mTower Q d e (n + 1)) 0 ((n - 1) * Q.length)
      = entry Q 0 0 + d * (n - 1) := by
    simpa using entry0_mTower_block' Q (d := d) (e := e) (n := n + 1) (k := n - 1) (i := 0)
      (by omega) hQ
  by_contra hc
  push Not at hc
  have hmin := h.2.2.2.2 ((n - 1) * Q.length) ⟨by omega, by omega⟩
  rw [e1, e2] at hmin
  omega

/-- ★★★★★★★★★★ **(W79)(b)**: さらに **`Q` の各列が根より `d` 以上深い**なら、
**親はちょうど 1 つ前のブロックの根**。 -/
theorem nextrel0_blockRoot_prev_root (Q : TrioSeq) {d e n : ℕ}
    (hQ : 0 < Q.length) (hd : 0 < d) (hn : 0 < n)
    (hgap : ∀ r, 0 < r → r < Q.length → entry Q 0 0 + d ≤ entry Q 0 r) :
    nextrel0 (mTower Q d e (n + 1)) ((n - 1) * Q.length) (n * Q.length) := by
  have hlen : (mTower Q d e (n + 1)).length = (n + 1) * Q.length :=
    mTower_length Q d e (n + 1)
  have hnq : (n - 1) * Q.length + Q.length = n * Q.length := by
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    subst hm; simp [Nat.succ_mul]
  have hnq1 : (n + 1) * Q.length = n * Q.length + Q.length := Nat.succ_mul n Q.length
  have hdlt : d * (n - 1) < d * n := by
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    subst hm; simp [Nat.mul_succ]; omega
  have hd1 : d * n = d * (n - 1) + d := by
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    subst hm; simp [Nat.mul_succ]
  have e1 : entry (mTower Q d e (n + 1)) 0 (n * Q.length) = entry Q 0 0 + d * n := by
    simpa using entry0_mTower_block' Q (d := d) (e := e) (n := n + 1) (k := n) (i := 0)
      (by omega) hQ
  have e2 : entry (mTower Q d e (n + 1)) 0 ((n - 1) * Q.length)
      = entry Q 0 0 + d * (n - 1) := by
    simpa using entry0_mTower_block' Q (d := d) (e := e) (n := n + 1) (k := n - 1) (i := 0)
      (by omega) hQ
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · rw [e1, e2]; omega
  · rintro j ⟨hj1, hj2⟩
    obtain ⟨r, rfl⟩ : ∃ r, j = (n - 1) * Q.length + r := ⟨j - (n - 1) * Q.length, by omega⟩
    have hr : r < Q.length := by omega
    rw [e1, entry0_mTower_block' Q (show n - 1 < n + 1 by omega) hr]
    have := hgap r (by omega) hr
    omega

/-- ⛔ **(W79)(c)**: **`d = 0` なら、ブロック根に行 0 の親はありません**（＝ 孤児）。 -/
theorem no_nextrel0_blockRoot_of_d_zero (Q : TrioSeq) {e n c : ℕ}
    (hQ : 0 < Q.length)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) :
    ¬ nextrel0 (mTower Q 0 e (n + 1)) c (n * Q.length) := by
  intro h
  have hlen : (mTower Q 0 e (n + 1)).length = (n + 1) * Q.length :=
    mTower_length Q 0 e (n + 1)
  have hclt : c < (n + 1) * Q.length := by have := h.1; rw [hlen] at this; exact this
  have hlt := h.2.2.2.1
  have hk : c / Q.length < n + 1 :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm] at hclt; exact hclt)
  have hr : c % Q.length < Q.length := Nat.mod_lt _ hQ
  have hsplit : c = (c / Q.length) * Q.length + c % Q.length :=
    (Nat.div_add_mod' c Q.length).symm
  have e1 : entry (mTower Q 0 e (n + 1)) 0 (n * Q.length) = entry Q 0 0 := by
    simpa using entry0_mTower_block' Q (d := 0) (e := e) (n := n + 1) (k := n) (i := 0)
      (by omega) hQ
  rw [hsplit, entry0_mTower_block' Q hk hr, e1] at hlt
  rcases Nat.eq_zero_or_pos (c % Q.length) with h0 | h0
  · rw [h0] at hlt; omega
  · have := hr0 (c % Q.length) h0 hr; omega


/-! ## 131. ★★★★★★★★★★ (W79'): **親は「直前のブロックの中」** —— (W79)(a) から両側で

(W79)(a) が下限 `(n−1)|Q| ≤ c` を、`nextrel0` の定義が上限 `c < n|Q|` をくれます。
⟹ ★★★★★ ⟹ **`c` は第 `n−1` ブロックの中**（根とは限りません）。
⟹ ★ そして **snoc の形**（`mTower Q d e n ++ [第 `n` ブロックの根]`）にも、`take` で移せます。 -/

/-- ★★★★★★★★★★ **(W79')**: `0 < d` ∧ `0 < n` ⟹ **親は第 `n−1` ブロックの中**（両側）。 -/
theorem nextrel0_blockRoot_in_prev_block (Q : TrioSeq) {d e n c : ℕ}
    (hQ : 0 < Q.length) (hd : 0 < d) (hn : 0 < n)
    (h : nextrel0 (mTower Q d e (n + 1)) c (n * Q.length)) :
    (n - 1) * Q.length ≤ c ∧ c < n * Q.length :=
  ⟨nextrel0_blockRoot_src_ge_prev Q hQ hd hn h, h.2.2.1⟩

/-- ★★★★★ ⟹ **窓は `|Q|` を超えません**（`|T| − 1 − 親 ≤ |Q|`）。 -/
theorem window_le_of_blockRoot (Q : TrioSeq) {d e n c : ℕ}
    (hQ : 0 < Q.length) (hd : 0 < d) (hn : 0 < n)
    (h : nextrel0 (mTower Q d e (n + 1)) c (n * Q.length)) :
    n * Q.length - c ≤ Q.length := by
  have hge := nextrel0_blockRoot_src_ge_prev Q hQ hd hn h
  have hnq : (n - 1) * Q.length + Q.length = n * Q.length := by
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    subst hm; simp [Nat.succ_mul]
  omega

/-- ★★★★★★★★ ⟹ **snoc の形に移した版**:
**`mTower Q d e n ++ (第 `n` ブロック).take 1` の末尾列の行 0 の親は、第 `n−1` ブロックの中**。 -/
theorem nextrel0_snoc_blockRoot_in_prev (Q : TrioSeq) {d e n c : ℕ}
    (hQ : 0 < Q.length) (hd : 0 < d) (hn : 0 < n)
    (h : nextrel0 (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take 1)
      c (n * Q.length)) :
    (n - 1) * Q.length ≤ c ∧ c < n * Q.length := by
  have hlen : (mTower Q d e (n + 1)).length = (n + 1) * Q.length :=
    mTower_length Q d e (n + 1)
  have hnq1 : (n + 1) * Q.length = n * Q.length + Q.length := Nat.succ_mul n Q.length
  rw [show (1 : ℕ) = 0 + 1 from rfl, mTower_append_take Q d e n 0] at h
  have h' : nextrel0 (mTower Q d e (n + 1)) c (n * Q.length) :=
    (Wset.nextrel0_take (X := mTower Q d e (n + 1)) (l := n * Q.length + (0 + 1))
      (by omega) (by omega)).mp h
  exact nextrel0_blockRoot_in_prev_block Q hQ hd hn h'


/-! ## 132. ★★★★★★★★★★ (W81): **`j > 0` なら親は同じブロックの中**

`d > 0` のとき、**第 `k` ブロックの根は、そこから先の全列より狭義に浅い**:
⟹ ★ **同じブロックの中** … `entry Q 0 r + d*k > entry Q 0 0 + d*k`（`hr0`）
⟹ ★ **後のブロック** … `entry Q 0 r + d*k' ≥ entry Q 0 0 + d*k' > entry Q 0 0 + d*k`（`d > 0`）
⟹ ⟹ ★★★★★ **私の `nextrel0_src_ge_of_shallow`（§310）がそのまま当たります**。 -/

/-- ★★★★★ **ブロック根は、そこから先の全列より狭義に浅い**（`d > 0`）。 -/
theorem blockRoot_shallow_mTower (Q : TrioSeq) {d e n k : ℕ} (hd : 0 < d) (hk : k < n)
    (hQ : 0 < Q.length)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l) :
    ∀ x, k * Q.length < x → x < (mTower Q d e n).length →
      entry (mTower Q d e n) 0 (k * Q.length) < entry (mTower Q d e n) 0 x := by
  intro x hx1 hx2
  have hlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  rw [hlen] at hx2
  have hk' : x / Q.length < n :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm] at hx2; exact hx2)
  have hr : x % Q.length < Q.length := Nat.mod_lt _ hQ
  have hsplit : x = (x / Q.length) * Q.length + x % Q.length :=
    (Nat.div_add_mod' x Q.length).symm
  have e1 : entry (mTower Q d e n) 0 (k * Q.length) = entry Q 0 0 + d * k := by
    simpa using entry0_mTower_block' Q (d := d) (e := e) (n := n) (k := k) (i := 0) hk hQ
  rw [e1, hsplit, entry0_mTower_block' Q hk' hr]
  have hge : entry Q 0 0 ≤ entry Q 0 (x % Q.length) := by
    rcases Nat.eq_zero_or_pos (x % Q.length) with h0 | h0
    · rw [h0]
    · exact le_of_lt (hr0 _ h0 hr)
  rcases Nat.lt_or_ge k (x / Q.length) with hlt | hge2
  · have : d * k < d * (x / Q.length) := by
      have h1 : d * (k + 1) ≤ d * (x / Q.length) := Nat.mul_le_mul_left d (by omega)
      have h2 : d * (k + 1) = d * k + d := Nat.mul_succ d k
      omega
    omega
  · have hkq : x / Q.length = k := by
      by_contra hne
      have hlt2 : x / Q.length < k := by omega
      have : (x / Q.length) * Q.length + Q.length ≤ k * Q.length := by
        have h1 : (x / Q.length + 1) * Q.length ≤ k * Q.length :=
          Nat.mul_le_mul_right _ (by omega)
        have h2 : (x / Q.length + 1) * Q.length = (x / Q.length) * Q.length + Q.length :=
          Nat.succ_mul _ _
        omega
      omega
    rw [hkq]
    have hr0pos : 0 < x % Q.length := by
      by_contra hc
      push Not at hc
      have : x % Q.length = 0 := by omega
      rw [hkq, this] at hsplit
      omega
    have := hr0 _ hr0pos hr
    omega

/-- ★★★★★★★★★★ **(W81)**: `d > 0` ∧ `0 < j` ⟹ **行 0 の親は同じブロックの中**。 -/
theorem nextrel0_src_ge_blockRoot_mTower (Q : TrioSeq) {d e n k j c : ℕ}
    (hd : 0 < d) (hk : k < n) (hj : j < Q.length) (hj0 : 0 < j)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (h : nextrel0 (mTower Q d e n) c (k * Q.length + j)) :
    k * Q.length ≤ c :=
  nextrel0_src_ge_of_shallow
    (blockRoot_shallow_mTower Q hd hk (by omega) hr0) (by omega) h

/-- ★★★★★ ⟹ **窓は `|Q|` 未満**（`j > 0` の版）。 -/
theorem window_lt_of_blockInner (Q : TrioSeq) {d e n k j c : ℕ}
    (hd : 0 < d) (hk : k < n) (hj : j < Q.length) (hj0 : 0 < j)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (h : nextrel0 (mTower Q d e n) c (k * Q.length + j)) :
    k * Q.length + j - c < Q.length := by
  have := nextrel0_src_ge_blockRoot_mTower Q hd hk hj hj0 hr0 h
  omega


/-! ## 133. ★★★★★★★★★★ (W81'): **`srow ≥ 1` でも親は直前のブロックの中**（`e > 0`）

`nextrel1` の源は **`le0` 祖先**。⟹ ★ そして **(W79)(a) より行 0 の親は第 `n−1` ブロックの中**、
**その先祖にブロック根がいる**（`le0_blockRoot_mTower`）⟹ ⟹ ★★ **ブロック根は `le0` 祖先**。
⟹ ★★★★★ **`e > 0` なら、根の行 1 は `+e*(n−1)` で的（`+e*n`）より真に低い**
⟹ ⟹ ★★★★★★★★★★ ⟹ **最小性が、根より前の候補を全部落とします**。 -/

/-- ★★★★★★★★★★ **(W81')**: `d > 0` ∧ `e > 0` ⟹ **ブロック根の行 1 の親も、第 `n−1` ブロックの中**。 -/
theorem nextrel1_blockRoot_src_ge_prev (Q : TrioSeq) {d e n c : ℕ}
    (hQ : 0 < Q.length) (hd : 0 < d) (he : 0 < e) (hn : 0 < n)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (h : nextrel1 (mTower Q d e (n + 1)) c (n * Q.length)) :
    (n - 1) * Q.length ≤ c := by
  have hlen : (mTower Q d e (n + 1)).length = (n + 1) * Q.length :=
    mTower_length Q d e (n + 1)
  have hnq : (n - 1) * Q.length + Q.length = n * Q.length := by
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    subst hm; simp [Nat.succ_mul]
  have hnq1 : (n + 1) * Q.length = n * Q.length + Q.length := Nat.succ_mul n Q.length
  have hclt : c < n * Q.length := h.2.2.1
  have hroot : le1 Q 0 0 := ⟨hQ, hQ, Relation.ReflTransGen.refl⟩
  have e1 : ∀ k, k < n + 1 → entry (mTower Q d e (n + 1)) 1 (k * Q.length)
      = entry Q 1 0 + e * k := by
    intro k hk
    have := entry1_mTower_block_formula Q (d := d) (e := e) (n := n + 1) (k := k) (i := 0) hk hQ
    rw [if_pos hroot] at this
    simpa using this
  -- 行 0 の親は第 `n−1` ブロックの中（(W79)(a)）
  have hle0 : le0 (mTower Q d e (n + 1)) ((n - 1) * Q.length) (n * Q.length) := by
    rcases Relation.ReflTransGen.cases_tail h.2.2.2.2.1.2.2 with h1 | ⟨c0, hc1, hc2⟩
    · exact absurd h1.symm (by omega)
    · have hge := nextrel0_blockRoot_src_ge_prev Q hQ hd hn hc2
      have hlt0 : c0 < n * Q.length := hc2.2.2.1
      rcases Nat.eq_or_lt_of_le hge with heq | hgt
      · exact ⟨by omega, by omega, by rw [heq]; exact Relation.ReflTransGen.single hc2⟩
      · obtain ⟨r, rfl⟩ : ∃ r, c0 = (n - 1) * Q.length + r :=
          ⟨c0 - (n - 1) * Q.length, by omega⟩
        have hr : r < Q.length := by omega
        have hb := le0_blockRoot_mTower Q (d := d) (e := e) (n := n + 1)
          (k := n - 1) (i := r) hr0 (by omega) hr (by omega)
        exact ⟨by omega, by omega, hb.2.2.tail hc2⟩
  by_contra hc
  push Not at hc
  have hmin := h.2.2.2.2.2 ((n - 1) * Q.length) ⟨by omega, hle0⟩
  rw [e1 n (by omega), e1 (n - 1) (by omega)] at hmin
  have hdlt : e * (n - 1) < e * n := by
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    subst hm; simp [Nat.mul_succ]; omega
  omega


/-! ## 134. ★★★★★★★★★★ (W82): **`j > 0` の `srow ≥ 1`** —— (W56) の接頭辞なし版

`prefix_mTower_nextrel1_src_ge`（(W56)）を **`A = []`** で使うと、そのまま出ます。
⟹ ★ **仮定は「`j` が `Q` の中で行 1 の親を持つ」だけ**（`d`, `e` は何でもよい）。
⟹ ⛔ **`j` が `Q` の中で行 1 の孤児のときだけ、越境の可能性が残ります**（(W56) の穴と同じ）。 -/

/-- ★★★★★★★★★★ **(W82) 行 1**: 証人があれば、**塔の行 1 の親は同じブロックの中**。 -/
theorem nextrel1_mTower_src_ge_block_of_witness (Q : TrioSeq) {d e n k j y c : ℕ}
    (hk : k < n) (hj : j < Q.length) (hy : nextrel1 Q y j)
    (h : nextrel1 (mTower Q d e n) c (k * Q.length + j)) :
    k * Q.length ≤ c := by
  have h' : nextrel1 ([] ++ mTower Q d e n) c (([] : TrioSeq).length + (k * Q.length + j)) := by
    simpa using h
  have := prefix_mTower_nextrel1_src_ge (A := []) hk hj hy h'
  simpa using le_trans (by omega) this

/-- ★★★★★★★★ **(W82) 行 2**（`e = 0`）: 証人があれば、**行 2 の親も同じブロックの中**。 -/
theorem nextrel2_mTower_src_ge_block_of_witness (Q : TrioSeq) {d n k j y c : ℕ}
    (hk : k < n) (hj : j < Q.length) (hy : nextrel2 Q y j)
    (h : nextrel2 (mTower Q d 0 n) c (k * Q.length + j)) :
    k * Q.length ≤ c := by
  have h' : nextrel2 ([] ++ mTower Q d 0 n) c (([] : TrioSeq).length + (k * Q.length + j)) := by
    simpa using h
  have := prefix_mTower_nextrel2_src_ge_of_e_zero (A := []) hk hj hy h'
  simpa using le_trans (by omega) this

/-- ★★★★★★★★★★ ⟹ **まとめ（`e = 0`）**: **`Q` の中で親を持てば、塔でも同じブロックの中**。
⟹ ★ `i` は 0, 1, 2 のどれでもよい（行 0 は (W81) が `d > 0` で覆います）。 -/
theorem nextR_mTower_src_ge_block_of_hasParent (Q : TrioSeq) {d n k j c i : ℕ}
    (hk : k < n) (hj : j < Q.length) (hj0 : 0 < j) (hd : 0 < d)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hpar : hasParent Q i j)
    (h : nextR (mTower Q d 0 n) i c (k * Q.length + j)) :
    k * Q.length ≤ c := by
  obtain ⟨y, hy, -⟩ := hpar
  unfold nextR at h hy
  split_ifs at h hy with h0 h1
  · exact nextrel0_src_ge_blockRoot_mTower Q hd hk hj hj0 hr0 h
  · exact nextrel1_mTower_src_ge_block_of_witness Q hk hj hy h
  · exact nextrel2_mTower_src_ge_block_of_witness Q hk hj hy h

end H12H2
end TRIO
