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

end H12H2
end TRIO
