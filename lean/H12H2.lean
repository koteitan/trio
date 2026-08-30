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

end H12H2
end TRIO
