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
    `Wtower2.W_drop`（`Wtower2:2870`）… `M ∈ W u → M.drop j ∈ W (lev M j)`

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

end H12H2
end TRIO
