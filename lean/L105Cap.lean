/-
L105Cap.lean: 課題 L105 —— **`CoreCap`（`Lind.lean:176`）を狙う**。

`CoreCap` は `Final.lean` の 28 核のうちの極小元のひとつで、**`GX` を含まない
純 `W` レベルの 1 文**（7 量化 / 5 前提）:

```lean
def CoreCap : Prop :=
  ∀ (M : TrioSeq), argOK M → 1 ≤ M.length → ∀ v z : ℕ, z ≤ 1 → CtxOK M v z →
    ∀ b c a t : ℕ, 2 * (v + t) + z ≤ a →
      Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: cap M b c) t ∈ W a
```

この file の主張は 1 行で言える:

> **`CoreCap` の段リフト `t` は自由変数にすぎない。**
> `Lift1` は `snoc` と可換（`Lift1_snoc`）なので、`t ≥ 1` でも `t = 0` でも
> **同じ snoc 問題**に落ちる。

⟹ 前任 L2 の `L53.cons_cap_of_wsnoc`（`t = 0` 限定）は **全 `t` に一般化できる**。
-/
import Lind
import L53Subst

namespace TRIO
namespace L105

open Wset
open Classical

/-! ## 1. `Lift1` は末尾 snoc と可換

`Lift1_dropLast`（`Wset.lean:1007`）が `(Lift1 X d).dropLast = Lift1 X.dropLast d`
を与えるので、`Lift1 (C ++ [p]) d` は `Lift1 C d` に 1 列足したものである。
足された列が何であるかは（`WSnoc` が `p` を全称するので）**使わない**。 -/

theorem Lift1_snoc_ne {C : TrioSeq} {p : ℕ × ℕ × ℕ} {d : ℕ} :
    Lift1 (C ++ [p]) d ≠ [] := by
  intro h
  have hl := congrArg List.length h
  rw [Lift1_length] at hl
  simp at hl

theorem entry_snoc_last (A : TrioSeq) (q : ℕ × ℕ × ℕ) (i : ℕ) :
    entry (A ++ [q]) i A.length = entry [q] i 0 := by
  simpa using entry_append_right A [q] i 0

/-- **★ `Lift1` は snoc と可換**（足す列の行 1 だけが取り替わる。行 0・行 2 は不変）。 -/
theorem Lift1_snoc (C : TrioSeq) (p : ℕ × ℕ × ℕ) (d : ℕ) :
    ∃ q : ℕ × ℕ × ℕ,
      Lift1 (C ++ [p]) d = Lift1 C d ++ [q] ∧ q.1 = p.1 ∧ q.2.2 = p.2.2 := by
  set q : ℕ × ℕ × ℕ := (Lift1 (C ++ [p]) d).getLast Lift1_snoc_ne with hqdef
  have heq : Lift1 (C ++ [p]) d = Lift1 C d ++ [q] := by
    conv_lhs =>
      rw [← List.dropLast_append_getLast (Lift1_snoc_ne (C := C) (p := p) (d := d))]
    congr 1
    rw [Lift1_dropLast]
    simp
  have hlen : (Lift1 C d).length = C.length := Lift1_length C d
  refine ⟨q, heq, ?_, ?_⟩
  · have hA : entry (Lift1 (C ++ [p]) d) 0 C.length = p.1 := by
      rw [entry0_Lift1]
      simpa using entry_snoc_last C p 0
    have hB : entry (Lift1 C d ++ [q]) 0 C.length = q.1 := by
      have h := entry_snoc_last (Lift1 C d) q 0
      rw [hlen] at h
      simpa using h
    rw [heq] at hA
    omega
  · have hA : entry (Lift1 (C ++ [p]) d) 2 C.length = p.2.2 := by
      rw [entry2_Lift1]
      simpa using entry_snoc_last C p 2
    have hB : entry (Lift1 C d ++ [q]) 2 C.length = q.2.2 := by
      have h := entry_snoc_last (Lift1 C d) q 2
      rw [hlen] at h
      simpa using h
    rw [heq] at hA
    omega

/-! ## 2. `(0,v,z) :: cap M b c` は「接頭辞パッケージに 1 列 snoc」 -/

theorem cons_cap_split (M : TrioSeq) (v z b c : ℕ) :
    (((0, v, z) : ℕ × ℕ × ℕ) :: cap M b c)
      = ((((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast)
          ++ [((entry M 0 (M.length - 1), b, c) : ℕ × ℕ × ℕ)]) := by
  unfold cap
  rw [List.cons_append]

/-- `CtxOK` の `k = |M| - 1` の項が、まさに snoc の土台を供給する。 -/
theorem ctxOK_dropLast {M : TrioSeq} {v z : ℕ} (hctx : CtxOK M v z)
    (hM2 : 1 ≤ M.length) {a t : ℕ} (hva : 2 * (v + t) + z ≤ a) :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast) t ∈ W a := by
  rw [List.dropLast_eq_take]
  exact hctx (M.length - 1) (by omega) a t hva

theorem cons_dropLast_ne {M : TrioSeq} {v z t : ℕ} :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast) t ≠ [] := by
  intro h
  have hl := congrArg List.length h
  rw [Lift1_length] at hl
  simp at hl

/-! ## 3. ★★★ `CoreCap ⟸ WSnoc`（**全 `t`**）

前任 L2 の `L53.cons_cap_of_wsnoc` は `t = 0` 専用だった。`Lift1_snoc` を挟むと
**リフト `t` は結論の 1 列を取り替えるだけ**なので、そのまま全 `t` に伸びる。 -/

theorem coreCap_of_wsnoc (hsn : WSnoc) : CoreCap := by
  intro M _ hM2 v z _ hctx b c a t hva
  rw [cons_cap_split M v z b c]
  obtain ⟨q, hq, -, -⟩ :=
    Lift1_snoc (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast)
      ((entry M 0 (M.length - 1), b, c) : ℕ × ℕ × ℕ) t
  rw [hq]
  exact snoc_step hsn q (ctxOK_dropLast hctx hM2 hva) cons_dropLast_ne


/-! ## 4. ★★ 段によらない snoc の三分法

`snoc_step`（`Wtower2.lean:2056`）の中に**孤児の枝が段 `u` のまま**埋まっていた
（`Wself` ではなく `W u` で閉じている）。抜き出して単独の補題にする。 -/

open Classical in
/-- **孤児 snoc は段によらず無料。**（`snoc_orphan` は `Wself` 版だが、
`mem_of_oper_mem`（`Wchar.lean:73`）を使えば任意の段 `u` で同じことが言える。） -/
theorem snoc_orphan_W {u : ℕ} {C : TrioSeq} (p : ℕ × ℕ × ℕ)
    (hC : C ∈ W u) (hCne : C ≠ [])
    (hnp : ¬ hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length) :
    C ++ [p] ∈ W u := by
  have hClen : 0 < C.length := List.length_pos_iff.mpr hCne
  have hlen : (C ++ [p]).length - 1 = C.length := by simp
  refine mem_of_oper_mem (fun n _ => ?_)
  have hL : (C ++ [p]).length - 1 ≠ 0 := by rw [hlen]; omega
  have hpr : (C ++ [p])⟦n⟧ = Pred (C ++ [p]) := by
    by_cases hz : entry (C ++ [p]) 0 ((C ++ [p]).length - 1) = 0 ∧
        entry (C ++ [p]) 1 ((C ++ [p]).length - 1) = 0 ∧
        entry (C ++ [p]) 2 ((C ++ [p]).length - 1) = 0
    · exact oper_eq_pred_of_zero n hL hz
    · exact oper_eq_pred_of_noParent n hL hz (by rw [hlen]; exact hnp)
  rw [hpr]
  unfold Pred
  rw [if_neg (by simp; omega), List.dropLast_concat]
  exact hC

open Classical in
/-- **★★ snoc は 2 条件（親あり・行 2 に非零あり）を満たす場合だけ開いている。**
`WSnoc` を仮定せずに済む枝を、段 `u` のまま全部落としたもの。 -/
theorem snoc_of_open {u : ℕ} {C : TrioSeq} (p : ℕ × ℕ × ℕ)
    (hC : C ∈ W u) (hCne : C ≠ [])
    (hopen : hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length →
      (∃ q ∈ C, 0 < q.2.2) → C ++ [p] ∈ W u) :
    C ++ [p] ∈ W u := by
  by_cases hpar : hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length
  · by_cases hz2 : ∃ q ∈ C, 0 < q.2.2
    · exact hopen hpar hz2
    · have hz2' : ∀ q ∈ C, q.2.2 = 0 := by
        intro q hq
        by_contra hc
        exact hz2 ⟨q, hq, by omega⟩
      have hClen : 0 < C.length := List.length_pos_iff.mpr hCne
      have hself : (C ++ [p]) ∈ Wself := snoc_zeroRow2 (M' := C) hz2' p
      have hlev : lev (C ++ [p]) 0 ≤ u := by
        have hE : ∀ i, entry (C ++ [p]) i 0 = entry C i 0 := by
          intro i; unfold entry; rw [getD_append_left hClen]
        have h1 : lev (C ++ [p]) 0 = lev C 0 := by unfold lev; rw [hE 1, hE 2]
        rw [h1]
        exact lev_root_le_of_mem_W hC hCne
      exact W_mono hlev hself
  · exact snoc_orphan_W p hC hCne hpar

/-! ## 5. ★★★ `CtxOK` の未使用分 —— **土台の接頭辞が全部 `W a` にいる**

`CoreCap` の土台は `capBase M v z t = Lift1 ((0,v,z) :: M.dropLast) t`。
`ctxOK_dropLast` は `CtxOK` の `k = |M|-1` の項しか使っていないが、
**残りの `k` は「`capBase` のすべての接頭辞が同じ段 `W a` にいる」を与える**。
一般の `WSnoc` にはこの情報が無い。⟹ 残核はここで細くなる。 -/

open Classical in
/-- `CoreCap` の snoc の土台。 -/
noncomputable def capBase (M : TrioSeq) (v z t : ℕ) : TrioSeq :=
  Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast) t

@[simp] theorem capBase_length (M : TrioSeq) (v z t : ℕ) :
    (capBase M v z t).length = M.dropLast.length + 1 := by
  unfold capBase; simp

theorem capBase_ne (M : TrioSeq) (v z t : ℕ) : capBase M v z t ≠ [] := by
  intro h
  have hl := congrArg List.length h
  rw [capBase_length] at hl
  simp at hl

theorem capBase_mem {M : TrioSeq} {v z a t : ℕ} (hctx : CtxOK M v z)
    (hM2 : 1 ≤ M.length) (hva : 2 * (v + t) + z ≤ a) :
    capBase M v z t ∈ W a :=
  ctxOK_dropLast hctx hM2 hva

/-- **★★★ 土台のすべての接頭辞が `W a` にいる。**（`CtxOK` の全項を使う。） -/
theorem capBase_take_mem {M : TrioSeq} {v z a t : ℕ} (hctx : CtxOK M v z)
    (hM2 : 1 ≤ M.length) (hva : 2 * (v + t) + z ≤ a) (j : ℕ) :
    (capBase M v z t).take j ∈ W a := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simpa using W_nil a
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rcases Nat.lt_or_ge (k + 1) (M.dropLast.length + 1) with hlt | hge
    · unfold capBase
      rw [Lift1_take (by simp only [List.length_cons]; omega),
        List.take_succ_cons, List.dropLast_eq_take, List.take_take]
      exact hctx (min k (M.length - 1)) (by omega) a t hva
    · rw [List.take_of_length_le (by rw [capBase_length]; omega)]
      exact capBase_mem hctx hM2 hva

/-! ## 6. ★★★★ 残核 `SnocPrefixOpen`

`CoreCap` を `snoc_of_open` ＋ `capBase_take_mem` に通すと、残るのは次の 1 文だけ:

    土台 `C` の**すべての接頭辞**が `W u` にいて、足す 1 列が**親を持ち**、
    `C` の行 2 に非零があるとき、`C ++ [p] ∈ W u`。

**`WSnocOpen1`（`L53Subst.lean:3727`）より前提が 1 本多い**（接頭辞の全所属）ので
真に弱い。しかも `srow` の場合分けも `argOK` も `CtxOK` も `Lift1` も**出てこない**。 -/

/-- **`CoreCap` の残核**。`WSnoc` から出るが、逆は言えない（前提が多い）。 -/
def SnocPrefixOpen : Prop :=
  ∀ (u : ℕ) (C : TrioSeq) (p : ℕ × ℕ × ℕ), C ≠ [] →
    (∀ j, (C.take j) ∈ W u) →
    hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length →
    (∃ q ∈ C, 0 < q.2.2) →
    C ++ [p] ∈ W u

/-- **★★★★ `SnocPrefixOpen` 1 本で `CoreCap` が出る。** -/
theorem coreCap_of_snocPrefixOpen (h : SnocPrefixOpen) : CoreCap := by
  intro M _ hM2 v z _ hctx b c a t hva
  rw [cons_cap_split M v z b c]
  obtain ⟨q, hq, -, -⟩ :=
    Lift1_snoc (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast)
      ((entry M 0 (M.length - 1), b, c) : ℕ × ℕ × ℕ) t
  rw [hq]
  show capBase M v z t ++ [q] ∈ W a
  refine snoc_of_open q (capBase_mem hctx hM2 hva) (capBase_ne M v z t) ?_
  intro hpar hz2
  exact h a (capBase M v z t) q (capBase_ne M v z t)
    (capBase_take_mem hctx hM2 hva) hpar hz2

/-- 位置づけ: `WSnoc` からは当然出る（接頭辞の情報を捨てるだけ）。 -/
theorem snocPrefixOpen_of_wsnoc (hsn : WSnoc) : SnocPrefixOpen := by
  intro u C p hCne hpre hpar _
  exact hsn u C p (by simpa using hpre C.length) hCne hpar

/-! ## 7. `srow = 0` 枝は `PrefixCopies` で落ちる（L2 の道具がそのまま効く） -/

/-- `srow ≥ 1` に絞った残核。 -/
def SnocPrefixOpen1 : Prop :=
  ∀ (u : ℕ) (C : TrioSeq) (p : ℕ × ℕ × ℕ), C ≠ [] →
    (∀ j, (C.take j) ∈ W u) →
    hasParent (C ++ [p]) (srow (C ++ [p]) C.length) C.length →
    (∃ q ∈ C, 0 < q.2.2) →
    srow (C ++ [p]) C.length ≠ 0 →
    C ++ [p] ∈ W u

open Classical in
theorem snocPrefixOpen_of_prefixCopies (hpc : L53.PrefixCopies)
    (h : SnocPrefixOpen1) : SnocPrefixOpen := by
  intro u C p hCne hpre hpar hz2
  by_cases hs : srow (C ++ [p]) C.length = 0
  · exact L53.wsnoc_srow0_of_prefixCopies hpc (by simpa using hpre C.length) hCne hs hpar
  · exact h u C p hCne hpre hpar hz2 hs

theorem coreCap_of_prefixCopies (hpc : L53.PrefixCopies) (h : SnocPrefixOpen1) :
    CoreCap :=
  coreCap_of_snocPrefixOpen (snocPrefixOpen_of_prefixCopies hpc h)


/-! ## 8. ⚠ **空振り 1**: `CtxOK` の「接頭辞が全部 `W a`」は**無料**だった

§5 で `capBase_take_mem` を作り、「一般の `WSnoc` にはこの情報が無いので残核が細くなる」
と書いたが、**`Wset.W_take`（`Wset.lean:2120`）が `M ∈ W u → M.take k ∈ W u` を
無条件で与える**。⟹ 接頭辞の全所属は `capBase ∈ W a` から自動で出るので、
`SnocPrefixOpen` は `WSnoc`（の行 2 非零の場合）と**同値**であって、弱くはない。

（`L53Subst.lean:3802` に「`A ++ Q ∈ W u` から `A ∈ W u` は `W_take` で無料」と
既に書いてあった。**教訓「作業前に既存のものを読む」の再発。**）

下の `wsnoc_of_snocPrefixOpen` がその証明。**`SnocPrefixOpen` は残核ではない。** -/

open Classical in
/-- ⚠ **逆も成り立つ** ⟹ `SnocPrefixOpen` は `WSnoc` より弱くない。 -/
theorem wsnoc_of_snocPrefixOpen (h : SnocPrefixOpen) : WSnoc := by
  intro u C p hC hCne hpar
  refine snoc_of_open p hC hCne ?_
  intro _ hz2
  exact h u C p hCne (fun j => W_take hC j) hpar hz2

/-! ## 9. ★★★★ 形を保った残核 `CapSnocOpen`

⟹ 残核を細くしたいなら、**土台の形を捨ててはいけない**。`CoreCap` の土台は

    `capBase M v z t = Lift1 ((0,v,z) :: M.dropLast) t`   （`argOK M`）

で、`Lift1_snoc` により足す 1 列 `q` は **`q.1 = entry M 0 (|M|-1)`、`q.2.2 = c`**
（行 1 だけがリフトで動く）。ここまで込みで書いたのが `CapSnocOpen`。

**`argOK M` が効く形**（一般の `WSnoc` の土台には無い）:

    根（添字 0）の行 0 は `0`、それ以外の列の行 0 は**すべて ≥ 1**、
    足す列 `q` の行 0 も **≥ 1**（`entry M 0 (|M|-1)` は `M` の列だから）。

⟹ **`C ++ [q]` の行 0 の木は根 `0` で連結**（`capBase_row0_root_lt`）。 -/

theorem capBase_entry0_root (M : TrioSeq) (v z t : ℕ) :
    entry (capBase M v z t) 0 0 = 0 := by
  unfold capBase
  rw [entry0_Lift1]
  rfl

theorem capBase_entry0_succ {M : TrioSeq} {v z t j : ℕ} :
    entry (capBase M v z t) 0 (j + 1) = entry M.dropLast 0 j := by
  unfold capBase
  rw [entry0_Lift1]
  show entry (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast) 0 (j + 1) = _
  unfold entry
  simp

/-- `argOK M` は `M.dropLast` に遺伝する。 -/
theorem argOK_dropLast {M : TrioSeq} (h : argOK M) : argOK M.dropLast :=
  fun p hp => h p (List.dropLast_subset M hp)

/-- **★ `argOK` ⟹ 根以外の列の行 0 は正**。 -/
theorem capBase_entry0_pos {M : TrioSeq} (hM : argOK M) {v z t j : ℕ}
    (hj : 0 < j) (hjlt : j < (capBase M v z t).length) :
    0 < entry (capBase M v z t) 0 j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [capBase_entry0_succ]
  rw [capBase_length] at hjlt
  have hk : k < M.dropLast.length := by omega
  have hmem : M.dropLast[k] ∈ M.dropLast := List.getElem_mem hk
  have := argOK_dropLast hM _ hmem
  have hEq : entry M.dropLast 0 k = (M.dropLast[k]).1 := by
    unfold entry
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rfl
  omega

/-- **★ 足す列の行 0 も正**（`M` の最後の列そのものだから）。 -/
theorem cap_col_entry0_pos {M : TrioSeq} (hM : argOK M) (hM2 : 1 ≤ M.length) :
    0 < entry M 0 (M.length - 1) := by
  have hk : M.length - 1 < M.length := by omega
  have hmem : M[M.length - 1] ∈ M := List.getElem_mem hk
  have := hM _ hmem
  have hEq : entry M 0 (M.length - 1) = (M[M.length - 1]).1 := by
    unfold entry
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rfl
  omega

/-- **`CoreCap` の残核（形を保った版）。**
`argOK M` / `z ≤ 1` / `CtxOK M v z` / 足す列の行 0 が `entry M 0 (|M|-1)` /
土台が `Lift1 ((0,v,z) :: M.dropLast) t` —— **形を全部残してある**。 -/
def CapSnocOpen : Prop :=
  ∀ (M : TrioSeq) (v z a t : ℕ), argOK M → 1 ≤ M.length → z ≤ 1 →
    CtxOK M v z → 2 * (v + t) + z ≤ a →
    ∀ q : ℕ × ℕ × ℕ, q.1 = entry M 0 (M.length - 1) →
      hasParent (capBase M v z t ++ [q])
        (srow (capBase M v z t ++ [q]) (capBase M v z t).length)
        (capBase M v z t).length →
      (∃ p ∈ capBase M v z t, 0 < p.2.2) →
      capBase M v z t ++ [q] ∈ W a

/-- **★★★★ `CapSnocOpen` 1 本で `CoreCap`。** -/
theorem coreCap_of_capSnocOpen (h : CapSnocOpen) : CoreCap := by
  intro M hMarg hM2 v z hz1 hctx b c a t hva
  rw [cons_cap_split M v z b c]
  obtain ⟨q, hq, hq0, -⟩ :=
    Lift1_snoc (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast)
      ((entry M 0 (M.length - 1), b, c) : ℕ × ℕ × ℕ) t
  rw [hq]
  show capBase M v z t ++ [q] ∈ W a
  refine snoc_of_open q (capBase_mem hctx hM2 hva) (capBase_ne M v z t) ?_
  intro hpar hz2
  exact h M v z a t hMarg hM2 hz1 hctx hva q hq0 hpar hz2

/-- 位置づけ: `WSnoc` からは当然出る。逆は**言えない**（土台と足す列の形が効くため）。 -/
theorem capSnocOpen_of_wsnoc (hsn : WSnoc) : CapSnocOpen := by
  intro M v z a t _ hM2 _ hctx hva q _ hpar _
  exact hsn a (capBase M v z t) q (capBase_mem hctx hM2 hva) (capBase_ne M v z t) hpar


/-! ## 10. ★★★ `argOK` の payoff —— **根は行 0 で全列の祖先**

`Wset.le0_cons_zero`（`Wset.lean:1907`、**既存・証明ずみ**）:

    `argOK R → ∀ j < |R|, le0 ((0,v,z) :: R) 0 (j+1)`

`Lift1` は行 0 も長さも変えない（`entry0_Lift1` / `Lift1_length`）ので、
`le0` はリフトを透かす（`le0_Lift1`）。⟹ **`CoreCap` の `C ++ [q]` では
根が全列（`q` 自身も含む）の行 0 祖先**である。

これは一般の `WSnoc` の土台には**無い**情報で、次の 2 つに効く:

1. 展開の親 `j0 = 0`（根）のとき、行 0 の増分 `k * d0` は
   **`le0 (C++[q]) 0 j` が全 `j` で成り立つので窓全体に一様**にかかる
   ⟹ その写しは「`C` を行 0 で一様シフトし、行 1 を根の錐でリフトしたもの」＝ **塔**。
2. `W_flatMap_copies`（`Wset.lean:2552`、証明ずみ）の側条件
   `∀ p ∈ Q, entry Q 0 0 ≤ p.1` は `j0 = 0` のとき **`entry C 0 0 = 0` から自明**。
   ⟹ **`j0 = 0` かつ `srow = 0` の枝は `PrefixCopies` すら要らない。** -/

theorem nextrel0_Lift1 {X : TrioSeq} {d a b : ℕ} :
    nextrel0 (Lift1 X d) a b ↔ nextrel0 X a b := by
  unfold nextrel0
  simp only [Lift1_length, entry0_Lift1]

/-- **`le0` は `Lift1` を透かす**（行 0 も長さも変わらないため）。 -/
theorem le0_Lift1 {X : TrioSeq} {d a b : ℕ} :
    le0 (Lift1 X d) a b ↔ le0 X a b := by
  unfold le0
  simp only [Lift1_length]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, Relation.ReflTransGen.mono (fun _ _ h => nextrel0_Lift1.mp h) h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, Relation.ReflTransGen.mono (fun _ _ h => nextrel0_Lift1.mpr h) h3⟩

theorem cap_length (M : TrioSeq) (b c : ℕ) :
    (cap M b c).length = M.dropLast.length + 1 := by
  unfold cap; simp

/-- `argOK` は `cap` に遺伝する（差し替わるのは行 1・行 2 だけだから）。 -/
theorem argOK_cap {M : TrioSeq} (hM : argOK M) (hM2 : 1 ≤ M.length) (b c : ℕ) :
    argOK (cap M b c) := by
  intro p hp
  unfold cap at hp
  rcases List.mem_append.mp hp with h | h
  · exact argOK_dropLast hM p h
  · rw [List.mem_singleton] at h
    subst h
    exact cap_col_entry0_pos hM hM2

/-- **★★★ `CoreCap` の snoc の道具立て一式。**
土台・足す列の行 0 と行 2・そして**根が行 0 で全列の祖先**であること。 -/
theorem cap_snoc_setup {M : TrioSeq} (hM : argOK M) (hM2 : 1 ≤ M.length)
    (v z t b c : ℕ) :
    ∃ q : ℕ × ℕ × ℕ,
      Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: cap M b c) t = capBase M v z t ++ [q]
      ∧ q.1 = entry M 0 (M.length - 1) ∧ q.2.2 = c
      ∧ ∀ j, j < (capBase M v z t ++ [q]).length →
          le0 (capBase M v z t ++ [q]) 0 j := by
  obtain ⟨q, hq, hq0, hq2⟩ :=
    Lift1_snoc (((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast)
      ((entry M 0 (M.length - 1), b, c) : ℕ × ℕ × ℕ) t
  have hsplit : (((0, v, z) : ℕ × ℕ × ℕ) :: cap M b c)
      = ((((0, v, z) : ℕ × ℕ × ℕ) :: M.dropLast)
          ++ [((entry M 0 (M.length - 1), b, c) : ℕ × ℕ × ℕ)]) :=
    cons_cap_split M v z b c
  have hEq : Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: cap M b c) t
      = capBase M v z t ++ [q] := by rw [hsplit]; exact hq
  refine ⟨q, hEq, hq0, hq2, ?_⟩
  intro j hj
  rw [← hEq]
  rw [← hEq] at hj
  rw [Lift1_length, List.length_cons, cap_length] at hj
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · exact ⟨by rw [Lift1_length]; simp, by rw [Lift1_length]; simp,
      Relation.ReflTransGen.refl⟩
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [le0_Lift1]
    exact le0_cons_zero (argOK_cap hM hM2 b c) k (by rw [cap_length]; omega)

/-! ## 11. ★★★★ 残核の最終形 `CapSnocOpen'`（根の行 0 祖先性つき）

`cap_snoc_setup` が根の祖先性を無料で供給するので、残核はさらに 1 前提ぶん弱くできる。
**この前提は `C ∈ W a` からは出ない**（`W_take` のときと違い、`argOK M` 由来）。 -/

def CapSnocOpen' : Prop :=
  ∀ (M : TrioSeq) (v z a t : ℕ), argOK M → 1 ≤ M.length → z ≤ 1 →
    CtxOK M v z → 2 * (v + t) + z ≤ a →
    ∀ q : ℕ × ℕ × ℕ, q.1 = entry M 0 (M.length - 1) →
      (∀ j, j < (capBase M v z t ++ [q]).length →
        le0 (capBase M v z t ++ [q]) 0 j) →
      hasParent (capBase M v z t ++ [q])
        (srow (capBase M v z t ++ [q]) (capBase M v z t).length)
        (capBase M v z t).length →
      (∃ p ∈ capBase M v z t, 0 < p.2.2) →
      capBase M v z t ++ [q] ∈ W a

/-- **★★★★★ `CapSnocOpen'` 1 本で `CoreCap`。**（この file の到達点。） -/
theorem coreCap_of_capSnocOpen' (h : CapSnocOpen') : CoreCap := by
  intro M hMarg hM2 v z hz1 hctx b c a t hva
  obtain ⟨q, hEq, hq0, -, hle0⟩ := cap_snoc_setup hMarg hM2 v z t b c
  rw [hEq]
  refine snoc_of_open q (capBase_mem hctx hM2 hva) (capBase_ne M v z t) ?_
  intro hpar hz2
  exact h M v z a t hMarg hM2 hz1 hctx hva q hq0 hle0 hpar hz2

theorem capSnocOpen'_of_capSnocOpen (h : CapSnocOpen) : CapSnocOpen' := by
  intro M v z a t hM hM2 hz1 hctx hva q hq0 _ hpar hz2
  exact h M v z a t hM hM2 hz1 hctx hva q hq0 hpar hz2



/-! ## 13. ★★★★★ **厳密な残核** `CapSnocOpenExact`（`CoreCap` と同値）

⚠ `CapSnocOpen'` は `q` を自由に走らせているので、**`cap` のリフトから作れない `q`
（例えば `q.2.1 < t` のもの）まで含む** ⟹ `CoreCap` より強いかもしれない。
`q` の出自の等式を前提に入れると、**`CoreCap` とちょうど同値**になる。 -/

def CapSnocOpenExact : Prop :=
  ∀ (M : TrioSeq) (v z a t b c : ℕ), argOK M → 1 ≤ M.length → z ≤ 1 →
    CtxOK M v z → 2 * (v + t) + z ≤ a →
    ∀ q : ℕ × ℕ × ℕ,
      Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: cap M b c) t = capBase M v z t ++ [q] →
      (∀ j, j < (capBase M v z t ++ [q]).length →
        le0 (capBase M v z t ++ [q]) 0 j) →
      hasParent (capBase M v z t ++ [q])
        (srow (capBase M v z t ++ [q]) (capBase M v z t).length)
        (capBase M v z t).length →
      (∃ p ∈ capBase M v z t, 0 < p.2.2) →
      capBase M v z t ++ [q] ∈ W a

theorem coreCap_of_capSnocOpenExact (h : CapSnocOpenExact) : CoreCap := by
  intro M hMarg hM2 v z hz1 hctx b c a t hva
  obtain ⟨q, hEq, -, -, hle0⟩ := cap_snoc_setup hMarg hM2 v z t b c
  rw [hEq]
  refine snoc_of_open q (capBase_mem hctx hM2 hva) (capBase_ne M v z t) ?_
  intro hpar hz2
  exact h M v z a t b c hMarg hM2 hz1 hctx hva q hEq hle0 hpar hz2

theorem capSnocOpenExact_of_coreCap (h : CoreCap) : CapSnocOpenExact := by
  intro M v z a t b c hMarg hM2 hz1 hctx hva q hEq _ _ _
  rw [← hEq]
  exact h M hMarg hM2 v z hz1 hctx b c a t hva

/-- **★★★★★ `CapSnocOpenExact` は `CoreCap` と同値** —— 「無料の枝を全部落として、
`argOK` 由来の根祖先性を与件に加えた `CoreCap`」がこれ。 -/
theorem capSnocOpenExact_iff_coreCap : CapSnocOpenExact ↔ CoreCap :=
  ⟨coreCap_of_capSnocOpenExact, capSnocOpenExact_of_coreCap⟩

theorem capSnocOpenExact_of_capSnocOpen' (h : CapSnocOpen') : CapSnocOpenExact := by
  intro M v z a t b c hMarg hM2 hz1 hctx hva q hEq hle0 hpar hz2
  obtain ⟨q', hEq', hq0', -, -⟩ := cap_snoc_setup hMarg hM2 v z t b c
  have hqq : q' = q := by
    have hcat : capBase M v z t ++ [q'] = capBase M v z t ++ [q] := hEq'.symm.trans hEq
    simpa using List.append_cancel_left hcat
  rw [hqq] at hq0'
  exact h M v z a t hMarg hM2 hz1 hctx hva q hq0' hle0 hpar hz2


/-! ## 14. ★★★★★ 課題 L106 への回答

### 14.1 ⚠ (1)(2) について: **`CtxOK` の `∀ k`（接頭辞の鎖）は逃げ道にならない**

§131 の課題 L106 は「土台が接頭辞の鎖を持つときだけの snoc」を新しい核として
立てる案だったが、**その鎖は `Wset.W_take`（`Wset.lean:2120`）で無料**である。
§8 の `wsnoc_of_snocPrefixOpen`（緑）がその証明:

    `SnocPrefixOpen`（土台の全接頭辞が `W u`）**⟹ `WSnoc`**

⟹ 接頭辞版は `WSnoc` と同値で、`wcat_of_snoc` を止められない。**この案は死ぬ。**

### 14.2 ⟹ 生きているのは `∀ t`（リフト族）と**主語の形**の 2 つ

    `CtxOK` の `∀ t` … `LiftStage` を接頭辞に限ったもの。**無料ではない**（§12.4）
    主語の形       … 土台は `Lift1 ((0,v,z) :: R) t`（`argOK R`, `z ≤ 1`）。
                     一般の `C ∈ W u` はこの形をしていない

`wcat_of_snoc`（`Wtower2.lean:2078`）は**任意の `A ++ B` の接頭辞**に 1 列 snoc する
必要があるので、この 2 つのどちらでも止まる。⟹ **`CapSnocOpenExact` から `WCat` は
出ない**（証明ではなく、`wcat_of_snoc` の適用が構文的に不可能という観察）。

### 14.3 ★ (3) について: **`PrefixCopies` は `W_add` では原理的に出ない**（算術で確定）

`srow = 0` の枝の展開は `C.take j0 ++ (C.drop j0 の n 個の写し)`（`oper_snoc_srow0`）。

    `j0 = 0` … 接頭辞が空。**`W_flatMap_copies`（`Wset.lean:2552`、証明ずみ）が
                そのまま当たる**。側条件 `∀ p ∈ Q, entry Q 0 0 ≤ p.1` は
                `entry C 0 0 = 0` から自明 ⟹ **無料**
    `j0 ≥ 1` … 接頭辞 `C.take j0` は**根（行 0 = 0）を含む**。一方 `C.drop j0` は
                `argOK` なので `entry (C.drop j0) 0 0 ≥ 1`。
                ⟹ `rsum (C.take j0) (C.drop j0)` は `1 ≤ 0` を要求して**必ず破れる**

**これは §131 の塔の算術（`n*e ≤ 0`）と同じ形の、2 本目の `rsum` 破れである。**
違いは、あちらが「写しが深くなる」ことで破れるのに対し、こちらは
**`argOK` が根を唯一の行 0 = 0 の列にしている**ことで破れる点。

⟹ **`PrefixCopies` は `W_add` 経由では出ない。**
⚠ ただし「`Aop` の節 3 が唯一の道」と書くのは**誤り**（§16 参照）。
残核そのものは `hasParent` を仮定しているので **節 3 は使えない**。
節 3 が使えるのは、節 2 で降りた**展開先**である。

以下がその Lean での確定（`Wset.not_rsum_cons_root` の一般化）。 -/

/-- **根（行 0 = 0）を含む接頭辞に `argOK` のブロックは `rsum` で足せない。** -/
theorem not_rsum_of_root_mem {A B : TrioSeq} (hB : argOK B) (hBne : B ≠ [])
    (hroot : ∃ p ∈ A, p.1 = 0) : ¬ rsum A B := by
  intro h
  obtain ⟨p, hpA, hp0⟩ := hroot
  have h1 := h p (List.mem_append.mpr (Or.inl hpA))
  cases B with
  | nil => exact hBne rfl
  | cons q tl =>
      have hq : 0 < q.1 := hB q (by simp)
      have hE : entry (q :: tl) 0 0 = q.1 := by simp [entry]
      rw [hE, hp0] at h1
      omega

theorem argOK_capBase_drop {M : TrioSeq} (hM : argOK M) {v z t j0 : ℕ}
    (hj0 : 1 ≤ j0) : argOK ((capBase M v z t).drop j0) := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  rw [List.length_drop] at hi
  have hlt : j0 + i < (capBase M v z t).length := by omega
  have hget : ((capBase M v z t).drop j0)[i]'(by rw [List.length_drop]; omega)
      = (capBase M v z t)[j0 + i]'hlt := by rw [List.getElem_drop]
  rw [hget, ← entry_triple hlt]
  exact capBase_entry0_pos hM (by omega) hlt

theorem capBase_root_mem_take {M : TrioSeq} {v z t j0 : ℕ} (hj0 : 1 ≤ j0) :
    ∃ p ∈ (capBase M v z t).take j0, p.1 = 0 := by
  have hlen : 0 < (capBase M v z t).length := by rw [capBase_length]; omega
  have h0 : 0 < ((capBase M v z t).take j0).length := by
    rw [List.length_take]; omega
  refine ⟨((capBase M v z t).take j0)[0], List.getElem_mem h0, ?_⟩
  have hget : ((capBase M v z t).take j0)[0] = (capBase M v z t)[0]'hlen := by
    rw [List.getElem_take]
  rw [hget, ← entry_triple hlen]
  exact capBase_entry0_root M v z t

/-- **★★★★★ `j0 ≥ 1` では `W_add` の側条件が必ず破れる。**
⟹ `CoreCap` の `srow = 0` 枝（と、そもそも接頭辞つきコピー全般）は
**連結（`W_add` / `rsum`）では絶対に組めない**。節 3（`graft`）だけが残る。 -/
theorem not_rsum_capBase_split {M : TrioSeq} (hM : argOK M) {v z t j0 : ℕ}
    (hj0 : 1 ≤ j0) (hj0lt : j0 < (capBase M v z t).length) :
    ¬ rsum ((capBase M v z t).take j0) ((capBase M v z t).drop j0) := by
  refine not_rsum_of_root_mem (argOK_capBase_drop hM hj0) ?_ (capBase_root_mem_take hj0)
  intro hnil
  have hl : ((capBase M v z t).drop j0).length = 0 := by rw [hnil]; rfl
  rw [List.length_drop] at hl
  omega


/-! ### 14.4 ★ §131 の「塔は `W_add` で組めない」の Lean 版

team-lead が §131 で算術で確定した

    `shTower Q e (n+1) = shTower Q e n ++ shiftr01 (n*e) 0 Q`（`Wtower2.lean:1976`）
    `rsum A B := ∀ p ∈ A ++ B, entry B 0 0 ≤ p.1`（`Wset.lean:1317`）
    `A` は `k=0` の塊として `Q` を含む ⟹ 根（行 0 = 0）を含む
    `entry B 0 0 = entry Q 0 0 + n*e = n*e ≥ 1`
    ⟹ 側条件は `1 ≤ 0` を要求して破れる

を、`not_rsum_of_root_mem` の 1 行の系として Lean に落とす。
**`j0 = 0`（根が親）の `CoreCap` の展開もこの形**（`d0 = q.1 ≥ 1` は `argOK` から、
`C` が基づくのは根が `(0, v+t, z)` だから）なので、**`j0 = 0` でも `W_add` は死ぬ**。
⟹ **`CoreCap` の残核は `j0` の値によらず、連結では絶対に組めない。**
残るのは `Aop` の節 3（`graft`）だけ（§132 の教訓 23 どおり、路線は死なない）。 -/

theorem not_rsum_shTower {Q : TrioSeq} (hQne : Q ≠ []) (hb : based Q)
    {e n : ℕ} (he : 1 ≤ e) (hn : 1 ≤ n) :
    ¬ rsum (shTower Q e n) (shiftr01 (n * e) 0 Q) := by
  have hQlen : 0 < Q.length := List.length_pos_iff.mpr hQne
  have hne : 0 < n * e := Nat.mul_pos hn he
  refine not_rsum_of_root_mem ?_ ?_ ?_
  · intro p hp
    simp only [shiftr01, List.mem_map] at hp
    obtain ⟨r, -, rfl⟩ := hp
    simp only []
    omega
  · intro hnil
    have hl : (shiftr01 (n * e) 0 Q).length = 0 := by rw [hnil]; rfl
    simp only [shiftr01, List.length_map] at hl
    omega
  · refine ⟨Q[0], ?_, ?_⟩
    · refine List.mem_flatMap.mpr ⟨0, List.mem_range.mpr hn, ?_⟩
      simp
    · rw [← entry_triple hQlen]
      exact hb

/-- `capBase` は基づく（根は `(0, v+t, z)`）。⟹ 上の系がそのまま当たる。 -/
theorem based_capBase (M : TrioSeq) (v z t : ℕ) : based (capBase M v z t) :=
  capBase_entry0_root M v z t


/-! ## 15. ★★★★★ `CtxOK` の `∀ t` の正体 —— **土台についての `LiftStage` そのもの**

`Wset.Lift1_Lift1`（`Wset.lean:1230`）`Lift1 (Lift1 X t) s = Lift1 X (t+s)` により

    `Lift1 (capBase M v z t) e = capBase M v z (t + e)`

なので、`CtxOK` の `∀ t` の項はそのまま

    **`Lift1 (capBase M v z t) e ∈ W a`（`2(v+t+e)+z ≤ a`）**

を与える。これは `LiftStage`（`Wtower2.lean:36`、`X ∈ W m → Lift1 X d ∈ W (m+2d)`）の
**`X = capBase`、`m = 2(v+t)+z` の場合そのもの**（段の伸びも `+2e` で一致）。

⟹ **`CoreCap` の残核では `LiftStage` は土台について「すでに成り立っている」。**
塔の第 `k` 写しが要求する行 1 のリフト `k*d1` は、これで `W (a + 2k*d1)` に入る。
**残っているのは段の帳尻**（`a + 2k d1` の族を段 `a` の 1 本にまとめること）だけで、
それは §14 のとおり `W_add`（連結）では**絶対に**できない。
⟹ 使えるのは `Aop` の**節 2 だけ**（§16）。 -/

theorem capBase_Lift1 (M : TrioSeq) (v z t e : ℕ) :
    Lift1 (capBase M v z t) e = capBase M v z (t + e) := by
  unfold capBase
  rw [Lift1_Lift1]

/-- **★★★★★ `CtxOK` は土台についての `LiftStage` を無料で配っている。** -/
theorem liftStage_capBase {M : TrioSeq} {v z t e a : ℕ} (hctx : CtxOK M v z)
    (hM2 : 1 ≤ M.length) (hva : 2 * (v + (t + e)) + z ≤ a) :
    Lift1 (capBase M v z t) e ∈ W a := by
  rw [capBase_Lift1]
  exact capBase_mem hctx hM2 hva

/-- 同じことを `LiftStage` の段の形で述べたもの（`m = 2(v+t)+z` のとき一致）。 -/
theorem liftStage_capBase' {M : TrioSeq} {v z t e : ℕ} (hctx : CtxOK M v z)
    (hM2 : 1 ≤ M.length) :
    Lift1 (capBase M v z t) e ∈ W ((2 * (v + t) + z) + 2 * e) :=
  liftStage_capBase hctx hM2 (by omega)


/-! ## 16. ★★★★★ 残核では `Aop` の**節 2 しか生きていない**

`Aop`（`Wset.lean:171`）の 3 節を残核の主語 `S := capBase ++ [q]` で潰す:

    節 1 `|S| ≤ 1 ∧ lev S 0 = 0`  … `|S| = |M| + 1 ≥ 2` ⟹ **死** 
    節 3 `∃ m < a, domT S m ∧ …`  … `domT S m` は
        **`¬ hasParent S (srow S (|S|-1)) (|S|-1)`** を含む（`Wset.lean:61`）。
        残核は `hasParent` を**仮定**しているので ⟹ **死**（`not_domT_of_hasParent`）
    節 2 `∀ n ≥ 1, S⟦n⟧ ∈ W a`    … **これだけが生きている**

⟹ **残核 `CapSnocOpenExact` は「すべての展開が `W a` にいる」に等しい**
（`mem_of_oper_mem` / `mem_iff_oper_mem`、`Wchar.lean:73`/`:75`）。
そして展開は `C.take j0 ++ 塔` で、§14 によりその**連結は `W_add` では組めない**。

⟹ **道は 1 本しかない: 展開先 `S⟦n⟧` に対して `Aop` の節 3（`domT` ＋ graft 閉包）が
使えるかを見る。** `S⟦n⟧` の末尾列が孤児かどうかが決め手。

⚠ §14.3 の初稿で「節 3 が唯一の道」と書いたのは**主語を取り違えた誤り**。
節 3 が使えるのは `S` ではなく `S⟦n⟧` である。 -/

/-- **親を持つ列は `domT` を満たさない** ⟹ 残核では `Aop` の節 3 が使えない。 -/
theorem not_domT_of_hasParent {M : TrioSeq} {m : ℕ}
    (h : hasParent M (srow M (M.length - 1)) (M.length - 1)) : ¬ domT M m :=
  fun hd => hd.2 h

/-- 残核の主語での具体化。 -/
theorem not_domT_capBase_snoc {M : TrioSeq} {v z t : ℕ} {q : ℕ × ℕ × ℕ}
    (h : hasParent (capBase M v z t ++ [q])
      (srow (capBase M v z t ++ [q]) (capBase M v z t).length)
      (capBase M v z t).length) (m : ℕ) :
    ¬ domT (capBase M v z t ++ [q]) m := by
  refine not_domT_of_hasParent ?_
  have hlen : (capBase M v z t ++ [q]).length - 1 = (capBase M v z t).length := by
    simp
  rw [hlen]
  exact h

/-- 節 1 も死んでいる（長さ ≥ 2）。 -/
theorem capBase_snoc_len (M : TrioSeq) (v z t : ℕ)
    (q : ℕ × ℕ × ℕ) : 2 ≤ (capBase M v z t ++ [q]).length := by
  rw [List.length_append, capBase_length]
  simp


/-! ### 16.1 ⟹ 残核の**最終形**: 「展開が全部 `W a` にいる」

節 2 しか無いので、残核は `mem_iff_oper_mem`（`Wchar.lean:75`）でそのまま
展開の言葉に書き換えられる。**次のエージェントが攻めるべき対象はこれ。** -/

def CapExpOpen : Prop :=
  ∀ (M : TrioSeq) (v z a t b c : ℕ), argOK M → 1 ≤ M.length → z ≤ 1 →
    CtxOK M v z → 2 * (v + t) + z ≤ a →
    ∀ q : ℕ × ℕ × ℕ,
      Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: cap M b c) t = capBase M v z t ++ [q] →
      (∀ j, j < (capBase M v z t ++ [q]).length →
        le0 (capBase M v z t ++ [q]) 0 j) →
      hasParent (capBase M v z t ++ [q])
        (srow (capBase M v z t ++ [q]) (capBase M v z t).length)
        (capBase M v z t).length →
      (∃ p ∈ capBase M v z t, 0 < p.2.2) →
      ∀ n, 1 ≤ n → (capBase M v z t ++ [q])⟦n⟧ ∈ W a

theorem capSnocOpenExact_of_capExpOpen (h : CapExpOpen) : CapSnocOpenExact := by
  intro M v z a t b c hM hM2 hz1 hctx hva q hEq hle0 hpar hz2
  exact mem_of_oper_mem (h M v z a t b c hM hM2 hz1 hctx hva q hEq hle0 hpar hz2)

theorem capExpOpen_of_coreCap (h : CoreCap) : CapExpOpen := by
  intro M v z a t b c hM hM2 hz1 hctx hva q hEq _ _ _
  refine oper_mem_of_mem (capBase_snoc_len M v z t q) ?_
  rw [← hEq]
  exact h M hM hM2 v z hz1 hctx b c a t hva

/-- **★★★★★ 三者は同値**: `CoreCap` ⟺ `CapSnocOpenExact` ⟺ `CapExpOpen`。 -/
theorem capExpOpen_iff_coreCap : CapExpOpen ↔ CoreCap :=
  ⟨fun h => coreCap_of_capSnocOpenExact (capSnocOpenExact_of_capExpOpen h),
   capExpOpen_of_coreCap⟩


/-! ## 17. ★★★★★ 課題 L107: **`srow` を決めているのは `(b, c)` そのもの**

`srow` は末尾列の成分だけで決まる（`Trio.lean:81`）。cap 列の行 1 は `b`（＋リフト）、
行 2 は `c` なので、**`∀ b c` はまさに `srow` の枝を生成している**。仮説は正しい。 -/

theorem srow_snoc_last (C : TrioSeq) (q : ℕ × ℕ × ℕ) :
    srow (C ++ [q]) C.length
      = (if 0 < q.2.2 then 2 else if 0 < q.2.1 then 1 else 0) := by
  unfold srow
  rw [entry_snoc_last C q 2, entry_snoc_last C q 1]
  rfl

/-- `Lift1` が動かすのは足す列の**行 1 だけ**で、動く幅は `[0, d]`。 -/
theorem Lift1_snoc_row1 {C : TrioSeq} {p q : ℕ × ℕ × ℕ} {d : ℕ}
    (heq : Lift1 (C ++ [p]) d = Lift1 C d ++ [q]) :
    p.2.1 ≤ q.2.1 ∧ q.2.1 ≤ p.2.1 + d := by
  have hlt : C.length < (C ++ [p]).length := by simp
  have hA : entry (Lift1 (C ++ [p]) d) 1 C.length
      = p.2.1 + (if le1 (C ++ [p]) 0 C.length then d else 0) := by
    rw [entry1_Lift1 hlt]
    congr 1
    simpa using entry_snoc_last C p 1
  have hB : entry (Lift1 C d ++ [q]) 1 C.length = q.2.1 := by
    have h := entry_snoc_last (Lift1 C d) q 1
    rw [Lift1_length] at h
    simpa using h
  rw [heq, hB] at hA
  by_cases hc : le1 (C ++ [p]) 0 C.length <;> simp [hc] at hA <;> omega

/-- **★★★ `srow = 2 ⟺ `c ≥ 1`。** cap の行 2 が枝をそのまま決める。 -/
theorem srow_cap_eq_two_iff {C : TrioSeq} {q : ℕ × ℕ × ℕ} {c : ℕ}
    (hq2 : q.2.2 = c) :
    srow (C ++ [q]) C.length = 2 ↔ 0 < c := by
  rw [srow_snoc_last, hq2]
  by_cases h : 0 < c
  · simp [h]
  · by_cases h1 : 0 < q.2.1 <;> simp [h, h1]

/-- **★★★ `srow = 0` なら `b = 0` かつ `c = 0`。**（対偶: `(b,c) ≠ (0,0)` が
`srow ≥ 1` を生む。リフト `t` は行 1 を**増やす**方向にしか動かさない。） -/
theorem srow_cap_eq_zero {C : TrioSeq} {p q : ℕ × ℕ × ℕ} {d : ℕ}
    (heq : Lift1 (C ++ [p]) d = Lift1 C d ++ [q]) (hq2 : q.2.2 = p.2.2)
    (h0 : srow (C ++ [q]) C.length = 0) : p.2.1 = 0 ∧ p.2.2 = 0 := by
  rw [srow_snoc_last] at h0
  obtain ⟨hlo, -⟩ := Lift1_snoc_row1 heq
  by_cases hc : 0 < q.2.2
  · simp [hc] at h0
  · by_cases hb : 0 < q.2.1
    · simp [hc, hb] at h0
    · omega

/-! ### 17.1 ⚠ **`c ≤ 1` では `srow = 2` は消えない**（team-lead の期待への回答）

`srow_cap_eq_two_iff` は **`0 < c`** が `srow = 2` の**必要十分**だと言っている。
断片は行 2 ≤ 1 なので `c ∈ {0, 1}` だが、**`c = 1` はちゃんと `srow = 2` を出す。**

⟹ **`c ≤ 1` に制限しても枝は 1 本も減らない。減らせるのは `c = 0` に制限したときだけで、
それは cap の行 2 を殺すこと ＝ `CoreSingleton` の `[(0,b,0)]` しか出さないこと**であり、
`Lind.mem_GX_of_singletons` の基底（`based y` の 1 列は `(0,b,c)` の**任意の** `c`）を
満たさない。**⟹ `srow = 2` の枝は落とせない。**

### 17.2 ★ `srow = 2` は**起きる**。しかも本線で起きる

以下は残核の `srow = 2` の枝の**構文的な証人**（`CtxOK` 以外の前提はすべて Lean で証明）。

    `Mw := [(1,1,1),(2,0,0)]`  … `argOK`、`|Mw| = 2`、`entry Mw 0 1 = 2`
    `v = z = t = 0`, `b = c = 1`
    土台 `capBase Mw 0 0 0 = [(0,0,0),(1,1,1)]`  ＝ **`ψ(Ω_ω)`（2 行 BMS の極限）**
    主語 `Sw = [(0,0,0),(1,1,1),(2,1,1)]`        ＝ **`D_1` の 1 つ上、`D_2` の 1 つ下**

**`Sw` は `L51Lift.lean` の `Mt` と同じ行列**（課題 L51 で既に解析ずみ:
`srow_Mt` / `hasParent_Mt` / `parent_Mt = 0` / `oper_Mt`）。

⟹ **`srow = 2` の枝は隅の場合ではなく、`(0,0,0)(1,1,1)` に 3 行目を足す
＝ 2 行 BMS から 3 行 BMS に出る、その一歩そのもの。**
これが「なぜ 3 行が 2 行より難しいか」の 3 本目である。 -/

def Mw : TrioSeq := [(1, 1, 1), (2, 0, 0)]

def Sw : TrioSeq := [(0, 0, 0), (1, 1, 1), (2, 1, 1)]

theorem argOK_Mw : argOK Mw := by
  intro p hp
  have hp' : p = ((1, 1, 1) : ℕ × ℕ × ℕ) ∨ p = ((2, 0, 0) : ℕ × ℕ × ℕ) := by
    simpa [Mw] using hp
  rcases hp' with rfl | rfl
  · show 0 < 1; omega
  · show 0 < 2; omega

theorem Mw_len : 1 ≤ Mw.length := by simp [Mw]

theorem capBase_Mw : capBase Mw 0 0 0 = [((0, 0, 0) : ℕ × ℕ × ℕ), (1, 1, 1)] := by
  unfold capBase
  rw [Lift1_zero]
  rfl

theorem cap_Mw : Lift1 (((0, 0, 0) : ℕ × ℕ × ℕ) :: cap Mw 1 1) 0 = Sw := by
  rw [Lift1_zero]
  rfl

theorem Sw_split : Sw = capBase Mw 0 0 0 ++ [((2, 1, 1) : ℕ × ℕ × ℕ)] := by
  rw [capBase_Mw]
  rfl

theorem srow_Sw : srow Sw 2 = 2 := by simp [srow, entry, Sw]

theorem row2_pos_capBase_Mw : ∃ p ∈ capBase Mw 0 0 0, 0 < p.2.2 := by
  rw [capBase_Mw]
  refine ⟨((1, 1, 1) : ℕ × ℕ × ℕ), by simp, ?_⟩
  show 0 < 1
  omega


/-! ### 17.3 証人の `hasParent`（`L51Lift.lean` の `Mt` と同じ手順） -/

theorem le0_le' {M : TrioSeq} {a b : ℕ} (h : le0 M a b) : a ≤ b := rtg0_le h.2.2

theorem le1_le' {M : TrioSeq} {a b : ℕ} (h : le1 M a b) : a ≤ b := rtg1_le h.2.2

theorem nextrel0_Sw_01 : nextrel0 Sw 0 1 := by
  refine ⟨by simp [Sw], by simp [Sw], by omega, by simp [entry, Sw], ?_⟩
  intro j hj
  omega

theorem nextrel0_Sw_12 : nextrel0 Sw 1 2 := by
  refine ⟨by simp [Sw], by simp [Sw], by omega, by simp [entry, Sw], ?_⟩
  intro j hj
  omega

theorem le0_Sw_02 : le0 Sw 0 2 :=
  ⟨by simp [Sw], by simp [Sw],
    (Relation.ReflTransGen.single nextrel0_Sw_01).tail nextrel0_Sw_12⟩

theorem nextrel1_Sw_02 : nextrel1 Sw 0 2 := by
  refine ⟨by simp [Sw], by simp [Sw], by omega, by simp [entry, Sw], le0_Sw_02, ?_⟩
  intro j hj
  obtain ⟨hj1, hj2⟩ := hj
  have h1 : j ≤ 2 := le0_le' hj2
  rcases j with _ | _ | _ | j
  · omega
  · simp [entry, Sw]
  · simp [entry, Sw]
  · omega

theorem le1_Sw_02 : le1 Sw 0 2 :=
  ⟨by simp [Sw], by simp [Sw], Relation.ReflTransGen.single nextrel1_Sw_02⟩

theorem nextrel2_Sw_02 : nextrel2 Sw 0 2 := by
  refine ⟨by simp [Sw], by simp [Sw], by omega, by simp [entry, Sw], le1_Sw_02, ?_⟩
  intro j hj
  obtain ⟨hj1, hj2⟩ := hj
  have h1 : j ≤ 2 := le1_le' hj2
  rcases j with _ | _ | _ | j
  · omega
  · simp [entry, Sw]
  · simp [entry, Sw]
  · omega

theorem nextrel2_Sw_unique {j : ℕ} (h : nextrel2 Sw j 2) : j = 0 := by
  obtain ⟨-, -, hj2, hlt, -, -⟩ := h
  rcases j with _ | _ | _ | j
  · rfl
  · simp [entry, Sw] at hlt
  · omega
  · omega

theorem nextR_Sw_02 : nextR Sw 2 0 2 := by
  rw [nextR]
  simp only [if_neg (by omega : (2 : ℕ) ≠ 0), if_neg (by omega : (2 : ℕ) ≠ 1)]
  exact nextrel2_Sw_02

theorem hasParent_Sw : hasParent Sw 2 2 := by
  refine ⟨0, nextR_Sw_02, ?_⟩
  intro y hy
  rw [nextR] at hy
  simp only [if_neg (by omega : (2 : ℕ) ≠ 0), if_neg (by omega : (2 : ℕ) ≠ 1)] at hy
  exact nextrel2_Sw_unique hy

theorem capBase_Mw_len : (capBase Mw 0 0 0).length = 2 := by
  rw [capBase_Mw]; rfl

/-- **★★★★★ 残核の `srow = 2` の枝は空ではない。**
`CtxOK Mw 0 0` 以外の前提はすべてここで証明されている。
主語は `(0,0,0)(1,1,1)(2,1,1)`、土台は `(0,0,0)(1,1,1) = ψ(Ω_ω)`
—— **2 行 BMS の極限に 3 行目を足す一歩そのもの**。 -/
theorem srow2_branch_live :
    argOK Mw ∧ 1 ≤ Mw.length ∧
    Lift1 (((0, 0, 0) : ℕ × ℕ × ℕ) :: cap Mw 1 1) 0
      = capBase Mw 0 0 0 ++ [((2, 1, 1) : ℕ × ℕ × ℕ)] ∧
    srow (capBase Mw 0 0 0 ++ [((2, 1, 1) : ℕ × ℕ × ℕ)])
      (capBase Mw 0 0 0).length = 2 ∧
    hasParent (capBase Mw 0 0 0 ++ [((2, 1, 1) : ℕ × ℕ × ℕ)])
      (srow (capBase Mw 0 0 0 ++ [((2, 1, 1) : ℕ × ℕ × ℕ)])
        (capBase Mw 0 0 0).length) (capBase Mw 0 0 0).length ∧
    (∃ p ∈ capBase Mw 0 0 0, 0 < p.2.2) := by
  have hsplit : capBase Mw 0 0 0 ++ [((2, 1, 1) : ℕ × ℕ × ℕ)] = Sw := Sw_split.symm
  refine ⟨argOK_Mw, Mw_len, ?_, ?_, ?_, row2_pos_capBase_Mw⟩
  · rw [hsplit]; exact cap_Mw
  · rw [hsplit, capBase_Mw_len]; exact srow_Sw
  · rw [hsplit, capBase_Mw_len, srow_Sw]; exact hasParent_Sw


/-! ## 18. ★★★★★ 課題 L107 (3): `CtxOK` の `∀ t` を `srow ≥ 1` の写しに噛ませる

`j0 = 0`（親が根）のとき、`oper` の写しは §10 の根祖先性により

    第 `k` 写し = `shiftr01 (k*d0) 0 (Lift1 C (k*d1))`

（行 0 は `le0 (C++[q]) 0 j` が全 `j` で成り立つので**一様**、行 1 は根の `le1` 錐＝`Lift1`）。
そして `CtxOK` の `∀ t` は `Lift1 C (k*d1) = capBase M v z (t + k*d1)` を
`W (2(v+t+k d1)+z)` に入れてくれる（§15）。`W_shift`（`Wset.lean:265` 付近、
**行 0 のシフトは段を変えない**）で行 0 のずれも吸収される。

⟹ **写しは 1 つ 1 つ、`CtxOK` から無料で `W` に入る。**
残っているのは**段の帳尻だけ**（`W (a + 2k d1)` の族を段 `a` の 1 本にまとめる）で、
それは §14 のとおり連結では絶対にできない。 -/

/-- **★★★★ `j0 = 0` の第 `k` 写しは `CtxOK` から無料。** -/
theorem copy_mem_of_ctxOK {M : TrioSeq} {v z t a k d0 d1 : ℕ} (hctx : CtxOK M v z)
    (hM2 : 1 ≤ M.length) (hva : 2 * (v + (t + k * d1)) + z ≤ a) :
    shiftr01 (k * d0) 0 (Lift1 (capBase M v z t) (k * d1)) ∈ W a :=
  W_shift (liftStage_capBase hctx hM2 hva) (k * d0)

/-! ### 18.1 `t = 0` かつ `j0 = 0` かつ `srow = 2` は **`oper_cons_tower2` そのもの**

`Wset.oper_cons_tower2`（`Wset.lean:3231`、**証明ずみ**）:

```lean
theorem oper_cons_tower2 (hR : argOK R) (hRne : R ≠ []) (hd : domT R m)
    (hi1 : srow R (R.length - 1) = 2)
    (hpM : hasParent ((0,v,z) :: R) (srow R (R.length - 1)) R.length) :
    ((0,v,z) :: R)⟦n + 1⟧
      = (0,v,z) :: graft R (Lift1 (((0,v,z) :: R)⟦n⟧) (entry R 1 (R.length-1) - v))
```

`R := cap M b c` と置くと前提は全部そろう:

    `argOK R`     … `argOK_cap`（§10、緑）
    `R ≠ []`      … `cap` は `M.dropLast ++ [1 列]`
    `srow R (|R|-1) = 2` … **`0 < c`**（`srow_cap_last`、§17）
    `hasParent`   … 残核の仮定そのもの
    **`domT R m`**  … `¬ hasParent R (srow) (|R|-1)`
                    ＝ **cap 列が `R` の中では親を持たない ＝ 親が根（`j0 = 0`）**

⟹ **`j0 = 0` ⟺ `domT (cap M b c) m`**、そしてそのとき残核は

    `S⟦n+1⟧ = (0,v,z) :: graft (cap M b c) (Lift1 (S⟦n⟧) (b - v))`

という **`graft` の再帰**になる。これは `GX`（`Gamma.lean:169`）の義務そのもので、
`Lind.mem_GX_of_singletons` の長さ帰納が回す形。**⟹ 設計どおりに閉じている。**

⚠ ただし `S⟦n⟧ ∈ GX` を得るには `CoreSingleton`（＝ `CoreCap`）が要る。
**循環ではなく、これが「長さの帰納」の姿**である（`Lind.lean` の設計）。 -/

theorem srow_cap_last (M : TrioSeq) (b c : ℕ) :
    srow (cap M b c) ((cap M b c).length - 1)
      = (if 0 < c then 2 else if 0 < b then 1 else 0) := by
  have hlen : (cap M b c).length - 1 = M.dropLast.length := by
    rw [cap_length]; omega
  rw [hlen]
  unfold cap
  exact srow_snoc_last M.dropLast ((entry M 0 (M.length - 1), b, c) : ℕ × ℕ × ℕ)

theorem srow_cap_last_eq_two {M : TrioSeq} {b c : ℕ} (hc : 0 < c) :
    srow (cap M b c) ((cap M b c).length - 1) = 2 := by
  rw [srow_cap_last, if_pos hc]

theorem cap_ne (M : TrioSeq) (b c : ℕ) : cap M b c ≠ [] := by
  intro h
  have hl : (cap M b c).length = 0 := by rw [h]; rfl
  rw [cap_length] at hl
  omega


/-! ## 19. ★★★★★ 課題 L109-1: **`c ≥ 2` は穴ではない**（`tower2_root_z_zero` の一般化）

R2 の実測「`c ≥ 2` で `srow = 2` かつ `z = 1` が 69,876 件起きる。
`L53.tower2_root_z_zero` は `c ≤ 1` を使っているので未処理」への回答。

**未処理ではない。同じ算術がそのまま通る。** 定義を並べると:

    `domT R m`（`Wset.lean:61`）… `lev R (|R|-1) = m + 1`
                                   ＝ `2w + c = m + 1`   （`w := entry R 1 (|R|-1)`,
                                                          `c := entry R 2 (|R|-1)`）
    要求（`tower2_stage_fits`）  … `2 * (v + (w - v)) + z ≤ m` ＝ `2w + z ≤ m`
    ⟹ **`2w + z ≤ 2w + c - 1` ⟺ `z < c`**

そして **`z < c` は「根が行 2 の親である」ことから自動で出る**:
`nextrel2` は `entry 2 j0 < entry 2 j1` を要求し、根の行 2 は `z`、孤児の行 2 は `c`。

⟹ **段は `c` の値によらず、根が親である限り必ず収まる。**
`tower2_root_z_zero`（`c = 1` ⟹ `z = 0`）は `z < c` の**特別な場合**にすぎず、
`z = 0` という結論を経由していたのが `c ≤ 1` を要求していた原因。
`z < c` を直接使えば `c ≥ 2` も `z = 1` も**そのまま通る**。 -/

/-- **★★★ 段が収まる本当の条件は `z < c`**（`L53.tower2_stage_fits` の一般化。
あちらは `z = 0` ＋ `0 < c` を使っていた）。 -/
theorem tower2_stage_fits_of_lt {v z m : ℕ} {R : TrioSeq} (hd : domT R m)
    (hzc : z < entry R 2 (R.length - 1))
    (hvw : v ≤ entry R 1 (R.length - 1)) :
    2 * (v + (entry R 1 (R.length - 1) - v)) + z ≤ m := by
  have h1 := hd.1
  unfold lev at h1
  omega

/-- **★★★ 根が行 2 の親なら `z < c`**（`L53.tower2_root_z_zero` の一般化。
あちらは `c = 1` を仮定して `z = 0` を出していた）。 -/
theorem tower2_root_z_lt {v z : ℕ} {R : TrioSeq} (hRne : R ≠ [])
    (h : nextR (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2 0 R.length) :
    z < entry R 2 (R.length - 1) := by
  rw [nextR] at h
  simp only [if_neg (by omega : (2 : ℕ) ≠ 0), if_neg (by omega : (2 : ℕ) ≠ 1)] at h
  have hlt := h.2.2.2.1
  rw [entry_cons_last hRne 2] at hlt
  have hz : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2 0 = z := by simp [entry]
  rw [hz] at hlt
  exact hlt

/-- **★★★★★ ⟹ `c ≥ 2` でも `z = 1` でも段は収まる。**
`srow = 2` の塔で親が根であるかぎり、`c` にも `z` にも制限は要らない。 -/
theorem tower2_stage_fits_root {v z m : ℕ} {R : TrioSeq} (hRne : R ≠ [])
    (hd : domT R m) (hvw : v ≤ entry R 1 (R.length - 1))
    (h : nextR (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2 0 R.length) :
    2 * (v + (entry R 1 (R.length - 1) - v)) + z ≤ m :=
  tower2_stage_fits_of_lt hd (tower2_root_z_lt hRne h) hvw

open Classical in
/-- `parent = 0` の形（`L53.tower2_z_zero_of_parent` に対応）。
`oper_cons_tower2` の場面では `Wset.parent_cons_eq_zero` が親 = 根を供給するので、
**この形がそのまま当たる**。 -/
theorem tower2_stage_fits_of_parent {v z m : ℕ} {R : TrioSeq} (hRne : R ≠ [])
    (hd : domT R m) (hvw : v ≤ entry R 1 (R.length - 1))
    (hpar : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2 R.length)
    (hp0 : parent (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2 R.length = 0) :
    2 * (v + (entry R 1 (R.length - 1) - v)) + z ≤ m := by
  obtain ⟨p0, hp0', -⟩ := hpar
  have hex : ∃ j0, nextR (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2 j0 R.length := ⟨p0, hp0'⟩
  have hspec : nextR (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2
      (parent (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2 R.length) R.length :=
    Classical.epsilon_spec hex
  rw [hp0] at hspec
  exact tower2_stage_fits_root hRne hd hvw hspec

/-- 旧補題は特別な場合として復元できる（`c = 1` ⟹ `z < 1` ⟹ `z = 0`）。 -/
theorem tower2_root_z_zero' {v z : ℕ} {R : TrioSeq} (hRne : R ≠ [])
    (hz' : entry R 2 (R.length - 1) = 1)
    (h : nextR (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2 0 R.length) : z = 0 := by
  have := tower2_root_z_lt hRne h
  omega

/-! ### 19.0 ⚠⚠ **自己訂正（重大）: §19 は既存補題の再発明だった**

`L53Subst.lean` を読み直したところ、**上の 3 本はすべて L2 が既に書いていた**:

    `L53.tower2_root_spec`     `:2360` 親は必ず根（`Wset.parent_cons_eq_zero` 経由）
    `L53.tower2_zr`            `:2380` **`z < entry R 2 (|R|-1)`** ← 私の `tower2_root_z_lt`
    `L53.tower2_stage_fits'`   `:2406` docstring:「**段はいつでもちょうど収まる
                                       （`z = 0` も `hz' = 1` も要らない）**」
                                       ← 私の `tower2_stage_fits_of_lt`

しかも**生きている鎖**（`towerOK2_of_clause3` `:2432` → `towerGraft2_of_liftTie`
→ `towerOK_of_liftTie`）は最初から `tower2_zr` ＋ `tower2_stage_fits'` を使っており、
**`c` について一般**である。

`tower2_root_z_zero`（`:1473`）は `tower2_z_zero_of_parent`（`:1486`）からしか
呼ばれておらず、**そちらはどこからも呼ばれていない**（死んだコード）。
`tower2_stage_fits`（`z = 0` 版、`:1375`）を使うのは旧版の
`towerOK2_of_noTie` / `towerOK2_of_strict` だけで、`towerOK2_of_clause3` が両方を含む。

⟹ **R2 の 69,876 件（`c ≥ 2` かつ `z = 1`）は最初から穴ではなかった。**
穴だったのは `Final.lean` の**コメント**だけである。

### 19.0.1 ⚠ さらに: 「親が根でない場合」は `TowerOK` の設定では**起きない**

`Wset.parent_cons_eq_zero`（**証明ずみ**）:

    `domT R m` ＋ `hasParent ((0,v,z) :: R) (srow R (|R|-1)) |R|`
    ⟹ **`parent ((0,v,z) :: R) (srow ...) |R| = 0`**（＝ 根）

理由: `domT R m` は「末尾列が `R` の中では親を持たない」なので、
`(0,v,z) :: R` での親が添字 `q'+1 ≥ 1` なら `R` の中の添字 `q'` が親になってしまう。

⟹ **`TowerOK2` の設定では親は必ず根。「親が根でない」枝は存在しない。**
私が前便で `Final.lean` に書いてもらった

    `srow = 2, 親が根でない` … **残核**。`z = 1` かつ `c = 1` のときだけ起きる

は**誤り**である。正しくは:

    `srow = 2` … 親は必ず根（`parent_cons_eq_zero`）⟹ `z < c` ⟹ **段は無条件に収まる**
                 残核は段ではなく **`LiftTie`**（`towerOK2_of_clause3` の仮定）

⚠ ただし **`CoreCap` の snoc の残核では話が違う**: あちらは `domT` が成り立たない
（§16、`hasParent` を仮定しているため）ので `parent_cons_eq_zero` が使えず、
**`j0 ≥ 1` は実際に起きる**（R2 の実測 24.0%）。**2 つの設定を混同したのが誤りの原因。**

⟹ 下の §19.1 も、`TowerOK` の設定については誤り。`CoreCap` の設定でのみ意味を持つ。 -/

/-! ### 19.1 （`CoreCap` の設定でのみ）`z = 1` は「起きない」のではなく「起きても構わない」

`Final.lean:81` と `STATUS.md` の

    `srow = 2`, `z = 1` … **起きない**（`tower2_root_z_zero`）

は **`c = 1` に限った言明**だった。正しい形は

    `srow = 2`, 親が根 … **`z < c` が自動 ⟹ 段は必ず収まる**（`c` にも `z` にも制限なし）

⚠ したがって R2 の 69,876 件は**穴ではない**。`tower2_stage_fits` を
`z = 0` ではなく `z < c` で書き直せば、`CoreCap` の `∀ c : ℕ` はそのまま通る。

⚠ **`TowerOK` の設定では「親が根でない」は起きない**（§19.0.1、`parent_cons_eq_zero`）。
起きるのは **`CoreCap` の snoc の残核**のほう（`domT` が無いので `j0 ≥ 1` が 24.0%）。
そこでは `z < c` が使えないので別扱いが要る。
ただし `c ≥ 2` なら根はふたたび行 2 の親候補になる（`z = 1 < 2 ≤ c`）ので、
**`c ≥ 2` はむしろ易しい側**である。 -/


/-! ## 20. ★★★★★ 課題 L109-2: **`rsum` は「写す塊の根の行 0」だけで決まる**

R2 の実測「木の下で `argOK` が破れる（訪問ノードの 5.6%）。反例
`[(0,0,0),(1,0,0),(0,0,0),(1,0,0)]`。`d0 = 0` の塔が同じ塊を反復する。
ただし `entry P 0 0 = 0` なので `rsum` は成り立つ側」を Lean で確定する。

**二分法（接頭辞が根を含むとき）**:

    写す塊 `Q` の根の行 0 = 0（＝ `based Q`）… `rsum A Q` は**自明に成り立つ**
    写す塊 `Q` の根の行 0 ≥ 1               … `rsum A Q` は**必ず破れる**

⟹ §14 の「`W_add` が死ぬ」と R2 の「`rsum` は成り立つ側」は**同じ二分法の裏表**。
`argOK` が生きている（＝ 根だけが行 0 = 0）ところでは塊の根が深いので `rsum` が破れ、
`argOK` が破れている（＝ 木の下に行 0 = 0 の列が湧く）ところでは塊が基づくので
`rsum` が通る。**⟹ どちらの場合も詰まらない。** -/

/-- **★ 写す塊が基づくなら `rsum` は自明**（ℕ なので `0 ≤ p.1`）。 -/
theorem rsum_of_based {A Q : TrioSeq} (hb : based Q) : rsum A Q := by
  intro p _
  rw [hb]
  exact Nat.zero_le _

/-- `not_rsum_of_root_mem` の**必要最小**の形（`argOK Q` は要らない）。 -/
theorem not_rsum_of_root_mem' {A Q : TrioSeq} (hQ : 0 < entry Q 0 0)
    (hroot : ∃ p ∈ A, p.1 = 0) : ¬ rsum A Q := by
  intro h
  obtain ⟨p, hpA, hp0⟩ := hroot
  have h1 := h p (List.mem_append.mpr (Or.inl hpA))
  omega

/-- **★★ 二分法**: 接頭辞が根を含むとき、`rsum` の成否は塊の根の行 0 だけで決まる。 -/
theorem rsum_iff_based_of_root_mem {A Q : TrioSeq} (hroot : ∃ p ∈ A, p.1 = 0) :
    rsum A Q ↔ entry Q 0 0 = 0 := by
  refine ⟨fun h => ?_, fun h => rsum_of_based h⟩
  by_contra hc
  exact not_rsum_of_root_mem' (by omega) hroot h

/-! ### 20.1 ⟹ **基づく塊の `PrefixCopies` は定理**（仮定ゼロ） -/

theorem based_flatMap_copies {Q : TrioSeq} (hb : based Q) (n : ℕ) :
    based ((List.range n).flatMap fun _ => Q) := by
  by_cases hQ : Q = []
  · subst hQ
    simp [based, entry]
  · have hlen : 0 < Q.length := List.length_pos_iff.mpr hQ
    cases n with
    | zero => simp [based, entry]
    | succ n =>
        rw [List.range_succ_eq_map, List.flatMap_cons]
        show entry (Q ++ _) 0 0 = 0
        rw [entry_append_left Q _ hlen]
        exact hb

/-- 基づく塊の写しは無条件で `W`（`W_flatMap_copies` の側条件が自明）。 -/
theorem W_copies_of_based {u : ℕ} {Q : TrioSeq} (hQ : Q ∈ W u) (hb : based Q)
    (n : ℕ) : ((List.range n).flatMap fun _ => Q) ∈ W u :=
  W_flatMap_copies hQ (fun p _ => by rw [hb]; exact Nat.zero_le _) n

/-- **★★★★★ `PrefixCopies`（`L53Subst.lean:3599`）は、写す塊が基づく場合には
仮定ゼロの定理である。** ⟹ R2 の「`argOK` が破れる 5.6%」はここで埋まる。 -/
theorem prefixCopies_of_based {u n : ℕ} {A Q : TrioSeq}
    (hA : A ∈ W u) (hQ : Q ∈ W u) (hb : based Q) :
    A ++ ((List.range n).flatMap fun _ => Q) ∈ W u := by
  refine W_add hA (W_copies_of_based hQ hb n) ?_
  intro p _
  rw [based_flatMap_copies hb n]
  exact Nat.zero_le _

/-! ### 20.2 R2 の反例の確認

`[(0,0,0),(1,0,0),(0,0,0),(1,0,0)]` は `Q = [(0,0,0),(1,0,0)]` の 2 個の写し。
`based Q`（`entry Q 0 0 = 0`）なので `prefixCopies_of_based` がそのまま当たる。 -/

def Qr : TrioSeq := [(0, 0, 0), (1, 0, 0)]

theorem based_Qr : based Qr := rfl

theorem rsum_Qr (A : TrioSeq) : rsum A Qr := rsum_of_based based_Qr

theorem W_copies_Qr {u : ℕ} (hQ : Qr ∈ W u) (n : ℕ) :
    ((List.range n).flatMap fun _ => Qr) ∈ W u :=
  W_copies_of_based hQ based_Qr n


/-- **★★ ⟹ `PrefixCopies` の残核は「写す塊が基づかない」場合だけ。** -/
theorem prefixCopies_split {u n : ℕ} {A Q : TrioSeq} (hA : A ∈ W u) (hQ : Q ∈ W u)
    (hopen : 0 < entry Q 0 0 → A ++ ((List.range n).flatMap fun _ => Q) ∈ W u) :
    A ++ ((List.range n).flatMap fun _ => Q) ∈ W u := by
  rcases Nat.eq_zero_or_pos (entry Q 0 0) with h | h
  · exact prefixCopies_of_based hA hQ h
  · exact hopen h

/-! ### 20.3 ⟹ `argOK` の生死がそのまま `rsum` の生死

`srow = 0` の展開では写す塊は `C.drop j0` で、`entry (C.drop j0) 0 0 = entry C 0 j0`。

    `argOK` が生きている（根だけが行 0 = 0）… `j0 ≥ 1` ⟹ `entry C 0 j0 ≥ 1`
      （`capBase_entry0_pos`）⟹ **`rsum` は破れる**（§14）⟹ `PrefixCopies` の残核側
    `argOK` が破れている（木の下に行 0 = 0 の列が湧く、R2 の 5.6%）
      ⟹ 塊が基づく ⟹ **`rsum` は通る**（§20）⟹ `prefixCopies_of_based` で**無料**

**⟹ R2 の 5.6% は障害ではなく、むしろ無料になる側。**
`oper_cons_nat` が `argOK R` を要求して止まる場面は、まさにこの無料の側である。 -/


/-! ## 21. ★★★★★ 課題 L109-3: **`LiftTie` は「自己段」だけで足りる**

§19.0 の読み直しで、`TowerOK2` の残核は段ではなく **`LiftTie`**（`L53Subst.lean:2337`）
だと確定した。そこでもう 1 段細くできる。

`L53.towerOK2_of_clause3`（`:2432`）が `liftStage_cons` を呼ぶのは

    `ih : ((0,v,z) :: graft R …) ∈ W (2*v+z)`   ← 塔の帰納 `key` は**自己段で回っている**

の 1 か所だけで、**段 `m` は常に `2*v+z`（＝ その cons の `lev` 根）**である。
⟹ `LiftTie` の `∀ m` は使われていない。**`m = 2v+z` の場合だけで足りる。**

`X ∈ W m` から `X ∈ W (lev X 0)` は**出ない**（`W_mono` は逆向き）ので、
これは真の弱化である。 -/

/-- **`LiftTie` の自己段版**（`m = 2v+z` に固定）。 -/
def LiftTieSelf : Prop :=
  ∀ (d v z : ℕ) (R : TrioSeq), argOK R → (∃ p ∈ R, p.2.1 = v) →
    (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W (2 * v + z) →
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d ∈ W (2 * v + z + 2 * d)

theorem liftTieSelf_of_liftTie (h : L53.LiftTie) : LiftTieSelf :=
  fun d v z R hR ht hX => h (2 * v + z) d v z R hR ht hX

/-- タイ／無タイの場合分け（`L53.liftStage_cons` の自己段版）。 -/
theorem liftStage_cons_self (h : LiftTieSelf) {d v z : ℕ} {R : TrioSeq}
    (hargOK : argOK R) (hX : (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W (2 * v + z)) :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d ∈ W (2 * v + z + 2 * d) := by
  by_cases ht : ∃ p ∈ R, p.2.1 = v
  · exact h d v z R hargOK ht hX
  · exact L53.liftStage_of_noTie hargOK (fun p hp hpv => ht ⟨p, hp, hpv⟩) hX

open Classical in
/-- **★★★★★ `TowerOK2` の節 3 側は `LiftTieSelf` だけで出る**
（`L53.towerOK2_of_clause3` の仮定を `LiftTie` から `LiftTieSelf` に弱めたもの）。 -/
theorem towerOK2_of_liftTieSelf {v z a m : ℕ} {R : TrioSeq} (hlt : LiftTieSelf)
    (hR : argOK R) (hRne : R ≠ []) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2) (hz1 : z ≤ 1) (hva : 2 * v + z ≤ a)
    (hgr : ∀ y ∈ W m, based y → graft R y ∈ Wstar)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    ∀ n : ℕ, (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a := by
  have hvw : v < entry R 1 (R.length - 1) := L53.tower2_vw hRne hd hi2 hpM
  have hzr : z < entry R 2 (R.length - 1) := L53.tower2_zr hRne hd hi2 hpM
  have hfits : 2 * v + z + 2 * (entry R 1 (R.length - 1) - v) ≤ m :=
    L53.tower2_stage_fits' hd hzr (by omega)
  have hzero := L53.oper_cons_zero (v := v) (z := z) hR hRne hd hpM
  have key : ∀ n : ℕ, (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W (2 * v + z) := by
    intro n
    induction n with
    | zero => rw [hzero]; exact W_nil _
    | succ n ih =>
        rw [oper_cons_tower2 (m := m) hR hRne hd hi2 hpM]
        have hin : Lift1 ((((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧)
            (entry R 1 (R.length - 1) - v) ∈ W m := by
          cases n with
          | zero => rw [hzero]; simpa using W_nil m
          | succ k =>
              rw [oper_cons_tower2 (m := m) hR hRne hd hi2 hpM] at ih ⊢
              exact W_mono hfits (liftStage_cons_self hlt (argOK_graft hRne hR _) ih)
        have hb : based (Lift1 ((((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧)
            (entry R 1 (R.length - 1) - v)) := by
          refine based_Lift1 _ ?_
          cases n with
          | zero => rw [hzero]; exact based_nil
          | succ k =>
              rw [oper_cons_tower2 (m := m) hR hRne hd hi2 hpM]
              exact L53.based_cons_root v z _
        exact hgr _ hin hb (argOK_graft hRne hR _) v z (2 * v + z) hz1 (by omega)
  exact fun n => W_mono hva (key n)

/-- ⟹ 開核 A（`TowerGraft2`）も `LiftTieSelf` だけで出る。 -/
theorem towerGraft2_of_liftTieSelf (hlt : LiftTieSelf) : TowerGraft2 :=
  fun _ _ _ _ _ hR hRne hz1 hva hd hi2 hgr hpM n _ =>
    towerOK2_of_liftTieSelf hlt hR hRne hd hi2 hz1 hva hgr hpM n

/-- ⟹ `TowerOK` は `LiftTieSelf` ＋ `TowerExp` から出る（`L53.towerOK_of_liftTie` の弱化）。 -/
theorem towerOK_of_liftTieSelf (hlt : LiftTieSelf) (he : TowerExp) : TowerOK :=
  towerOK_of (towerGraft2_of_liftTieSelf hlt) he


/-! ## 22. ★★★★★ 課題 L110 / L111: **`j0` の二分法と、降下が止まる場所**

### 22.1 (L111-1) `j0 ≥ 1` ⟺ **尾の中に親がある**

根つき列 `S = (0,v,z) :: R` の末尾の親 `j0` について、既存の 2 本が二分法を作る:

    `Wset.parent_cons_eq_zero`  `domT R m`（＝ 尾の中に親が**無い**）⟹ **`j0 = 0`**（根）
    `Wset.nextR_cons_uniq`      尾の中に親 `q` があれば、`S` での親は **`q + 1 ≥ 1`**

⟹ **`j0 = 0` ⟺ 尾の中に親が無い（＝ 塔の枝）、`j0 ≥ 1` ⟺ 尾の中に親がある
（＝ `oper_cons_nat` の枝）。**「親が根でない」は自動的に `oper_cons_nat` の枝に落ちる。 -/

/-- **★ 親が根でない ⟹ 尾の中に親がある**（`parent_cons_eq_zero` の対偶）。 -/
theorem hasParent_tail_of_parent_ne_zero {v z : ℕ} {R : TrioSeq} (hRne : R ≠ [])
    (hlev : 1 ≤ lev R (R.length - 1))
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length)
    (hne : parent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length ≠ 0) :
    hasParent R (srow R (R.length - 1)) (R.length - 1) := by
  by_contra hnp
  exact hne (parent_cons_eq_zero (m := lev R (R.length - 1) - 1) hRne
    ⟨by omega, hnp⟩ hpM)

open Classical in
/-- **★ 逆向き: 尾の中に親があれば `j0 = q + 1 ≥ 1`。** -/
theorem parent_cons_ne_zero_of_hasParent {v z : ℕ} {R : TrioSeq} (hR : argOK R)
    (hRne : R ≠ [])
    (hp : hasParent R (srow R (R.length - 1)) (R.length - 1)) :
    parent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length ≠ 0 := by
  have hnrR : nextR R (srow R (R.length - 1))
      (parent R (srow R (R.length - 1)) (R.length - 1)) (R.length - 1) :=
    parent_nextR hp
  have hex : ∃ j0, nextR (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      j0 R.length :=
    ⟨_, (nextR_cons_last hRne _ _).mpr hnrR⟩
  have hspec := Classical.epsilon_spec hex
  have := nextR_cons_uniq (v := v) (z := z) hR hRne hp _ hspec
  show parent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length ≠ 0
  unfold parent
  omega

/-- **★★ `j0 ≥ 1` の枝の展開は無条件の等式**（`oper_cons_nat`）。 -/
theorem oper_cons_of_parent_ne_zero {v z n : ℕ} {R : TrioSeq} (hR : argOK R)
    (hRne : R ≠ []) (hlev : 1 ≤ lev R (R.length - 1))
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length)
    (hne : parent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length ≠ 0) :
    (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ = ((0, v, z) : ℕ × ℕ × ℕ) :: R⟦n⟧ :=
  oper_cons_nat hR hRne (hasParent_tail_of_parent_ne_zero hRne hlev hpM hne)

/-! ### 22.2 (L111-2) ⚠ **等式は無条件だが、所属は閉じない**

`oper_cons_of_parent_ne_zero` は**等式**を無条件で与える。しかし `Aop` の節 2 で要るのは

    `∀ n ≥ 1, ((0,v,z) :: R)⟦n⟧ ∈ W a`   ＝   **`∀ n ≥ 1, (0,v,z) :: R⟦n⟧ ∈ W a`**

で、これは**元の目標と同じ形**（`R` を `R⟦n⟧` に置き換えただけ）である。
⟹ **`oper_cons_nat` は目標を「同じ形の、尾が展開された目標」に書き換えるだけ。
所属は 1 ミリも閉じていない。** R2 の「(P1) は閉じている」は**等式が無条件**の意味であり、
**所属が閉じる意味ではない** —— team-lead の予想どおり。

### 22.3 (L111-3 / L110-1,2) **降下は何の上で回るか**

**長さでは回らない。** `oper` の長さは `j0 + n*(j1 - j0)` なので

    `n = 1` … `j0 + (j1 - j0) = j1 = |M| - 1` ⟹ **1 減る**
    `n ≥ 2` … **増える**

`Aop` の節 2 は `∀ n ≥ 1` を要求するので、**長さは減りも増えもする ⟹ 測度にならない。**

⟹ 実際に回っている測度は 2 つあり、**別々のもの**である:

    (A) `Wstar` 路線 … **`W` の最小不動点の導出木**（`A2'` による帰納）。
        `TowerOK` の仮定 **`Aop W u0 Wstar R`** がまさに「尾が自分の導出を持っている」
        ことの表明で、`Wset.Wstar_closed` はこの上で回る
    (B) `GX` 路線 … **`Lind.mem_GX_of_singletons`（`Lind.lean:79`）は
        `y` の長さの強帰納**（窓分解 `graft_take_drop` で文脈 `y.take p`（長さ `p < |y|`）と
        データ `shiftl0 … (y.drop p)`（長さ `|y| - p < |y|`）に割る）。
        **展開 `⟦n⟧` はここには一度も現れない。**

**(L110-2 への回答) 段のインフレは (B) の測度を壊さない。**
`GX`（`Gamma.lean:169`）は `∀ M ∀ v z ∀ i ∀ a t` を**述語の中で**全称している。
段 `a` とリフト `t` は帰納の**パラメータではない**ので、`a + 2k*d1` の族が出ても
長さ `|y|` は動かない。**壊れない理由はこれ。**

**(L110-3 への回答) 塔の再帰では段はインフレしない。**
`L53.towerOK2_of_clause3` の `key` は

    `∀ n, ((0,v,z) :: R)⟦n⟧ ∈ W (2*v+z)`   ← **段は `2v+z` に固定**

の帰納で、各段で払うリフトは `e = w - v`（**`n` に依らない定数**）。
節 3 に渡すのに要るのは `Lift1 (S⟦n⟧) e ∈ W m` で、
`L53.tower2_stage_fits'` が `2v+z+2e ≤ m` を与える。⟹ **`m` で頭打ち。**
私が §18 で書いた `a + 2k*d1` は `gcopy` から見た形で、**塔として見れば入れ子の
リフトは 1 回ぶんに畳まれる**（`oper_cons_tower2` の再帰形）。**向きは逆ではない。**

### 22.4 ★ **⟹ どこで止まるか（1 行）**

> **`j0 ≥ 1` の枝は `oper_cons_nat` で「尾が展開された同じ目標」に落ちるだけで、
> `CoreCap` は尾の `W` 導出（`Aop W u0 Wstar R`）を仮定していないので、
> そこで測度が無くなる。**

⚠ これは「原理的に不可能」の主張ではない（教訓 13）。**今ある道具立てでは
測度が無い**という報告である。`j0 ≥ 1` の枝に必要なのは
**「尾が自分の `W` 導出を持っている」** —— それがまさに `Wstar` 路線の
`Aop W u0 Wstar R` であり、`TowerOK` が持っていて `CoreCap` が持っていないもの。

⟹ **2 つの路線は合流させる必要がある**: データ側の長さ帰納は `Lind`（B）、
文脈側の降下は `Wstar` の `A2'`（A）。`CoreCap` は (B) の**葉**であり、
その葉で (A) が要る。 -/


/-! ## 23. ★★★★★ 課題 L111 の前提の訂正: **`z=1 ∧ c=1 ∧ 親が根でない` は起きない**

team-lead が「残核」と名指した

    `z = 1` かつ `c = 1` かつ `srow = 2` かつ「親が根でない」

は、**`TowerOK2` の設定（`domT R m` がある）では空虚**である。理由は 2 つあり、
どちらも既存の証明ずみ補題から 1 行で出る:

    `Wset.parent_cons_eq_zero`  `domT R m` ⟹ **親は必ず根** ⟹「親が根でない」は起きない
    `L53.tower2_zr`             `domT R m` ＋ `hasParent` ⟹ **`z < c`**
                                ⟹ `z = 1` かつ `c = 1` は**矛盾** -/

/-- **★ `TowerOK2` の設定では親は必ず根**（`parent_cons_eq_zero` の別名）。 -/
theorem tower2_parent_is_root {v z m : ℕ} {R : TrioSeq} (hRne : R ≠ [])
    (hd : domT R m)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    parent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length = 0 :=
  parent_cons_eq_zero hRne hd hpM

/-- **★★★ `z = 1` かつ `c = 1` は `TowerOK2` の設定では起きない。** -/
theorem tower2_not_z1_c1 {v m : ℕ} {R : TrioSeq} (hRne : R ≠ []) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2)
    (hpM : hasParent (((0, v, 1) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length)
    (hc : entry R 2 (R.length - 1) = 1) : False := by
  have := L53.tower2_zr (v := v) (z := 1) hRne hd hi2 hpM
  omega

/-! ## 24. ⚠ 自己訂正: **`j0 = 0` は `srow ≥ 1` を含意しない**

私は前便で

> `d0 = q.1 = entry M 0 (|M|-1) ≥ 1` は `argOK` から**常に**成り立つので、
> R2 の (d)「`d0 = 0` なら `rsum` が通る」は **`j0 = 0` では起きません**

と書いたが、**誤り**である。`Cnf.lean:1060` の

    `d0 := if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0`

は `i1 = srow = 0` のとき **`j0` に関係なく `d0 = 0`**。そして `srow = 0`（足す列の
行 1・行 2 が両方 0）と `j0 = 0`（根が行 0 の親）は**同時に起きる**:

    `S = [(0,0,0), (5,0,0), (2,0,0)]`  … `argOK` の尾、`srow S 2 = 0`、
      `nextrel0 S 0 2`（`0 < 2`、間の列 `5 ≥ 2`）⟹ `j0 = 0`、`d0 = 0`

⟹ **team-lead と R2 の読みが正しく、私の主張が誤り。食い違いは私の側にあった。**
（`d0 = q.1 ≥ 1` が言えるのは **`srow ≥ 1` かつ `j0 = 0`** のときだけ。）

⚠ なお `srow = 0` かつ `j0 = 0`（＝ 親が根）の枝は **`Wtower2.snoc_flat_root` で
無料**なので（§12.2）、この訂正で残核が増えることはない。 -/


/-! ## 25. ★★★★★ 課題 L112 / L113 の答え: **`CoreCap ⟺ GraftAll`**

### 25.1 (L112) `CoreCap` の鎖は `TowerExp` を「タダにしている」のではない

`Final.lean` を開いて鎖を全部並べた（`file:line` はすべて実在を確認ずみ）:

    `Final.lean:573`  `TRIO_terminates_of_cap (hc : CoreCap)`
      └ `Lind.lean:181`   `coreSingleton_of_cap : CoreCap → CoreSingleton`
      └ `Final.lean:559`  `TRIO_terminates_of_core (hs : CoreSingleton)`
          └ `Final.lean:552` `wf_olt_ST_TS_of_core`
              ├ `Lind.lean:215` `coreCtxSuffixLift_of_core : CoreSingleton → CoreCtxSuffixLift`
              ├ `Lind.lean:208` `corePlantCtxLift_of_core  : CoreSingleton → CorePlantCtxLift`
              └ `Final.lean:540` `wf_olt_ST_TS_of_cores`
                  ├ `Gamma.lean:2625` `graftAll_of_cores : … → Wset.GraftAll`
                  ├ `Lcone.lean:687`  `Wstar2s_closed_of_graftAll (hga : GraftAll)`
                  │    └ `Wset.Wstar2s_closed` `:4347` に 3 本渡す:
                  │       `liftInner_holds`（**無条件**、`Lcone.lean`）
                  │       **`Wset.operTower1_of_graftAll hga`** `:4151`  ← `TowerOK1` 相当
                  │       **`Wset.operTowerExp2_of_graftAll hga`** `:4211` ← **`TowerExp` 相当**
                  └ `trio_cofinality`（**無条件**）

⟹ **答えは (2)。** `TowerExp` に相当する債務は
**`Wset.operTowerExp2_of_graftAll`（`Wset.lean:4211`）として `GraftAll` から出ている**。
`CoreCap` がタダにしているのではなく、**`GraftAll` が `TowerExp` の仕事をしていて、
その `GraftAll` が `CoreCap` から出る**。

`Wset.GraftAll`（`Wset.lean:4085`）の docstring もそう書いている:
「**The single Buchholz-(1) core**: the graft closure of every block at every stage.」

### 25.2 ★★★ `CoreCap` は `GraftAll` の **`y` が 1 列の場合そのもの**

`Lind.graft_singleton_eq_cap`（`Lind.lean:169`）: **`graft M [(0,b,c)] = cap M b c`**。
そして `GraftAll` の装備仮定は **`CtxOK M v z` の定義そのもの**（`Gamma.lean:153` と
`Wset.lean:4086-4088` を並べると逐語で一致）。

⟹ **`GraftAll` に `y := [(0,b,c)]` を入れると `CoreCap` になる**（下の `coreCap_of_graftAll`）。
逆は上の鎖（`Lind` の長さ帰納 ＋ `Gamma` の `graftAll_of_GX`）。
⟹ **`CoreCap ⟺ GraftAll`。** -/

theorem coreCap_of_graftAll (hga : GraftAll) : CoreCap := by
  intro M hMarg hM2 v z hz1 hctx b c a t hva
  have hMne : M ≠ [] := by
    intro h
    rw [h] at hM2
    simp at hM2
  have hy : [((0, b, c) : ℕ × ℕ × ℕ)] ∈ W (2 * b + c) := mem_iff_lev_le.mpr le_rfl
  have hb : based [((0, b, c) : ℕ × ℕ × ℕ)] := rfl
  have harg : argOK (graft M [((0, b, c) : ℕ × ℕ × ℕ)]) := by
    rw [graft_singleton_eq_cap]
    exact argOK_cap hMarg hM2 b c
  have hres := hga M hMarg hMne v z hz1 hctx (2 * b + c)
    [((0, b, c) : ℕ × ℕ × ℕ)] hy hb harg a t hva
  rwa [graft_singleton_eq_cap] at hres

theorem graftAll_of_coreCap (hc : CoreCap) : GraftAll :=
  graftAll_of_cores (coreCtxSuffixLift_of_core (coreSingleton_of_cap hc))
    (corePlantCtxLift_of_core (coreSingleton_of_cap hc))

/-- **★★★★★ `CoreCap` は `GraftAll` と同値。** -/
theorem coreCap_iff_graftAll : CoreCap ↔ GraftAll :=
  ⟨graftAll_of_coreCap, coreCap_of_graftAll⟩

/-! ### 25.3 (L113) ⟹ **`CoreCap ⟸ LiftTieSelf` は通りません**

`towerOK2_of_liftTieSelf`（§21）の前提のうち、`CoreCap` の設定で**供給できないのは
`hgr`** ただ 1 つ:

    `hgr : ∀ y ∈ W m, based y → graft R y ∈ Wstar`

これは「**任意の `y ∈ W m` について graft 先が `W`**」で、`GraftAll`（`Wset.lean:4085`）
そのものの形である。そして §25.2 で **`CoreCap ⟺ GraftAll`** なので、
**`hgr` を供給することは `CoreCap` を仮定することと同じ**。⟹ 循環。

⚠ `Gamma.ctxOK_graft`（`Gamma.lean:307`）で `CtxOK (graft M Y) v z` は出るが、
その前提は **`hYd : Y.dropLast ∈ GX`** で、これも `CoreSingleton`（＝ `CoreCap`）
からしか出ない。⟹ こちらも循環。

**⟹ (L113 の答え) 通りません。足りないのは `hgr` ＝ `GraftAll` ＝ `CoreCap` 自身です。**

### 25.4 ⟹ 3 つの核の正確な関係（今日の到達点）

    **`CoreCap` ⟺ `GraftAll`**（§25.2、緑）… 仮定 1 本。`TowerExp` 相当を**内側に含む**
    **`LiftTieSelf` ＋ `TowerExp`**（§21）… 仮定 2 本。`LiftTieSelf` は文が最小
      （4 量化 / 3 前提、段は `2v+z` 固定）

⟹ team-lead の (3) が正しい: **「仮定 1 本」は見かけで、`CoreCap` は
`LiftTieSelf ∧ TowerExp` に相当する仕事を 1 本に畳んだもの**である。
`GraftAll` の docstring が「the graft closure of every block at every stage」と
言っているとおり、**`CoreCap` は全ブロック・全段の graft 閉包**であって、
`y` が 1 列に見えるのは `graft` が末尾の孤児しか見ないからにすぎない。

**⟹ 乗り換えの判断材料は揃った。** 文の小ささでは `LiftTieSelf`（＋`TowerExp`）、
仮定の本数では `CoreCap`。**同じ仕事量**である。 -/


/-! ## 26. ★★★★ 課題 L115-1: `LiftTieSelf` を割る

`Final.lean:152` の H11 実測（`TowerOK2` の場面 70557 件）:

    狭義                 62476 (88.5%)  `L53.liftStage_of_strict`   ✅ 仮定ゼロ
    無タイだが狭義でない  1950 ( 2.8%)  `L53.liftStage_of_noTie`    ✅ 仮定ゼロ
    タイだが `TieFree`     ( 6.1%)      `L53.liftTie_case_tieFree`  ✅ 既存定理
    **残りのタイ                         ← 核**

無タイは `liftStage_cons_self`（§21）で既に落としてあるので、あと 1 枝
（`TieFree` が立つタイ）を落とす。 -/

/-- **`LiftTieSelf` の残核**: タイがあり、しかも `TieFree` でない場合だけ。
（`v = 0` は `TieFree` が空虚に立つが `liftStage_of_tieFree` が `1 ≤ v` を要求するので、
`1 ≤ v ∧ TieFree` を 1 つの条件にまとめてある。） -/
def LiftTieSelfOpen : Prop :=
  ∀ (d v z : ℕ) (R : TrioSeq), argOK R → (∃ p ∈ R, p.2.1 = v) →
    ¬ (1 ≤ v ∧ TieFree (((0, v, z) : ℕ × ℕ × ℕ) :: R)) →
    (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W (2 * v + z) →
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d ∈ W (2 * v + z + 2 * d)

open Classical in
/-- **★★★ `TieFree` が立つタイ（実測 6.1%）は既存定理で落ちる。** -/
theorem liftTieSelf_of_open (h : LiftTieSelfOpen) : LiftTieSelf := by
  intro d v z R hR ht hX
  by_cases hc : 1 ≤ v ∧ TieFree (((0, v, z) : ℕ × ℕ × ℕ) :: R)
  · refine L53.liftTie_case_tieFree hX ?_ hc.2
    show 1 ≤ entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 0
    simpa [entry] using hc.1
  · exact h d v z R hR ht hc hX

/-- ⟹ `TowerOK` は `LiftTieSelfOpen` ＋ `TowerExp` から出る。 -/
theorem towerOK_of_liftTieSelfOpen (h : LiftTieSelfOpen) (he : TowerExp) : TowerOK :=
  towerOK_of_liftTieSelf (liftTieSelf_of_open h) he

/-! ## 27. ⚠ 課題 L115-1 の `split_lastTie` 路線: **どこで止まるか**

`L53.split_lastTie`（`L53Subst.lean:1692`）は `R = R₁ ++ [tie] ++ R₂` を与え、
`L53.split_lastTie_len`（`:1831`）は `|R₁| < |R|` を与える。長さの帰納は回る。
**しかし帰納の中身が繋がらない。** 定義を開いて確かめた:

### 27.1 タイが何を壊しているか（`Lcone.le1_zero_iff` `:36`）

    `le1 X 0 i` ⟺ `i` の**根以外の**行 0 祖先 `y` がすべて `entry X 1 0 < entry X 1 y`

⟹ 行 1 が `v` **以下**の行 0 祖先が 1 つでもあれば `i` は錐に入らない。
タイ（`= v`）はその最小の壊し方である。
`liftStage_of_window`（`Wtower2.lean:128`）はこの条件が**全列**で成り立つときに
`Lift1 X d = shiftr01 0 d X`（**一様シフト**）に潰れ、`Wslift.ulift_mem_W` で無料になる。

### 27.2 ⚠ 長さの帰納が繋がらない理由

`split_lastTie` で得た `R₁` に帰納法の仮定を当てると

    `Lift1 ((0,v,z) :: R₁) d ∈ W (2v+z+2d)`     （`W_take` で `(0,v,z) :: R₁ ∈ W (2v+z)`）

は出る。**しかし目標は `Lift1 ((0,v,z) :: R₁ ++ [tie] ++ R₂) d`** であり、
接頭辞の結果から全体を復元するには **`[tie] ++ R₂` を連結し直す**必要がある。
それは `WCat`（`Wtower2.lean:1974`、`CORES.md:31`「残核より広い」）である。

⟹ **`split_lastTie` は「タイを 1 本ずつ剥がす」ための道具だが、
剥がした後に戻す操作が `WCat` になる。** ここで止まる。

### 27.3 ⟹ 止まる場所（1 行）

> **タイの分解は接頭辞を短くするが、`Lift1` は列ごとではなく
> 「根の錐」という大域的な条件で決まるので、接頭辞の結果を全体に戻せない。
> 戻す操作が `WCat` になる。**

⚠ 「原理的に不可能」ではない（教訓 13）。**この分解の向きでは繋がらない**、の報告。

### 27.4 ⟹ 繋がりそうな向き（未着手、次のエージェントへ）

`split_lastTie` は**接頭辞**を切るが、`Lift1` の錐は**行 0 の祖先鎖**で決まる。
⟹ 切るなら**行 0 の祖先鎖に沿って**切るべきで、それは `Lind.graft_take_drop`
（`Lind.lean:63`、**窓分解**）の切り方である（行 0 が末尾最小の位置で切る）。
`Lind` の長さ帰納がその切り方で回っているのは偶然ではない。
⟹ **`LiftTieSelf` を攻めるなら `split_lastTie` ではなく窓分解のほうが筋が良い。** -/


/-! ## 28. ★★★★★ 課題 L115-1（続）: **`∀ d` は `d = 1` に落ちる**

`split_lastTie` が繋がらない（§27）ので、別の方向で削る。

`Wset.Lift1_Lift1`（`:1230`）`Lift1 (Lift1 X t) s = Lift1 X (t+s)` と
`Wset.lift_cons`（`:3656`）`Lift1 ((0,v,z) :: R) t = (0,v+t,z) :: ltail v z R t` を
合わせると、**`d` についての帰納が回る**:

    `Lift1 X (d+1) = Lift1 (Lift1 X 1) d = Lift1 ((0,v+1,z) :: ltail v z R 1) d`

しかも `Lift1 X 1 ∈ W (2v+z+2) = W (2(v+1)+z)` は**また自己段**なので、
帰納法の仮定がそのまま当たる（`Wset.argOK_ltail`（`:3716`）で `argOK` も保たれる）。

⟹ **核から `∀ d` が消える。** -/

/-- **`d = 1` に固定した `LiftTieSelf`。** -/
def LiftTieSelfUnit : Prop :=
  ∀ (v z : ℕ) (R : TrioSeq), argOK R → (∃ p ∈ R, p.2.1 = v) →
    (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W (2 * v + z) →
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 ∈ W (2 * v + z + 2)

open Classical in
/-- タイ／無タイの場合分け（`d = 1` 版）。 -/
theorem liftUnit_cons_self (h : LiftTieSelfUnit) {v z : ℕ} {R : TrioSeq}
    (hargOK : argOK R) (hX : (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W (2 * v + z)) :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 ∈ W (2 * v + z + 2) := by
  by_cases ht : ∃ p ∈ R, p.2.1 = v
  · exact h v z R hargOK ht hX
  · have hres := L53.liftStage_of_noTie (d := 1) hargOK
      (fun p hp hpv => ht ⟨p, hp, hpv⟩) hX
    simpa using hres

/-- **★★★★★ `d = 1` から全 `d` が出る**（`Lift1_Lift1` ＋ `lift_cons` の帰納）。 -/
theorem liftSelf_of_unit (h : LiftTieSelfUnit) :
    ∀ (d v z : ℕ) (R : TrioSeq), argOK R →
      (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W (2 * v + z) →
      Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d ∈ W (2 * v + z + 2 * d) := by
  intro d
  induction d with
  | zero => intro v z R _ hX; simpa using hX
  | succ d ih =>
      intro v z R hargOK hX
      have hstep : Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 ∈ W (2 * v + z + 2) :=
        liftUnit_cons_self h hargOK hX
      rw [lift_cons] at hstep
      have hstep' : (((0, v + 1, z) : ℕ × ℕ × ℕ) :: ltail v z R 1)
          ∈ W (2 * (v + 1) + z) := by
        have he : 2 * (v + 1) + z = 2 * v + z + 2 := by omega
        rw [he]
        exact hstep
      have hih := ih (v + 1) z (ltail v z R 1) (argOK_ltail hargOK) hstep'
      have heq : Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) (d + 1)
          = Lift1 (((0, v + 1, z) : ℕ × ℕ × ℕ) :: ltail v z R 1) d := by
        rw [← lift_cons, Lift1_Lift1]
        congr 1
        omega
      rw [heq]
      have he2 : 2 * v + z + 2 * (d + 1) = 2 * (v + 1) + z + 2 * d := by omega
      rw [he2]
      exact hih

theorem liftTieSelf_of_unit (h : LiftTieSelfUnit) : LiftTieSelf :=
  fun d v z R hargOK _ hX => liftSelf_of_unit h d v z R hargOK hX

/-! ## 29. ★★★★★ **今日の最小核** `LiftTieCore`

§26（`TieFree` の枝を落とす）と §28（`∀ d` を落とす）を合わせた形。 -/

/-- **★★★★★ 最小核**: **`d = 1`・自己段・タイあり・`TieFree` でない**。
3 量化（`v z R`）／ 4 前提。 -/
def LiftTieCore : Prop :=
  ∀ (v z : ℕ) (R : TrioSeq), argOK R → (∃ p ∈ R, p.2.1 = v) →
    ¬ (1 ≤ v ∧ TieFree (((0, v, z) : ℕ × ℕ × ℕ) :: R)) →
    (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W (2 * v + z) →
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 ∈ W (2 * v + z + 2)

open Classical in
theorem liftTieSelfUnit_of_core (h : LiftTieCore) : LiftTieSelfUnit := by
  intro v z R hargOK ht hX
  by_cases hc : 1 ≤ v ∧ TieFree (((0, v, z) : ℕ × ℕ × ℕ) :: R)
  · have hres := L53.liftTie_case_tieFree (d := 1) hX
      (by show 1 ≤ entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 0
          simpa [entry] using hc.1) hc.2
    simpa using hres
  · exact h v z R hargOK ht hc hX

theorem liftTieSelf_of_core (h : LiftTieCore) : LiftTieSelf :=
  liftTieSelf_of_unit (liftTieSelfUnit_of_core h)

/-- **★★★★★ `TowerOK` は `LiftTieCore` ＋ `TowerExp` から出る。** -/
theorem towerOK_of_liftTieCore (h : LiftTieCore) (he : TowerExp) : TowerOK :=
  towerOK_of_liftTieSelf (liftTieSelf_of_core h) he

/-- 位置づけ: `L53.LiftTie` からはもちろん出る（前提を落とすだけ）。 -/
theorem liftTieCore_of_liftTie (h : L53.LiftTie) : LiftTieCore :=
  fun v z R hR ht _ hX => by
    have := h (2 * v + z) 1 v z R hR ht hX
    simpa using this


/-! ## 30. ★★★★ 課題 L116: 窓分解と `Lift1` の錐

`Lcone.le1_zero_iff`（`Lcone.lean:36`）:

    根が行 0 で狭義最浅なら
    **`le1 X 0 j` ⟺ `j` の根以外の行 0 祖先 `y` がすべて `entry X 1 0 < entry X 1 y`**

⟹ 錐は**行 0 の祖先について上方閉**（祖先が錐に無ければ子孫も無い）。
対偶で言えば **「ブロッカー（行 1 ≤ v の列）は自分の行 0 部分木を丸ごと錐から外す」**。 -/

/-- **★★ 錐は行 0 の祖先について上方閉。**（対偶: ブロッカーは部分木ごと外す。） -/
theorem le1_root_of_rtg0 {X : TrioSeq}
    (hr : ∀ l, 0 < l → l < X.length → entry X 0 0 < entry X 0 l)
    {p i : ℕ} (hi : i < X.length)
    (hpi : Relation.ReflTransGen (nextrel0 X) p i) (h : le1 X 0 i) :
    le1 X 0 p := by
  have hple : p ≤ i := nextrel0_rtrancl_index_le hpi
  have hp : p < X.length := by omega
  rw [le1_zero_iff hr hp]
  rw [le1_zero_iff hr hi] at h
  intro y hyp hy0
  exact h y (hyp.trans hpi) hy0

/-- **★ タイは錐に入らない**（`nextrel1` は行 1 の狭義増加を要求）。 -/
theorem not_le1_of_tie {X : TrioSeq} {j : ℕ} (hj : (0 : ℕ) ≠ j)
    (htie : entry X 1 j = entry X 1 0) : ¬ le1 X 0 j := by
  intro h
  have := le1_entry1_lt h hj
  omega

/-- **★★ ⟹ タイの行 0 部分木は丸ごと錐の外**（`Lift1` が触らない）。 -/
theorem not_le1_of_tie_ancestor {X : TrioSeq}
    (hr : ∀ l, 0 < l → l < X.length → entry X 0 0 < entry X 0 l)
    {y i : ℕ} (hy0 : (0 : ℕ) ≠ y) (hi : i < X.length)
    (hyi : Relation.ReflTransGen (nextrel0 X) y i)
    (htie : entry X 1 y = entry X 1 0) : ¬ le1 X 0 i := by
  intro h
  exact not_le1_of_tie hy0 htie (le1_root_of_rtg0 hr hi hyi h)

/-- **★★★ 窓の切れ目（行 0 の最小点）では錐の判定が「その列だけ」で済む。**
`Lind.graft_take_drop`（`Lind.lean:63`）が切る位置 `p` は行 0 で最小なので、
`p` の根以外の行 0 祖先は `p` 自身しかない。 -/
theorem le1_root_at_min {X : TrioSeq}
    (hr : ∀ l, 0 < l → l < X.length → entry X 0 0 < entry X 0 l)
    {p : ℕ} (hp0 : 0 < p) (hp : p < X.length)
    (hmin : ∀ j, 0 < j → j < X.length → entry X 0 p ≤ entry X 0 j) :
    le1 X 0 p ↔ entry X 1 0 < entry X 1 p := by
  rw [le1_zero_iff hr hp]
  constructor
  · intro h
    exact h p Relation.ReflTransGen.refl (by omega)
  · intro h y hyp hy0
    have hyp' : y = p := by
      rcases Relation.ReflTransGen.cases_tail hyp with heq | ⟨c, hyc, hcp⟩
      · exact heq.symm
      · exfalso
        have hclt : c < p := hcp.2.2.1
        have hdeep : entry X 0 c < entry X 0 p := hcp.2.2.2.1
        rcases Nat.eq_zero_or_pos c with rfl | hcpos
        · have := nextrel0_rtrancl_index_le hyc
          omega
        · have := hmin c hcpos (by omega)
          omega
    rw [hyp']
    exact h

/-! ### 30.1 ★★ **BMS では「行 0 の部分木」＝ 区間**（`Gcopy.rtg0_of_window` `:65`）

    `rtg0_of_window : j < |M| → a ≤ j → (∀ l, a < l → l ≤ j → entry M 0 a < entry M 0 l)
                    → ReflTransGen (nextrel0 M) a j`

⟹ **`y` の行 0 部分木は区間 `[y, k)`**（`k` は `y` の次に行 0 が `≤ entry X 0 y` になる位置）。
⟹ `Wtower2.W_segment`（`:2981`）`(M.drop j).take k ∈ W (lev M j)` と
   `Wtower2.drop_rebase_mem_W`（`:3196`）が**そのまま当たる**。 -/

/-- **★★ タイの部分木（区間）は丸ごと錐の外。** -/
theorem not_le1_of_tie_window {X : TrioSeq}
    (hr : ∀ l, 0 < l → l < X.length → entry X 0 0 < entry X 0 l)
    {y i : ℕ} (hy0 : (0 : ℕ) ≠ y) (hyi : y ≤ i) (hi : i < X.length)
    (hwin : ∀ l, y < l → l ≤ i → entry X 0 y < entry X 0 l)
    (htie : entry X 1 y = entry X 1 0) : ¬ le1 X 0 i :=
  not_le1_of_tie_ancestor hr hy0 hi (rtg0_of_window hi hyi hwin) htie

/-! ### 30.2 ⚠ **自己訂正**: 分解はできる。止まるのは**再結合**

初稿でここに「`Lind` の窓分解は行 0 の最小点で切るのでタイを分離できない、
必要なのは区間ではない木の部分木分解だ」と書いたが、**誤りだった**。
`Gcopy.rtg0_of_window`（`:65`）を開いたら **BMS では部分木は区間**であり、
`W_segment` / `drop_rebase_mem_W` が**すでにある**。**分解はできる。**

⟹ 止まるのは §27 とまったく同じ場所である:

    タイの部分木 `[y, k)` は区間 ⟹ `W_segment` で `W (lev X y)` に置ける（分解 ✅）
    `Lift1 X d` はその区間に触らない（`not_le1_of_tie_window`、上、緑）
    **しかし `X.take y ++ (部分木) ++ X.drop k` に戻す操作が `WCat`**（再結合 ❌）

### 30.3 ★ 止まる場所（1 行、§27 と同一）

> **タイの部分木は区間なので分解はできる（`W_segment`）。だが `Lift1` の結論は
> 列全体についてのものなので、分解した断片を `W` の中で戻す必要があり、
> それが `WCat` になる。分解ではなく再結合が壁。**

⟹ §27（`split_lastTie`、接頭辞で切る）も §30（窓分解、行 0 で切る）も
**同じ壁**（`WCat`）に当たる。**`Lift1` の核は「分解して組み直す」形では取れない。**

### 30.4 ⟹ 次のエージェントへ

`Lift1` は列ごとの局所操作ではなく**根の錐という大域条件**なので、
分解・再結合の路線は `WCat` に帰着する（§27・§30 で 2 回確認）。
⟹ 残る道は **`Aop` の節 2 で降りる**（`mem_iff_oper_mem`、`Wchar.lean:75`）だけ:

    `Lift1 X 1 ∈ W (m+2)` ⟸ `∀ n ≥ 1, (Lift1 X 1)⟦n⟧ ∈ W (m+2)`

そして `Wtower2` には**その挟み込みが既にある**:

    `Le1_Lift1_oper`（`Wtower2.lean:4408`）      `Lift1 (X⟦n⟧) d ≤₁ (Lift1 X d)⟦n⟧`
    `Le1_oper_Lift1_shiftr01`（`:4457`）         `(Lift1 X d)⟦n⟧ ≤₁ shiftr01 0 d (X⟦n⟧)`
    `Wslift.ulift_mem_W`（`:461`）               `shiftr01 0 d Y ∈ W (m+2d)`（**無条件**）

⟹ **上界は無料。隙間を潰すのが `WConvex`**（`Wtower2.lean:450`、
`liftStage_of_wconvex'` `:4473`）。**`d = 1` に落ちた今、隙間は行 1 で高々 1**
なので、**幅 1 の凸性（`WConvex1` / `WConvexUnit`）で足りるはず**である。
`L53.liftStage_of_wconvex1` / `wconvex1_of_unit` が既にある。**そこが次の一手。** -/


/-! ## 31. `LiftTieCore` の位置づけ（`CORES.md` の「より強いもの」列） -/

/-- `LiftStage`（全部の根での (WL)）からは当然出る。 -/
theorem liftTieCore_of_liftStage (h : LiftStage) : LiftTieCore :=
  liftTieCore_of_liftTie (L53.liftTie_of_liftStage h)

/-- `WConvexUnit`（1 列 1 段の凸性）からも出る
（`L53.wconvex1_of_unit` → `L53.liftStage_of_wconvex1`）。 -/
theorem liftTieCore_of_wconvexUnit (h : L53.WConvexUnit) : LiftTieCore :=
  liftTieCore_of_liftStage (L53.liftStage_of_wconvex1 (L53.wconvex1_of_unit h))

/-- `WConvex1`（幅 1 の凸性）からも出る。 -/
theorem liftTieCore_of_wconvex1 (h : L53.WConvex1) : LiftTieCore :=
  liftTieCore_of_liftStage (L53.liftStage_of_wconvex1 h)

/-- `WSnoc` からも出る（`L53.liftStage_of_wsnoc`）。 -/
theorem liftTieCore_of_wsnoc (h : WSnoc) : LiftTieCore :=
  liftTieCore_of_liftStage (L53.liftStage_of_wsnoc h)

/-- `Row1Mono` からも出る。 -/
theorem liftTieCore_of_row1mono (h : Row1Mono) : LiftTieCore :=
  liftTieCore_of_liftStage (liftStage_of_row1mono h)

/-! ### 31.1 ⟹ 今日の核の一覧（`L105Cap.lean` の到達点）

| 命題 | 場所 | ∀ | → | 単独か | より強いもの |
|---|---|---|---|---|---|
| **`LiftTieCore`** | §29 | **3** | **4** | `TowerExp` が要る | `LiftTie`, `LiftStage`, `WConvex1`, `WConvexUnit`, `WSnoc`, `Row1Mono` |
| `LiftTieSelfUnit` | §28 | 3 | 3 | 同上 | `LiftTieCore` は前提が 1 本多い |
| `LiftTieSelf` | §21 | 4 | 3 | 同上 | ↑ |
| `L53.LiftTie` | `L53Subst:2337` | 5 | 3 | 同上 | ↑ |
| **`CoreCap` ⟺ `Wset.GraftAll`** | §25 | 7 | 5 | **単独** | —— |

**`CoreCap` だけが単独**だが、§25 のとおり `TowerExp` 相当を内側に畳んでいる。
⟹ **仕事量は同じ。** 文の小ささでは `LiftTieCore` が今日の最小。 -/


/-! ## 32. ★★★★★ **行 2 ≡ 0 なら (WL) は無条件に無料**（H12 の線への回答）

H12 の「未判定 60016 件は `v=0` / `b=1` のタイに固まる。`snoc_zeroRow2` 系を伸ばせば
片づくのでは」という見立てを、定義から確かめた。**もっと直接的な形で正しい。**

`Lift1` は**行 2 を動かさない**（`Wset.entry2_Lift1`）。したがって `X` の行 2 が
恒等的に `0` なら `Lift1 X d` の行 2 も `0` で、`Wtower2.zeroRow2_mem_Wself`（`:3011`）が
そのまま `Wself` に入れる。そして

    `lev (Lift1 X d) 0 = 2*(entry X 1 0 + d) + entry X 2 0 = lev X 0 + 2d ≤ m + 2d`

（根は反射で必ず錐に入る: `L53.entry1_Lift1_zero`）。⟹ `W_mono` で終わり。

**⟹ `(WL)` の「行 2 ≡ 0」の場合は、タイがあろうがなかろうが、`d` が何であろうが、
仮定ゼロで成り立つ。**（既存の `snoc_zeroRow2` / `shTower_zeroRow2` の**リフト版**。
`grep zeroRow2` では見つからなかったので新規。） -/

theorem zeroRow2_Lift1 {X : TrioSeq} {d : ℕ} (h : ∀ p ∈ X, p.2.2 = 0) :
    ∀ p ∈ Lift1 X d, p.2.2 = 0 := by
  intro p hp
  unfold Lift1 at hp
  rw [List.mem_map] at hp
  obtain ⟨j, hj, hjp⟩ := hp
  rw [List.mem_range] at hj
  rw [← hjp]
  show entry X 2 j = 0
  exact h _ (entry_pair_mem (B := X) hj)

/-- **★★★★★ 行 2 ≡ 0 なら `(WL)` は仮定ゼロで成り立つ。** -/
theorem liftStage_of_zeroRow2 {m d : ℕ} {X : TrioSeq} (hz : ∀ p ∈ X, p.2.2 = 0)
    (hX : X ∈ W m) : Lift1 X d ∈ W (m + 2 * d) := by
  by_cases hne : X = []
  · subst hne
    simpa using W_nil (m + 2 * d)
  · have hself : Lift1 X d ∈ Wself := zeroRow2_mem_Wself (zeroRow2_Lift1 hz)
    have h1 : entry (Lift1 X d) 1 0 = entry X 1 0 + d := L53.entry1_Lift1_zero hne d
    have h2 : entry (Lift1 X d) 2 0 = entry X 2 0 := entry2_Lift1 X d 0
    have hlx : lev X 0 ≤ m := lev_root_le_of_mem_W hX hne
    have hlev : lev (Lift1 X d) 0 ≤ m + 2 * d := by
      unfold lev at hlx ⊢
      rw [h1, h2]
      omega
    exact W_mono hlev hself

/-! ### 32.1 ⟹ `LiftTieCore` は「行 2 に非零がある」場合だけ

行 2 ≡ 0 の枝が落ちるので、残核はさらに細くなる。
とくに**根の行 2 `z` が `0` の場合は、`R` に行 2 > 0 の列が要る**。 -/

def LiftTieCoreRow2 : Prop :=
  ∀ (v z : ℕ) (R : TrioSeq), argOK R → (∃ p ∈ R, p.2.1 = v) →
    ¬ (1 ≤ v ∧ TieFree (((0, v, z) : ℕ × ℕ × ℕ) :: R)) →
    (∃ p ∈ (((0, v, z) : ℕ × ℕ × ℕ) :: R), 0 < p.2.2) →
    (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W (2 * v + z) →
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 ∈ W (2 * v + z + 2)

open Classical in
theorem liftTieCore_of_row2 (h : LiftTieCoreRow2) : LiftTieCore := by
  intro v z R hR ht htf hX
  by_cases hz2 : ∃ p ∈ (((0, v, z) : ℕ × ℕ × ℕ) :: R), 0 < p.2.2
  · exact h v z R hR ht htf hz2 hX
  · have hz : ∀ p ∈ (((0, v, z) : ℕ × ℕ × ℕ) :: R), p.2.2 = 0 := by
      intro p hp
      by_contra hc
      exact hz2 ⟨p, hp, by omega⟩
    simpa using liftStage_of_zeroRow2 (d := 1) hz hX

/-- ⟹ `TowerOK` は `LiftTieCoreRow2` ＋ `TowerExp` から出る。 -/
theorem towerOK_of_liftTieCoreRow2 (h : LiftTieCoreRow2) (he : TowerExp) : TowerOK :=
  towerOK_of_liftTieCore (liftTieCore_of_row2 h) he


/-! ## 33. ★★★★★ 課題 L117: `WConvexUnit` は**再結合の壁を避けている**

### 33.1 (Q1) 避けています。理由は 1 行

> **`WConvexUnit` 経路は列を一度も切らない。** `lift1_mem_of_wconvex1`
> （`L53Subst.lean:3230`）は `mem_of_oper_mem`（`Aop` の節 2）で降り、各段で
> **完全な列 3 本**（`Lift1 (Y⟦n⟧) 1` / `(Lift1 Y 1)⟦n⟧` / `shiftr01 0 1 (Y⟦n⟧)`）を
> 比べるだけ。`take` / `drop` / `++` は**一度も出てこない**。
> **切らないので、戻す必要が無い。**

`wconvex1_of_unit`（`:3514`）も同じで、添字 `i` の帰納で**列全体**を 1 列ずつ下げ、
`eq_of_entries` で終える。連結は現れない。

⚠ **代わりに払う代償**（正直に）: `WConvexUnit` は「行 1 を 1 列だけ 1 下げても `W a`」で、
**行 1 を動かすと `srow` / `nextrel1` / `nextrel2` が変わり得る**ので展開木ごと変わる。
⟹ **難所は「再結合」ではなく「展開の不安定性」**。壁は避けているが、別の壁がある。

### 33.2 (Q2) 幅 1 は本当に出る

`L53.sandwich_window_one`（`L53Subst.lean:3200`）は **`d = 1` に固定して書かれている**:

    `entry (shiftr01 0 1 Y) 1 j ≤ entry (Lift1 Y 1) 1 j + 1`

そして `lift1_mem_of_wconvex1` はそれをそのまま `WConvex1` の窓条件に渡している。
⟹ **`d = 1` への圧縮と噛み合っている。**
（`L53.liftStage1_of_wconvex1` → `L53.liftStage_of_unit`（`:3174`）で全 `d` に戻る。
**L2 は `LiftStage` について同じ `d = 1` 圧縮を既にやっていた**。私の §28 はその
タイ版・自己段版。）

### 33.3 (Q3) 挟み込みは閉じている（既存・緑）

    `Wtower2.Le1_Lift1_oper`（`:4415`）        `Lift1 (X⟦n⟧) d ≤₁ (Lift1 X d)⟦n⟧`
    `Wtower2.Le1_oper_Lift1_shiftr01`（`:4482`）`(Lift1 X d)⟦n⟧ ≤₁ shiftr01 0 d (X⟦n⟧)`
    `Wslift.ulift_mem_W`                        上端は無料

`L53.lift1_mem_of_wconvex1`（`:3230`）が**すでに緑で閉じている**。

### 33.4 ⟹ 向きの心配への回答: **使う実例だけに絞れる**

`WConvexUnit` / `WConvex1` は `LiftTieCore` より強い（`liftTieCore_of_wconvexUnit`）。
だが `lift1_mem_of_wconvex1` が凸性を呼ぶのは **1 か所だけ**で、その 3 本は
**`Y⟦n⟧` から作られた特定の列**である。⟹ その実例だけを核にできる。 -/

/-- **★★★ `lift1_mem_of_wconvex1` が実際に使う凸性の実例だけ。**
`Le1` の 2 本も窓条件も上端も既存定理で自動なので、残るのはこれだけ。 -/
def WConvexLift1 : Prop :=
  ∀ (m n : ℕ) (Y : TrioSeq), Y⟦n⟧ ∈ W m → Lift1 (Y⟦n⟧) 1 ∈ W (m + 2) →
    (Lift1 Y 1)⟦n⟧ ∈ W (m + 2)

theorem convexLift1_of_wconvex1 (h : L53.WConvex1) : WConvexLift1 := by
  intro m n Y hY hL
  refine h (m + 2) (Lift1 (Y⟦n⟧) 1) ((Lift1 Y 1)⟦n⟧) (shiftr01 0 1 (Y⟦n⟧)) hL ?_
    (Le1_Lift1_oper Y 1 n) (Le1_oper_Lift1_shiftr01 Y 1 n)
    (fun j => L53.sandwich_window_one (Y⟦n⟧) j)
  have := ulift_mem_W (Y⟦n⟧) hY (d := 1)
  simpa using this

theorem lift1_mem_of_convexLift1 (h : WConvexLift1) {m : ℕ} {Y : TrioSeq}
    (hop : ∀ n, 1 ≤ n → Y⟦n⟧ ∈ W m ∧ Lift1 (Y⟦n⟧) 1 ∈ W (m + 2 * 1)) :
    Lift1 Y 1 ∈ W (m + 2 * 1) := by
  refine mem_of_oper_mem (fun n hn => ?_)
  have hres := h m n Y (hop n hn).1 (by simpa using (hop n hn).2)
  simpa using hres

open Classical in
/-- **★★★★★ 使う実例だけで `LiftStage1` が出る**（`L53.liftStage1_of_wconvex1` の
`WConvex1` を `WConvexLift1` に置き換えた版）。 -/
theorem liftStage1_of_convexLift1 (h : WConvexLift1) : L53.LiftStage1 := by
  intro m X hX
  have hsub : W m ⊆ {Y : TrioSeq | Y ∈ W m ∧ Lift1 Y 1 ∈ W (m + 2 * 1)} := by
    refine A2' ?_
    rintro Y (⟨hl, hlev⟩ | hop | ⟨m', hm', hd', hgr⟩)
    · refine ⟨A1_intro (Or.inl ⟨hl, hlev⟩), ?_⟩
      rcases Nat.eq_zero_or_pos Y.length with h0 | hpos
      · have hnil : Y = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        show Lift1 ([] : TrioSeq) 1 ∈ W (m + 2 * 1)
        simpa using W_nil (m + 2 * 1)
      · have h1 : Y.length = 1 := by omega
        have hbc : 2 * entry Y 1 0 + entry Y 2 0 = 0 := by
          unfold lev at hlev; omega
        exact lift1_singleton_mem h1 (by omega)
    · exact ⟨mem_of_oper_mem (fun n hn => (hop n hn).1),
        lift1_mem_of_convexLift1 h (fun n hn => hop n hn)⟩
    · have hY : Y ∈ W m :=
        A1_intro (Or.inr (Or.inr ⟨m', hm', hd', fun z hz hb => (hgr z hz hb).1⟩))
      refine ⟨hY, ?_⟩
      rcases Nat.lt_or_ge Y.length 2 with hsm | hbig
      · have hYne : Y ≠ [] := by
          intro hc
          rw [hc] at hd'
          exact not_domT_nil m' hd'
        have h1 : Y.length = 1 := by
          have : 0 < Y.length := List.length_pos_iff.mpr hYne
          omega
        have hlev := hd'.1
        rw [show Y.length - 1 = 0 from by omega] at hlev
        unfold lev at hlev
        exact lift1_singleton_mem h1 (by omega)
      · exact lift1_mem_of_convexLift1 h (aop_clause3_to_clause2 hbig hd' hgr)
  have hres := (hsub hX).2
  have he : m + 2 * 1 = m + 2 := by omega
  rwa [he] at hres

/-- ⟹ `LiftTieCore` は `WConvexLift1` から出る。 -/
theorem liftTieCore_of_convexLift1 (h : WConvexLift1) : LiftTieCore :=
  liftTieCore_of_liftStage (L53.liftStage_of_unit (liftStage1_of_convexLift1 h))


/-! ### 33.5 ⚠ 向きについての正直な結論

`WConvexLift1` は「実際に使う実例」まで絞ったが、**それでも `LiftStage` 全体が出る**
（`liftStage1_of_convexLift1` → `L53.liftStage_of_unit`）。理由は構造的である:

> **凸性経路の帰納は `A2'`（`W m` の最小不動点）の上で回るので、`Y` は `W m` の
> 元すべてを走る。`LiftTieCore` の制限（cons 形・自己段・タイあり・`¬TieFree`）は
> `Y⟦n⟧` に受け継がれないので、帰納の中で保てない。**

⟹ **凸性経路では `LiftTieCore` の弱さを保てない。** 強い側（`LiftStage`）を
証明することになる。これは避けられない。

**⟹ 選択肢は 2 つ:**

    (i) 凸性経路を取る … `WConvexLift1`（＝ 実際に使う実例）を証明する。
        目標より強いものを証明することになるが、**再結合の壁は無い**（§33.1）
    (ii) `LiftTieCore` の弱さを活かす … タイ・自己段・`d=1`・行 2 非零という制限を
        使う別の議論を探す。ただし §27 / §30 で「分解・再結合」は封じられている

**私の見立て: (i) が現実的。** 理由は 3 つ:

    `WConvexLift1` の 3 本は**同じ `Y⟦n⟧` から作った 2 つのリフト**で、
      行 0 と行 2 は**完全に一致**し、行 1 だけが錐の外で 1 違う（`sandwich_window_one`）
    上端 `shiftr01 0 1 (Y⟦n⟧)` は**無条件で `W`**（`ulift_mem_W`）
    下端 `Lift1 (Y⟦n⟧) 1` は**帰納法の仮定**

⟹ **要るのは「行 1 を錐の外で 1 だけ下げても `W` を保つ」ただ 1 点**であり、
それは `Row1Mono` の**最小の場合**（1 段・下端 witness つき・行 0/行 2 不変）である。
`L53.WConvexUnit`（`:3505`）がその形。**そこが本当の底。** -/


/-! ### 33.6 ★ (Q1) の**機械的な確認**: 経路に連結補題は 1 つも現れない

team-lead の問い「その帰納が `W` の中で何を使うのか。`W_take` / `W_segment` / `W_add` の
どれか」に、**証明本文を機械的に走査して**答える。

`L53Subst.lean` の 4 本の証明本文（合計 119 行）を
`W_add` / `rsum` / `W_take` / `W_segment` / `W_drop` / `WCat` / `++` / `.take` / `.drop`
で検索した結果:

    `wconvex1_of_unit`        （65 行） … **該当ゼロ**
    `lift1_mem_of_wconvex1`   （ 8 行） … **該当ゼロ**
    `liftStage1_of_wconvex1`  （36 行） … **該当ゼロ**
    `liftStage_of_unit`       （10 行） … **該当ゼロ**

**実際に使っている `W` レベルの道具は次だけ:**

    `wconvex1_of_unit`       `eq_of_entries` / `Le1_trans` / `lowerAt`
                             （＋ 仮定 `WConvexUnit` 自身）
    `lift1_mem_of_wconvex1`  **`mem_of_oper_mem`**（節 2）/ `ulift_mem_W` /
                             `Le1_Lift1_oper` / `Le1_oper_Lift1_shiftr01` /
                             `sandwich_window_one`
    `liftStage1_of_wconvex1` **`A2'`**（最小不動点の帰納）/ `A1_intro` /
                             `mem_of_oper_mem` / `W_nil` / `lift1_singleton_mem` /
                             `aop_clause3_to_clause2` / `not_domT_nil`

⟹ **`B ∈ W a` を出しているのは `mem_of_oper_mem`（`Aop` の節 2）と `A2'` だけ。**
断片を組み直す操作は**存在しない**。

### 33.7 ⟹ (Q1) の答え（1 行）

> **`B ∈ W a` は `mem_of_oper_mem`（節 2 で降りる）と `A2'`（最小不動点の帰納）だけで出る。
> `W_add` も `rsum` も `W_take` も `W_segment` も経路に現れない。⟹ 再結合の壁は無い。**

⚠ ただし §33.1 の但し書きは残る: `WConvexUnit` **自身**の証明はまだ無く、
そこで払う代償は「行 1 を 1 下げると `srow` / `nextrel1` / `nextrel2` が変わり得るので
展開木が変わる」ことである。**壁は別物**（再結合ではなく展開の不安定性）。 -/


/-! ## 34. R2 の §R97 を補題にする ＋ 凸性経路の第一歩

### 34.1 ★ **`TowerOK2` の場面では最終列はタイにならない**（R2 実測 0 / 1,821,258）

R2 の算術は正しく、しかも**既存の `L53.tower2_vw`（`L53Subst.lean:2392`）1 本で出る**。 -/

theorem last_not_tie {v z m : ℕ} {R : TrioSeq} (hRne : R ≠ []) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    entry R 1 (R.length - 1) ≠ v := by
  have := L53.tower2_vw hRne hd hi2 hpM
  omega

/-! ### 34.2 ★★★ 凸性経路の第一歩: **`Lift1` は `srow` を変えない**

`WConvexUnit` / `WConvexLift1` の代償は「行 1 を動かすと `srow` / `nextrel1` /
`nextrel2` が変わり展開木が変わる」ことだった（§33.1）。**そのうち `srow` は変わらない。**

骨: `Lift1` は行 2 を不変にする（`entry2_Lift1`）。行 1 については、
**根以外の列が錐に入るには行 1 が根より真に大きい必要がある**
（`Wset.le1_entry1_lt`）ので、`0 < entry X 1 j` の真偽はリフトで**変わらない**
（もともと正なら正のまま、0 なら錐に入れないのでリフトされない）。

⟹ **悪い部分がどの行を見るかは、リフトで動かない。** -/

theorem entry1_pos_Lift1 {X : TrioSeq} {d j : ℕ} (hj : (0 : ℕ) ≠ j) :
    0 < entry (Lift1 X d) 1 j ↔ 0 < entry X 1 j := by
  rcases Nat.lt_or_ge j X.length with hlt | hge
  · rw [entry1_Lift1 hlt]
    by_cases hc : le1 X 0 j
    · have h := le1_entry1_lt hc hj
      rw [if_pos hc]
      omega
    · rw [if_neg hc]
      omega
  · rw [entry1_out (by rw [Lift1_length]; omega), entry1_out hge]

/-- **★★★ `Lift1` は（根以外の）`srow` を変えない。** -/
theorem srow_Lift1 {X : TrioSeq} {d j : ℕ} (hj : (0 : ℕ) ≠ j) :
    srow (Lift1 X d) j = srow X j := by
  unfold srow
  rw [entry2_Lift1]
  by_cases h2 : 0 < entry X 2 j
  · rw [if_pos h2, if_pos h2]
  · rw [if_neg h2, if_neg h2]
    by_cases h1 : 0 < entry X 1 j
    · rw [if_pos ((entry1_pos_Lift1 hj).mpr h1), if_pos h1]
    · rw [if_neg (fun hc => h1 ((entry1_pos_Lift1 hj).mp hc)), if_neg h1]

/-- 長さ 2 以上なら悪い部分の添字 `|X|-1` は根でないので、上が当たる。 -/
theorem srow_Lift1_last {X : TrioSeq} {d : ℕ} (h2 : 2 ≤ X.length) :
    srow (Lift1 X d) ((Lift1 X d).length - 1) = srow X (X.length - 1) := by
  rw [Lift1_length]
  exact srow_Lift1 (by omega)

/-! ### 34.3 ⟹ 残る不安定性は `nextrel1` / `nextrel2` だけ

    行 0 の木 … **不変**（`nextrel0_Lift1` / `le0_Lift1`、§10）
    `srow`   … **不変**（`srow_Lift1`、上）
    行 2      … **不変**（`entry2_Lift1`）
    長さ      … **不変**（`Lift1_length`）
    **`nextrel1` / `nextrel2`** … 錐の内と外で行 1 の差が `d` ずれるので**変わりうる**

⟹ `WConvexLift1` の難所は**行 1 の木だけ**に絞られた。 -/


/-! ## 35. ★★★★ 凸性経路の第二歩: **`Lift1` は行 1 の辺を増やさない**

§34.3 で残った不安定性は `nextrel1` / `nextrel2` だけ。そこをさらに絞る。

`Lift1 X d` の第 `j` 列の行 1 の増分は `c j := if le1 X 0 j then d else 0`。
§30 の `le1_root_of_rtg0`（錐は行 0 の祖先について上方閉）より、
**`b` が錐にいれば祖先 `a` も錐にいる** ⟹ **`c b ≤ c a`**（増分は祖先のほうが大きい）。

⟹ `nextrel1` の**狭義不等式**の部分について:

    `entry (Lift1 X d) 1 a < entry (Lift1 X d) 1 b`  ⟹  `entry X 1 a < entry X 1 b`

すなわち **`Lift1` は行 0 の祖先鎖に沿った行 1 の辺を「増やさない」**。 -/

theorem Lift1_mask_ge {X : TrioSeq} {d a b : ℕ}
    (hr : ∀ l, 0 < l → l < X.length → entry X 0 0 < entry X 0 l)
    (hb : b < X.length) (hab : Relation.ReflTransGen (nextrel0 X) a b) :
    (if le1 X 0 b then d else 0) ≤ (if le1 X 0 a then d else 0) := by
  by_cases hcb : le1 X 0 b
  · rw [if_pos hcb, if_pos (le1_root_of_rtg0 hr hb hab hcb)]
  · rw [if_neg hcb]
    exact Nat.zero_le _

/-- **★★★ `Lift1` は行 0 の祖先鎖に沿った行 1 の辺を増やさない。** -/
theorem entry1_lt_of_Lift1_lt {X : TrioSeq} {d a b : ℕ}
    (hr : ∀ l, 0 < l → l < X.length → entry X 0 0 < entry X 0 l)
    (ha : a < X.length) (hb : b < X.length)
    (hab : Relation.ReflTransGen (nextrel0 X) a b)
    (h : entry (Lift1 X d) 1 a < entry (Lift1 X d) 1 b) :
    entry X 1 a < entry X 1 b := by
  rw [entry1_Lift1 ha, entry1_Lift1 hb] at h
  have hm := Lift1_mask_ge (d := d) hr hb hab
  omega

/-- ⟹ `nextrel1` の狭義不等式の部分は `Lift1` で保たれる（片側）。 -/
theorem nextrel1_lt_transfer {X : TrioSeq} {d a b : ℕ}
    (hr : ∀ l, 0 < l → l < X.length → entry X 0 0 < entry X 0 l)
    (h : nextrel1 (Lift1 X d) a b) : entry X 1 a < entry X 1 b := by
  have ha : a < X.length := by
    have := h.1
    rwa [Lift1_length] at this
  have hb : b < X.length := by
    have := h.2.1
    rwa [Lift1_length] at this
  refine entry1_lt_of_Lift1_lt hr ha hb ?_ h.2.2.2.1
  have hle0 : le0 X a b := le0_Lift1.mp h.2.2.2.2.1
  exact hle0.2.2

/-! ### 35.1 ⟹ 不安定性の最終形: **最小性の節だけ**

`nextrel1 M a b` の 5 つの連言のうち、`Lift1` で動くのは最後の 1 本だけになった:

    `a < |M|` / `b < |M|` / `a < b` … 長さ不変（`Lift1_length`）⟹ **不変**
    `entry M 1 a < entry M 1 b`      … **辺は増えない**（`entry1_lt_of_Lift1_lt`、上）
    `le0 M a b`                      … **不変**（`le0_Lift1`、§10）
    **`∀ j, a < j ∧ le0 M j b → entry M 1 b ≤ entry M 1 j`** … ここだけ動く

そして動く向きも一方向である: `b` が錐の**外**にいるとき（`c b = 0`）、祖先 `j` が
錐の**中**にいる（`c j = d`）と、最小性の要求が `entry X 1 b ≤ entry X 1 j + d` に
**緩む**。⟹ **`Lift1` は行 1 の辺を「増やさない」が、最小性が緩んで
新しい辺が立つことはある。**

⟹ **`WConvexLift1` の残る不安定性は「最小性の緩み」1 点。**
`b` が錐の外・祖先 `j` が錐の中、という配置でしか起きない。
そしてその配置は **`j` と `b` の間にブロッカー（行 1 ≤ `v` の列）がある**ことを意味する
（§30 の `le1_root_of_rtg0` の対偶）。⟹ **タイの位置と直結している。** -/


/-! ## 36. ★★★★ 課題 L118: `lowerAt`（1 列 1 段の引き下げ）が何を動かすか

`L53.lowerAt C j0`（`L53Subst.lean:3453`）は **第 `j0` 列の行 1 を 1 だけ下げる**。
`WConvexUnit` の `B` と `C` の関係はちょうどこれ。 -/

/-- 行 1 は `j0` 以外では変わらない。 -/
theorem entry1_lowerAt_ne {C : TrioSeq} {j0 j : ℕ} (h : j ≠ j0) :
    entry (L53.lowerAt C j0) 1 j = entry C 1 j := by
  rcases Nat.lt_or_ge j C.length with hj | hj
  · rw [L53.entry1_lowerAt hj, if_neg h]
    omega
  · rw [entry1_out (by rw [L53.lowerAt_length]; omega), entry1_out hj]

/-- 行 0 の木は `lowerAt` で不変（行 0 も長さも動かさない）。 -/
theorem nextrel0_lowerAt {C : TrioSeq} {j0 a b : ℕ} :
    nextrel0 (L53.lowerAt C j0) a b ↔ nextrel0 C a b := by
  unfold nextrel0
  simp only [L53.lowerAt_length, L53.entry0_lowerAt]

theorem le0_lowerAt {C : TrioSeq} {j0 a b : ℕ} :
    le0 (L53.lowerAt C j0) a b ↔ le0 C a b := by
  unfold le0
  simp only [L53.lowerAt_length]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, Relation.ReflTransGen.mono (fun _ _ h => nextrel0_lowerAt.mp h) h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, Relation.ReflTransGen.mono (fun _ _ h => nextrel0_lowerAt.mpr h) h3⟩

/-! ### 36.1 ★ (Q1) `srow` が動くのは **「行 2 = 0 かつ 行 1 = 1」の 1 列だけ**

team-lead の読みは正しい。`Trio.lean:81` の定義から:

    行 2 > 0        … `srow = 2` のまま（`lowerAt` は行 2 を動かさない）
    行 1 ≥ 2        … 下げても ≥ 1 なので `srow = 1` のまま
    行 1 = 0        … 下げても 0（ℕ の切り捨て減算）なので `srow = 0` のまま
    **行 2 = 0 かつ 行 1 = 1** … `1 → 0` で **`srow` が `1 → 0` に動く**  ← ここだけ -/

theorem srow_lowerAt {C : TrioSeq} (j0 j : ℕ)
    (h : ¬ (j = j0 ∧ entry C 2 j = 0 ∧ entry C 1 j = 1)) :
    srow (L53.lowerAt C j0) j = srow C j := by
  unfold srow
  rw [L53.entry2_lowerAt]
  by_cases h2 : 0 < entry C 2 j
  · rw [if_pos h2, if_pos h2]
  · rw [if_neg h2, if_neg h2]
    by_cases hjj : j = j0
    · subst hjj
      have hz : entry C 2 j = 0 := by omega
      have hne1 : entry C 1 j ≠ 1 := fun hc => h ⟨rfl, hz, hc⟩
      rcases Nat.lt_or_ge j C.length with hj | hj
      · rw [L53.entry1_lowerAt hj, if_pos rfl]
        by_cases hp : 0 < entry C 1 j
        · rw [if_pos (by omega), if_pos hp]
        · rw [if_neg (by omega), if_neg hp]
      · rw [entry1_out (by rw [L53.lowerAt_length]; omega), entry1_out hj]
    · rw [entry1_lowerAt_ne hjj]

/-! ### 36.2 ★ (Q2) `nextrel1` が動くのは **`j0` に触る場合だけ**

`lowerAt` が変える成分は **1 つ**（第 `j0` 列の行 1）なので、`nextrel1 a b` の 5 連言のうち
`j0` に触らないものは全部不変である:

    `a < |M|` / `b < |M|` / `a < b` … 長さ不変 ⟹ **不変**
    `le0 M a b`                     … **不変**（`le0_lowerAt`、上）
    `entry M 1 a < entry M 1 b`     … `a ≠ j0` かつ `b ≠ j0` なら **不変**
    最小性 `∀ j, a<j ∧ le0 j b → …` … `j0` がその範囲に無ければ **不変**

⟹ 下が正確な形。 -/

theorem nextrel1_lowerAt_of_avoid {C : TrioSeq} {j0 a b : ℕ}
    (ha : a ≠ j0) (hb : b ≠ j0) (hmid : ¬ (a < j0 ∧ le0 C j0 b)) :
    nextrel1 (L53.lowerAt C j0) a b ↔ nextrel1 C a b := by
  have hjne : ∀ j, a < j → le0 C j b → j ≠ j0 := by
    intro j hj1 hj2 hc
    exact hmid ⟨hc ▸ hj1, hc ▸ hj2⟩
  unfold nextrel1
  rw [L53.lowerAt_length, entry1_lowerAt_ne ha, entry1_lowerAt_ne hb]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, h4, le0_lowerAt.mp h5, fun j hj => ?_⟩
    have hres := h6 j ⟨hj.1, le0_lowerAt.mpr hj.2⟩
    rwa [entry1_lowerAt_ne (hjne j hj.1 hj.2)] at hres
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, h4, le0_lowerAt.mpr h5, fun j hj => ?_⟩
    have hj2 : le0 C j b := le0_lowerAt.mp hj.2
    rw [entry1_lowerAt_ne (hjne j hj.1 hj2)]
    exact h6 j ⟨hj.1, hj2⟩

/-! ### 36.3 ★ (Q3) `Le1` は**差の上界を含んでいません**

`Wtower2.Le1`（`:333`）:

    `Le1 A B := |A| = |B| ∧ (∀j, entry A 0 j = entry B 0 j) ∧
               (∀j, entry A 2 j = entry B 2 j) ∧ (∀j, entry A 1 j ≤ entry B 1 j)`

**行 1 の差に上界はありません。** 幅 1 は `WConvex1` の**追加の前提**
（`∀ j, entry C 1 j ≤ entry A 1 j + 1`）が持っており、それを供給するのが
`L53.sandwich_window_one`（`L53Subst.lean:3200`、`d = 1` 固定）です。
⟹ **`Le1` からは鎖の変化を抑えられません。** 抑えているのは `WConvexUnit` の
「`B` と `C` は `j0` 以外で一致し、`j0` で差はちょうど 1」という**強い前提**のほうです。

### 36.4 ⟹ 壁の高さ（課題 L118 の答え）

    **`srow`**    … 動くのは **`j0` の 1 列だけ**、しかも「行 2 = 0 かつ 行 1 = 1」の場合だけ
    **行 0 の木** … **不変**
    **`nextrel1`** … 動くのは **`j0` に触る関係だけ**（端点が `j0`、または `j0` が
                    最小性の範囲 `a < j0 ∧ le0 j0 b` に入る場合）
    **`nextrel2`** … `le1` を通して `nextrel1` の変化を受け継ぐ（行 2 自体は不変）

⟹ **「展開木が変わる」は「`j0` に触る関係だけが、高々 1 だけ動く」に落ちました。**
壁の高さは測れています。**(ii) に移る必要はありません。** -/


/-! ## 37. ★★★★★ 課題 L120: **`TowerGraft2` は `|R| = 1` だけになる**

R2 の §R98 の骨は正しく、しかも**その道具は既に緑で存在する**:

    `Wchar.aop_clause3_to_clause2`（`Wchar.lean:39`、**証明ずみ**）
      `2 ≤ |M| → domT M m → (∀ z ∈ W m, based z → graft M z ∈ X) → ∀ n ≥ 1, M⟦n⟧ ∈ X`

これは `TowerExp` の仮定 `(∀ n ≥ 1, R⟦n⟧ ∈ Wstar)` **そのもの**である。
⟹ `Wset.towerOK_of`（`Wset.lean:4513`）の節 3・`srow = 2` の枝で `|R| ≥ 2` なら
**`TowerGraft2` の代わりに `TowerExp` が使える**。

⟹ **`TowerGraft2` が要るのは `|R| = 1` の場合だけ。** -/

/-- `TowerGraft2` を `|R| = 1` に制限したもの。 -/
def TowerGraft2Single : Prop :=
  ∀ (v z m a : ℕ) (R : TrioSeq), argOK R → R.length = 1 → z ≤ 1 → 2 * v + z ≤ a →
    domT R m → srow R (R.length - 1) = 2 →
    (∀ y ∈ W m, based y → graft R y ∈ Wstar) →
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length →
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a

/-- **★★★★★ `TowerOK` は `TowerExp` ＋ `|R| = 1` の `TowerGraft2` から出る。**
（`Wset.towerOK_of` は `TowerGraft2` を**全長**で要求していた。） -/
theorem towerOK_of_exp (he : TowerExp) (h1 : TowerGraft2Single) : TowerOK := by
  intro v z u0 a R hR hRne hz1 hva AR hdR hpM n hn
  obtain ⟨m0, hm0⟩ := hdR
  have hlevpos : 0 < lev R (R.length - 1) := by rw [hm0.1]; omega
  have hsr : srow R (R.length - 1) = 1 ∨ srow R (R.length - 1) = 2 := by
    unfold srow
    unfold lev at hlevpos
    by_cases h2' : 0 < entry R 2 (R.length - 1)
    · rw [if_pos h2']; exact Or.inr rfl
    · rw [if_neg h2', if_pos (by omega)]; exact Or.inl rfl
  rcases AR with ⟨hl, hw⟩ | hop | ⟨m, hm, hd, hgr⟩
  · exfalso
    have hR1 : R.length = 1 := by
      have := List.length_pos_iff.mpr hRne
      omega
    have h := hm0.1
    rw [hR1] at h
    simp only [Nat.sub_self] at h
    omega
  · exact he v z m0 a R hR hRne hz1 hva hm0 hop hpM n hn
  · rcases hsr with h1' | h1'
    · rw [oper_cons_tower1 hR hRne hd h1' hpM]
      exact tower1_mem hR hRne hz1 hva hd h1' hgr hpM n
    · rcases Nat.lt_or_ge R.length 2 with hsm | hbig
      · have hR1 : R.length = 1 := by
          have := List.length_pos_iff.mpr hRne
          omega
        exact h1 v z m a R hR hR1 hz1 hva hd h1' hgr hpM n hn
      · exact he v z m a R hR hRne hz1 hva hd
          (aop_clause3_to_clause2 hbig hd hgr) hpM n hn

/-- ⟹ `TowerGraft2` の全長版からも当然出る（位置づけ）。 -/
theorem towerGraft2Single_of_towerGraft2 (h : TowerGraft2) : TowerGraft2Single :=
  fun v z m a R hR hR1 hz1 hva hd hi2 hgr hpM n hn =>
    h v z m a R hR (by intro hc; rw [hc] at hR1; simp at hR1) hz1 hva hd hi2 hgr hpM n hn


/-! ## 38. ★★★★★★ 課題 L120-3: **`TowerGraft2Single` は定理**（仮定ゼロ）

`|R| = 1` の塔を `oper_cons_tower2`（`Wset.lean:3231`）で展開すると

    `X⟦n+1⟧ = (0,v,z) :: graft R (Lift1 (X⟦n⟧) e)`,  `X = (0,v,z) :: R`

で、`|R| = 1` だから `R.dropLast = []` ⟹ **`graft R y` は `y` の行 0 をずらすだけ**。
そして `Lift1` も `graft` も**行 2 を動かさない**。⟹ 帰納法で

    **塔のすべての列の行 2 は `z`（根の行 2）に等しい。**

行 2 が定数なら、末尾列は行 2 で真に浅い列を持たないので**必ず孤児** ⟹ `oper` は `Pred`
⟹ 長さの帰納で根の単元まで剥け、そこは `lev = 2v+z ≤ a`。**仮定ゼロで閉じる。** -/

theorem constRow2_Lift1 {X : TrioSeq} {d k : ℕ} (h : ∀ p ∈ X, p.2.2 = k) :
    ∀ p ∈ Lift1 X d, p.2.2 = k := by
  intro p hp
  unfold Lift1 at hp
  rw [List.mem_map] at hp
  obtain ⟨j, hj, hjp⟩ := hp
  rw [List.mem_range] at hj
  rw [← hjp]
  show entry X 2 j = k
  exact h _ (entry_pair_mem (B := X) hj)

theorem graft_row2_single {R : TrioSeq} (hR1 : R.length = 1) {y : TrioSeq} {k : ℕ}
    (hy : ∀ p ∈ y, p.2.2 = k) : ∀ p ∈ graft R y, p.2.2 = k := by
  intro p hp
  have hdl : R.dropLast = [] := by
    rw [List.dropLast_eq_take, hR1]
    simp
  unfold graft at hp
  rw [hdl, List.nil_append, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact hy q hq

/-- **★★★ 行 2 が定数なら、根のレベルさえ収まれば `W`。**
末尾列は行 2 で真に浅い列を持たないので必ず孤児 ⟹ `oper` は `Pred`。 -/
theorem constRow2_mem_W_aux {c : ℕ} (hc : 1 ≤ c) :
    ∀ (N : ℕ) (M : TrioSeq) (a : ℕ), M.length ≤ N → (∀ p ∈ M, p.2.2 = c) →
      lev M 0 ≤ a → M ∈ W a := by
  intro N
  induction N with
  | zero =>
      intro M a hN _ _
      have hnil : M = [] := List.length_eq_zero_iff.mp (by omega)
      subst hnil
      exact W_nil a
  | succ N ih =>
      intro M a hN hz hlev
      rcases Nat.lt_or_ge M.length 2 with hsm | hbig
      · rcases Nat.eq_zero_or_pos M.length with h0 | hpos
        · have hnil : M = [] := List.length_eq_zero_iff.mp h0
          subst hnil
          exact W_nil a
        · obtain ⟨q, rfl⟩ := List.length_eq_one_iff.mp (by omega : M.length = 1)
          have hq : ([q] : TrioSeq) = [((q.1, q.2.1, q.2.2) : ℕ × ℕ × ℕ)] := by simp
          rw [hq]
          refine singleton_mem_W ?_
          have hl : lev ([q] : TrioSeq) 0 = 2 * q.2.1 + q.2.2 := rfl
          omega
      · have hMne : 0 < M.length := by omega
        have hlast : entry M 2 (M.length - 1) = c := by
          have hmem : M.getD (M.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) ∈ M :=
            entry_pair_mem (B := M) (by omega)
          exact hz _ hmem
        have hsr : srow M (M.length - 1) = 2 := by
          unfold srow
          rw [if_pos (by omega : 0 < entry M 2 (M.length - 1))]
        have hnz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
            entry M 2 (M.length - 1) = 0) := by
          rintro ⟨-, -, h3⟩
          omega
        have hnp : ¬ hasParent M (srow M (M.length - 1)) (M.length - 1) := by
          rw [hsr]
          rintro ⟨j0, hj0, -⟩
          rw [nextR] at hj0
          simp only [if_neg (by omega : (2 : ℕ) ≠ 0),
            if_neg (by omega : (2 : ℕ) ≠ 1)] at hj0
          have hjlt : j0 < M.length := hj0.1
          have hlt := hj0.2.2.2.1
          have : entry M 2 j0 = c :=
            hz _ (entry_pair_mem (B := M) hjlt)
          omega
        refine mem_of_oper_mem (fun n _ => ?_)
        rw [oper_eq_pred_of_noParent n (by omega) hnz hnp]
        unfold Pred
        rw [if_neg (by omega)]
        refine ih M.dropLast a (by rw [List.length_dropLast]; omega)
          (fun p hp => hz p (List.dropLast_subset M hp)) ?_
        have hd0 : ∀ i, entry M.dropLast i 0 = entry M i 0 := by
          intro i
          rw [List.dropLast_eq_take]
          exact Wset.entry_take (by omega)
        unfold lev at hlev ⊢
        rw [hd0 1, hd0 2]
        exact hlev

theorem constRow2_mem_W {M : TrioSeq} {c a : ℕ} (hz : ∀ p ∈ M, p.2.2 = c)
    (hlev : lev M 0 ≤ a) : M ∈ W a := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · exact W_mono hlev (zeroRow2_mem_Wself hz)
  · exact constRow2_mem_W_aux hc M.length M a le_rfl hz hlev

open Classical in
/-- **★★★★★★ `|R| = 1` の `TowerGraft2` は定理。** -/
theorem towerGraft2Single_holds : TowerGraft2Single := by
  intro v z m a R hR hR1 hz1 hva hd hi2 hgr hpM n hn
  have hRne : R ≠ [] := by
    intro hc
    rw [hc] at hR1
    simp at hR1
  have hzero := L53.oper_cons_zero (v := v) (z := z) hR hRne hd hpM
  have hrow2 : ∀ k, ∀ p ∈ ((((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦k⟧), p.2.2 = z := by
    intro k
    induction k with
    | zero =>
        rw [hzero]
        intro p hp
        simp at hp
    | succ k ih =>
        rw [oper_cons_tower2 (m := m) hR hRne hd hi2 hpM]
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · rfl
        · exact graft_row2_single hR1 (constRow2_Lift1 ih) p hp
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine constRow2_mem_W (c := z) (hrow2 (k + 1)) ?_
  rw [oper_cons_tower2 (m := m) hR hRne hd hi2 hpM]
  show lev (((0, v, z) : ℕ × ℕ × ℕ) :: _) 0 ≤ a
  have hl : lev (((0, v, z) : ℕ × ℕ × ℕ)
      :: graft R (Lift1 ((((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦k⟧)
        (entry R 1 (R.length - 1) - v))) 0 = 2 * v + z := by
    unfold lev
    simp [entry]
  rw [hl]
  exact hva

/-- **★★★★★★ ⟹ `TowerOK` は `TowerExp` 1 本から出る。** -/
theorem towerOK_of_towerExp (he : TowerExp) : TowerOK :=
  towerOK_of_exp he towerGraft2Single_holds


/-! ## 39. ★★★★★ 唯一の核 `TowerExp` を絞る

`Wset.Wstar`（`Wset.lean:2684`）:

    `Wstar R := argOK R → ∀ v z a, z ≤ 1 → 2*v+z ≤ a → ((0,v,z) :: R) ∈ W a`

### 39.1 ★ `|R| = 1` の `TowerExp` は**定理**（R2 の §R98-2、仮定ゼロ）

`|R| = 1` では `oper` は恒等（`Wchar.oper_of_length_one` `:31`）なので、仮定
`∀ n ≥ 1, R⟦n⟧ ∈ Wstar` は `R ∈ Wstar` そのもの。それを `(v,z,a)` に当てると
`((0,v,z) :: R) ∈ W a` が出て、`|(0,v,z) :: R| = 2` なので
`Wchar.oper_mem_of_mem`（`:63`）が展開に配る。 -/

theorem towerExp_singleton {v z a : ℕ} {R : TrioSeq} (hR : argOK R)
    (hR1 : R.length = 1) (hz1 : z ≤ 1) (hva : 2 * v + z ≤ a)
    (hop : ∀ n, 1 ≤ n → R⟦n⟧ ∈ Wstar) :
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a := by
  have hRstar : R ∈ Wstar := by
    have hres := hop 1 le_rfl
    rwa [oper_of_length_one hR1 1] at hres
  exact oper_mem_of_mem (by simp [hR1]) (hRstar hR v z a hz1 hva)

/-! ### 39.2 ★ `|R| ≥ 2` では `domT` から `R⟦n⟧ = R.dropLast`（R2 の §R98-1）

`domT R m` は末尾列が `R` の中で孤児だと言うので、`oper` は `Pred` に落ちる。 -/

theorem oper_eq_dropLast_of_domT {R : TrioSeq} {m : ℕ} (hd : domT R m)
    (hbig : 2 ≤ R.length) (n : ℕ) : R⟦n⟧ = R.dropLast := by
  have hlev := hd.1
  have hnz : ¬ (entry R 0 (R.length - 1) = 0 ∧ entry R 1 (R.length - 1) = 0 ∧
      entry R 2 (R.length - 1) = 0) := by
    rintro ⟨-, h1, h2⟩
    unfold lev at hlev
    omega
  rw [oper_eq_pred_of_noParent n (by omega) hnz hd.2]
  unfold Pred
  rw [if_neg (by omega)]

/-! ### 39.3 ⟹ `TowerExp` の最終形

`|R| = 1` は落ちた（§39.1）。`|R| ≥ 2` では仮定が **`R.dropLast ∈ Wstar`** 1 本に潰れる。 -/

/-- **`TowerExp` の残核**: `|R| ≥ 2`、仮定は `R.dropLast ∈ Wstar` だけ。 -/
def TowerExpBig : Prop :=
  ∀ (v z m a : ℕ) (R : TrioSeq), argOK R → 2 ≤ R.length → z ≤ 1 → 2 * v + z ≤ a →
    domT R m → R.dropLast ∈ Wstar →
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length →
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a

theorem towerExp_of_big (h : TowerExpBig) : TowerExp := by
  intro v z m a R hR hRne hz1 hva hd hop hpM n hn
  rcases Nat.lt_or_ge R.length 2 with hsm | hbig
  · have hR1 : R.length = 1 := by
      have := List.length_pos_iff.mpr hRne
      omega
    exact towerExp_singleton hR hR1 hz1 hva hop n hn
  · refine h v z m a R hR hbig hz1 hva hd ?_ hpM n hn
    have hres := hop 1 le_rfl
    rwa [oper_eq_dropLast_of_domT hd hbig 1] at hres

/-- **★★★★★★ `TowerOK` は `TowerExpBig` 1 本から出る。** -/
theorem towerOK_of_towerExpBig (h : TowerExpBig) : TowerOK :=
  towerOK_of_towerExp (towerExp_of_big h)

/-! ### 39.4 ⟹ 現在地

    `TowerOK` ⟸ **`TowerExpBig`** 1 本
      `∀ v z m a R, argOK R → 2 ≤ |R| → z ≤ 1 → 2v+z ≤ a →
         domT R m → **R.dropLast ∈ Wstar** →
         hasParent ((0,v,z) :: R) (srow R (|R|-1)) |R| →
         ∀ n ≥ 1, ((0,v,z) :: R)⟦n⟧ ∈ W a`

`TowerGraft2` / `LiftTie` / `LiftTieSelf` / `LiftTieCore` / `WConvex` 系は**もう要らない**。 -/


/-! ## 40. ★★★★★ 課題 L121-2/3: **行 2 の定数性は `|R| ≥ 2` でも効く**

team-lead の問い「行 2 の定数性は `|R| ≥ 2` では効かないはず（`graft R y` の胴体に
`R.dropLast` が入り、その行 2 は `z` とは限らない）」——
**そのとおりだが、`R.dropLast` の行 2 が `z` に等しいときは効く。**
`graft` の定義（`Wset.lean:66`）を開いた:

    `graft M z = M.dropLast ++ z.map (fun p => (p.1 + entry M 0 (|M|-1), p.2.1, p.2.2))`

⟹ `graft R y` の行 2 は **`R.dropLast` の行 2 と `y` の行 2 の合併**。
`|R| = 1` では `R.dropLast = []` なので条件が空虚だった（§38）。**一般には条件が要る。**

⟹ **`∀ p ∈ R.dropLast, p.2.2 = z` を足せば、`|R|` によらず塔は行 2 定数**で、
`constRow2_mem_W`（§38）がそのまま当たる。**`srow = 1` でも `srow = 2` でも。** -/

/-- `graft_row2_single`（§38）の一般化。 -/
theorem graft_row2 {R : TrioSeq} {k : ℕ} (hR2 : ∀ p ∈ R.dropLast, p.2.2 = k)
    {y : TrioSeq} (hy : ∀ p ∈ y, p.2.2 = k) : ∀ p ∈ graft R y, p.2.2 = k := by
  intro p hp
  unfold graft at hp
  rcases List.mem_append.mp hp with h | h
  · exact hR2 p h
  · rw [List.mem_map] at h
    obtain ⟨q, hq, rfl⟩ := h
    exact hy q hq

open Classical in
/-- **★★★★★ `R.dropLast` の行 2 が根の `z` に等しければ、塔は仮定ゼロで `W a`。**
`TowerExp` にも `TowerGraft2` にも同じ形で効く（graft 閉包 `hgr` を**使わない**）。 -/
theorem tower_of_row2const {v z m a : ℕ} {R : TrioSeq} (hR : argOK R)
    (hRne : R ≠ []) (hva : 2 * v + z ≤ a) (hd : domT R m)
    (hR2 : ∀ p ∈ R.dropLast, p.2.2 = z)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a := by
  have hlevpos : 0 < lev R (R.length - 1) := by rw [hd.1]; omega
  have hsr : srow R (R.length - 1) = 1 ∨ srow R (R.length - 1) = 2 := by
    unfold srow
    unfold lev at hlevpos
    by_cases h2' : 0 < entry R 2 (R.length - 1)
    · rw [if_pos h2']; exact Or.inr rfl
    · rw [if_neg h2', if_pos (by omega)]; exact Or.inl rfl
  rcases hsr with h1 | h1
  · -- srow = 1: 塔は `tow v z R n`
    have hrow2 : ∀ k, ∀ p ∈ tow v z R k, p.2.2 = z := by
      intro k
      induction k with
      | zero => intro p hp; simp [tow] at hp
      | succ k ih =>
          intro p hp
          simp only [tow, List.mem_cons] at hp
          rcases hp with rfl | hp
          · rfl
          · exact graft_row2 hR2 ih p hp
    intro n hn
    rw [oper_cons_tower1 hR hRne hd h1 hpM]
    refine constRow2_mem_W (c := z) (hrow2 n) ?_
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    show lev (tow v z R (k + 1)) 0 ≤ a
    have hl : lev (tow v z R (k + 1)) 0 = 2 * v + z := by
      simp only [tow]
      unfold lev
      simp [entry]
    rw [hl]
    exact hva
  · -- srow = 2: 塔は `oper_cons_tower2` の再帰
    have hzero := L53.oper_cons_zero (v := v) (z := z) hR hRne hd hpM
    have hrow2 : ∀ k, ∀ p ∈ ((((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦k⟧), p.2.2 = z := by
      intro k
      induction k with
      | zero =>
          rw [hzero]
          intro p hp
          simp at hp
      | succ k ih =>
          rw [oper_cons_tower2 (m := m) hR hRne hd h1 hpM]
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · rfl
          · exact graft_row2 hR2 (constRow2_Lift1 ih) p hp
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine constRow2_mem_W (c := z) (hrow2 (k + 1)) ?_
    rw [oper_cons_tower2 (m := m) hR hRne hd h1 hpM]
    show lev (((0, v, z) : ℕ × ℕ × ℕ) :: _) 0 ≤ a
    have hl : lev (((0, v, z) : ℕ × ℕ × ℕ)
        :: graft R (Lift1 ((((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦k⟧)
          (entry R 1 (R.length - 1) - v))) 0 = 2 * v + z := by
      unfold lev
      simp [entry]
    rw [hl]
    exact hva

/-! ### 40.1 ⟹ `TowerExpBig` の残核は「`R.dropLast` の行 2 が `z` でない」場合だけ -/

/-- `TowerExpBig` を「`R.dropLast` に行 2 ≠ `z` の列がある」場合に絞ったもの。 -/
def TowerExpBigRow2 : Prop :=
  ∀ (v z m a : ℕ) (R : TrioSeq), argOK R → 2 ≤ R.length → z ≤ 1 → 2 * v + z ≤ a →
    domT R m → R.dropLast ∈ Wstar →
    (∃ p ∈ R.dropLast, p.2.2 ≠ z) →
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length →
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a

open Classical in
theorem towerExpBig_of_row2 (h : TowerExpBigRow2) : TowerExpBig := by
  intro v z m a R hR hbig hz1 hva hd hdl hpM n hn
  by_cases hc : ∃ p ∈ R.dropLast, p.2.2 ≠ z
  · exact h v z m a R hR hbig hz1 hva hd hdl hc hpM n hn
  · have hR2 : ∀ p ∈ R.dropLast, p.2.2 = z := by
      intro p hp
      by_contra hne
      exact hc ⟨p, hp, hne⟩
    exact tower_of_row2const hR (by intro hcc; rw [hcc] at hbig; simp at hbig)
      hva hd hR2 hpM n hn

/-- **★★★★★★ `TowerOK` は `TowerExpBigRow2` 1 本から出る。** -/
theorem towerOK_of_towerExpBigRow2 (h : TowerExpBigRow2) : TowerOK :=
  towerOK_of_towerExpBig (towerExpBig_of_row2 h)

/-! ### 40.2 ⟹ 現在地（`TowerOK` の唯一の核）

    `∀ v z m a R, argOK R → **2 ≤ |R|** → z ≤ 1 → 2v+z ≤ a → domT R m →
       **R.dropLast ∈ Wstar** → **(∃ p ∈ R.dropLast, p.2.2 ≠ z)** →
       hasParent ((0,v,z) :: R) (srow R (|R|-1)) |R| →
       ∀ n ≥ 1, ((0,v,z) :: R)⟦n⟧ ∈ W a`

落ちた枝（全部仮定ゼロ）:

    `|R| = 1`                       … `towerExp_singleton`（`oper` が恒等）
    `R.dropLast` の行 2 ≡ `z`       … `tower_of_row2const`（塔が行 2 定数 ⟹ 末尾は必ず孤児）
    `|R| ≥ 2` の節 3                 … `Wchar.aop_clause3_to_clause2`（節 2 に落ちる）
    `|R| = 1` の節 3・`srow = 2`      … `towerGraft2Single_holds` -/


/-! ## 41. ★★★★ 課題 L122: `|R| ≥ 2` で塔の行 2 はどうなるか

`tower_of_row2const`（§40）の骨は「行 2 が定数」だけを使っている。同じ帰納を
**任意の述語 `P`** で回せる。 -/

/-- `constRow2_Lift1` の述語版。 -/
theorem row2_pred_Lift1 {X : TrioSeq} {d : ℕ} {P : ℕ → Prop}
    (h : ∀ p ∈ X, P p.2.2) : ∀ p ∈ Lift1 X d, P p.2.2 := by
  intro p hp
  unfold Lift1 at hp
  rw [List.mem_map] at hp
  obtain ⟨j, hj, hjp⟩ := hp
  rw [List.mem_range] at hj
  rw [← hjp]
  show P (entry X 2 j)
  exact h _ (entry_pair_mem (B := X) hj)

open Classical in
/-- **★★★ 塔の行 2 は `{z} ∪ row2(R.dropLast)` の外に出ない。**
（`tower_of_row2const` は `P := (· = z)` の場合。） -/
theorem tower_row2_pred {v z m : ℕ} {R : TrioSeq} {P : ℕ → Prop} (hR : argOK R)
    (hRne : R ≠ []) (hd : domT R m)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length)
    (hz : P z) (hR2 : ∀ p ∈ R.dropLast, P p.2.2) :
    ∀ n, ∀ p ∈ ((((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧), P p.2.2 := by
  have hgraft : ∀ {y : TrioSeq}, (∀ p ∈ y, P p.2.2) →
      ∀ p ∈ graft R y, P p.2.2 := by
    intro y hy p hp
    unfold graft at hp
    rcases List.mem_append.mp hp with h | h
    · exact hR2 p h
    · rw [List.mem_map] at h
      obtain ⟨q, hq, rfl⟩ := h
      exact hy q hq
  have hlevpos : 0 < lev R (R.length - 1) := by rw [hd.1]; omega
  have hsr : srow R (R.length - 1) = 1 ∨ srow R (R.length - 1) = 2 := by
    unfold srow
    unfold lev at hlevpos
    by_cases h2' : 0 < entry R 2 (R.length - 1)
    · rw [if_pos h2']; exact Or.inr rfl
    · rw [if_neg h2', if_pos (by omega)]; exact Or.inl rfl
  rcases hsr with h1 | h1
  · intro n
    rw [oper_cons_tower1 hR hRne hd h1 hpM]
    induction n with
    | zero => intro p hp; simp [tow] at hp
    | succ k ih =>
        intro p hp
        simp only [tow, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hz
        · exact hgraft ih p hp
  · have hzero := L53.oper_cons_zero (v := v) (z := z) hR hRne hd hpM
    intro n
    induction n with
    | zero =>
        rw [hzero]
        intro p hp
        simp at hp
    | succ k ih =>
        rw [oper_cons_tower2 (m := m) hR hRne hd h1 hpM]
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hz
        · exact hgraft (row2_pred_Lift1 ih) p hp

/-! ### 41.1 ⚠ `|R| ≥ 2` で剥き落としが**効かなくなる理由**（team-lead の問いへの回答）

`graft R y = R.dropLast ++ (y を行 0 でずらしたもの)` なので、塔は

    `X⟦k+1⟧ = (0,v,z) :: R.dropLast ++ (ずらした X⟦k⟧)`

⟹ **行 2 の列は `z, (R.dropLast の行 2), z, (R.dropLast の行 2), …` と周期的**になる。
`|R| = 2`（`R.dropLast = [(d,b,c)]`）なら **`z, c, z, c, …`**。

    `c = z` … **定数** ⟹ `tower_of_row2const`（§40）で**無料**
    `c ≠ z` … **定数でない**

そして剥き落とし（`oper = Pred`）が回るには、**どの接尾辞でも末尾列が行 2 の孤児**
である必要がある ⟹ **行 2 が非増加**でなければならない。周期 `z, c, z, c, …` が
非増加になるのは `c = z` のときだけ。

⟹ **`c ≠ z` では剥き落としは原理的に効かない。** とくに `z < c` なら、末尾列
（行 2 = `c`）に対して**根（行 2 = `z`）が行 2 の親の候補**になる。

### 41.2 ★ ⟹ `TowerExpBig` の本体（1 行）

> **`|R| ≥ 2` かつ `R.dropLast` の行 2 が `z` と違うとき、塔の行 2 は周期的になり、
> 末尾列は行 2 の孤児でなくなる。⟹ `oper` は `Pred` にならず、塔は伸び続ける。
> そこを支えるのは `Aop` の節 3（graft）しかない。**

そして塔の胴体の先頭 `(0,v,z) :: R.dropLast` は仮定 `R.dropLast ∈ Wstar` から `W a` だが、
**そこに後続を `W_add` で繋ぐ道は死んでいる**（`not_rsum_of_root_mem`、§14:
先頭は根（行 0 = 0）を含み、後続は `entry R 0 (|R|-1) ≥ 1` だけ深い）。

⟹ **経路 D（`Wstar`）の残核は、経路 C（`GX` / `CoreCap` ⟺ `GraftAll`）と同じ
「graft 閉包」1 点に合流した。** -/


/-! ## 42. ★★★★ 課題 L122: `|R|` の長さ帰納で graft 閉包は作れるか

team-lead の指摘は正しい: **`TowerExpBigRow2` は `R.dropLast ∈ Wstar` を仮定として
持っており、それが §22 で「`CoreCap` には無い」と書いた尾の `W` 導出そのもの。**
⟹ 経路 D から入るほうが測度がある。

そこで「節 3 の義務を `R.dropLast ∈ Wstar` と `|R|` の帰納から作れるか」を見た。

### 42.1 義務の形は **`graft (根つきブロック) y`**（`Wset.graft_cons` `:2545`）

    `graft ((0,v',z') :: R) y = (0,v',z') :: graft R y`

⟹ 節 3 の義務 `graft R y ∈ Wstar`、すなわち
`((0,v',z') :: graft R y) ∈ W a'` は、**`graft ((0,v',z') :: R) y ∈ W a'` と同じ**。

⟹ **「主ブロック `(0,v',z') :: R` を `y` で graft したものが `W a'`」**という形。 -/

theorem graft_cons_obligation {v z : ℕ} {R y : TrioSeq} (hRne : R ≠ []) :
    (((0, v, z) : ℕ × ℕ × ℕ) :: graft R y) = graft (((0, v, z) : ℕ × ℕ × ℕ) :: R) y :=
  (graft_cons hRne).symm

/-! ### 42.2 ⚠ **`|R|` の帰納が閉じない理由（1 行）**

主ブロック `(0,v,z) :: R` について `Aop` の節 3 が使えれば、その義務がそのまま出る。
ところが節 3 は **`domT ((0,v,z) :: R) m`**、すなわち
**その末尾列が `(0,v,z) :: R` の中で孤児**であることを要求する。

**しかし `TowerExpBig` の仮定は `hasParent ((0,v,z) :: R) (srow R (|R|-1)) |R|`
—— つまり「根が末尾列を復活させる」**である。両者は正面から矛盾する
（`domT` の第 2 連言が `¬hasParent`、`Wset.lean:61`）。

> **⟹ 主ブロックには節 3 が使えない。使えるのは節 2（展開して降りる）だけで、
> 展開すると `oper_cons_tower1/2` の塔になり、その胴体にまた `graft R (…)` が現れる。
> ⟹ 長さ `|R|` は減らない。**

これは §16（`CoreCap` の残核でも節 3 が死ぬ）と**まったく同じ形**である。
違いは、**経路 D では `R.dropLast ∈ Wstar` という尾の導出が手元にある**こと。

### 42.3 ⟹ 「復活」がこの証明の唯一の結び目

    節 3 が使える  ⟺ 末尾列が孤児（`domT`）
    塔が起きる     ⟺ 根が末尾列を復活させる（`hasParent`）
    **この 2 つは排他**。⟹ 塔の場面では節 3 が使えず、節 2 で降りるしかない。
    そして節 2 で降りると胴体にまた `graft` が出る。

`Xbar.graft_assoc`（`Xbar.lean:469`）`graft (graft M y) w = graft M (graft y w)` は
**graft の合成を 1 本にまとめる**ので、塔の入れ子は `graft R (graft R (…))` の形に
畳める。⟹ **測度になるのは `R` の長さではなく、`y` 側の `W m` の導出**である
（`m < u` で段が下がる唯一の節が節 3 だから）。

**⟹ 次のエージェントへ**: `R.dropLast ∈ Wstar` を「`y` 側の導出」に変換できるか。
`graft_assoc` で入れ子を畳んだうえで、`W m` の `A2'` 帰納に載せるのが筋のはず。 -/


/-! ## 43. ★★★★★★ 課題 L123: **`srow = 1` の塔は `shTower` そのもの**

team-lead の (3)「`graft` の結合律のような補題はないか」への答えは
**`Xbar.graft_assoc`（`Xbar.lean:469`）`graft (graft M y) w = graft M (graft y w)`**（既存）。
だが**もっと直接的な形が出た**。

`Wset.graft_eq_shift`（`:2737`）: `graft M y = M.dropLast ++ shiftr01 (entry M 0 (|M|-1)) 0 y`。
これを `Wset.tow`（`:2780`）`tow v z R (k+1) = (0,v,z) :: graft R (tow v z R k)` に入れると

    `tow (k+1) = ((0,v,z) :: R.dropLast) ++ shiftr01 e 0 (tow k)`,  `e = entry R 0 (|R|-1)`

⟹ **`tow v z R n = shTower ((0,v,z) :: R.dropLast) e n`**（`Wtower2.shTower` `:1688`）。

⟹ **`srow = 1` の `TowerExp` は `ShiftTowerClosed`（`Wtower2.lean:1763`）そのもの。**
しかも土台 `Q = (0,v,z) :: R.dropLast` は

    `Q ∈ W a`      … 仮定 `R.dropLast ∈ Wstar` から**そのまま**
    側条件         … `entry Q 0 0 = 0` なので `∀ p ∈ Q, entry Q 0 0 ≤ p.1` は**自明**
    強い側条件     … `argOK R.dropLast` から `∀ j ≥ 1, 0 < entry Q 0 j` ＝ **`ShiftTowerClosedS` の形**

**⟹ `TowerExp` の `srow = 1` 枝は `ShiftTowerClosedS`（`Wtower2.lean:1771`）に完全に一致する。** -/

theorem shTower_cons (Q : TrioSeq) (e : ℕ) :
    ∀ n : ℕ, shTower Q e (n + 1) = Q ++ shiftr01 e 0 (shTower Q e n) := by
  intro n
  induction n with
  | zero =>
      rw [shTower_zero, shiftr01_nil, List.append_nil]
      exact shTower_one Q e
  | succ n ih =>
      rw [shTower_succ Q e (n + 1)]
      conv_lhs => rw [ih]
      rw [List.append_assoc]
      congr 1
      have he : (n + 1) * e = e + n * e := by
        rw [Nat.succ_mul, Nat.add_comm]
      rw [he, ← shiftr01_comp, ← shiftr01_append, ← shTower_succ Q e n]

/-- **★★★★★ `srow = 1` の塔は `shTower` そのもの。** -/
theorem tow_eq_shTower (v z : ℕ) (R : TrioSeq) :
    ∀ n : ℕ, tow v z R n
      = shTower (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast)
          (entry R 0 (R.length - 1)) n := by
  intro n
  induction n with
  | zero => simp [tow, shTower]
  | succ n ih =>
      show ((0, v, z) : ℕ × ℕ × ℕ) :: graft R (tow v z R n) = _
      rw [graft_eq_shift, ih, shTower_cons, List.cons_append]

open Classical in
/-- **★★★★★★ `srow = 1` の `TowerExp` は `ShiftTowerClosedS` から出る。** -/
theorem towerExp1_of_shiftTowerClosedS (hst : ShiftTowerClosedS)
    {v z m a : ℕ} {R : TrioSeq} (hR : argOK R) (hRne : R ≠ [])
    (hz1 : z ≤ 1) (hva : 2 * v + z ≤ a) (hd : domT R m)
    (hi1 : srow R (R.length - 1) = 1) (hdl : R.dropLast ∈ Wstar)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a := by
  intro n _
  rw [oper_cons_tower1 hR hRne hd hi1 hpM, tow_eq_shTower]
  refine hst a (entry R 0 (R.length - 1)) n _ (hdl (argOK_dropLast hR) v z a hz1 hva) ?_
  intro j hj1 hj2
  have h0 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 0 0 = 0 := by
    simp [entry]
  rw [h0]
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [List.length_cons] at hj2
  have hk : k < R.dropLast.length := by omega
  have hmem : R.dropLast.getD k ((0, 0, 0) : ℕ × ℕ × ℕ) ∈ R.dropLast :=
    entry_pair_mem (B := R.dropLast) hk
  have hpos := argOK_dropLast hR _ hmem
  show 0 < entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 0 (k + 1)
  have he : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 0 (k + 1)
      = entry R.dropLast 0 k := by
    unfold entry
    simp
  rw [he]
  exact hpos

/-! ### 43.1 ⟹ `TowerExpBigRow2` の `srow = 2` 枝だけが残る

    `srow = 1` … **`ShiftTowerClosedS`**（`Wtower2.lean:1771`、`CORES.md` の既知の核）に一致
    `srow = 2` … `oper_cons_tower2` の塔（`Lift1` が入るので `shTower` ではない）

⚠ `ShiftTowerClosedS` は `CORES.md:38` で「`WCat` / `SubstClosedG` から出る」と
記録されている既知の核。**新しい核ではないが、`TowerExp` の半分がそこに一致することは
今日まで書かれていなかった。** -/


/-! ## 44. 課題 L124: 所属を開く道具と、それが測度にならない理由

### 44.1 (Q1) **所属を開く道具はあります**

    `Wset.lfpS_unfold`（`:166`）  最小不動点の展開
    **`Wset.A1`（`:243`）**       `Aset W u (W u) = W u`
                                 ⟹ `rw [← A1 a] at h` で `h : S ∈ W a` を
                                    `h : Aop W a (W a) S` に開ける
                                 （`Wchar.oper_mem_of_mem` `:63` が実際にそうしている）
    `Wset.A1_intro`（`:255`）     逆向き（作る側）
    `Wset.A2'`（`:251`）          **`W u ⊆ X`** を示す帰納（最小不動点の帰納法）

### 44.2 ⚠ (Q2) **開いても測度になりません**

`A1` で開けるのは **1 段だけ**で、出てくるのは**同じ `W a`** についての `Aop` である。
整礎な再帰にするには `A2'`（`W u ⊆ X` 向き）が要るが、それを使うには
**性質 `X` が `Aop` で閉じている**ことを示す必要がある。

いま開きたいのは `((0,v',z') :: R.dropLast) ∈ W a'` で、`A2'` を回すと導出は
**その列 `N` を歩く**。ところが目標の塔は **`R`（＝ `R.dropLast ++ [末尾]`）で決まって**おり、
`Aop` の再帰は `N` と `R` の関係を保たない（`N⟦n⟧` はもう `R.dropLast` の形をしていない）。

⟹ **「`R.dropLast` の導出で `R` の塔を組む」形の帰納は立たない。**
これを立てようとしたものが `Wset.Wstar_closed`（`:4372`）そのもので、
**その残債務がまさに `TowerOK`** である。⟹ **循環。**

⚠ ここは §22.3 で `CoreCap` について書いたのと**同じ構造**である。違いは、
`TowerExpBigRow2` では `R.dropLast ∈ Wstar` という**仮定の形で**尾の情報を持っている点だが、
`Wstar` は Π 命題（`∀ v' z' a', … → cons ∈ W a'`）なので**それ自体には導出木が無い**。
中の `∈ W a'` を開くと上の問題に戻る。

### 44.3 ★ H12 の §185（`le1` の接頭辞局所性）は **既に証明ずみ**

    **`Wset.le1_take`（`Wset.lean:908`）**
      `l ≤ |X| → b < l → (le1 (X.take l) a b ↔ le1 X a b)`

H12 が 2245 万件で測った「`le1 X 0 j ⟺ le1 (X.take k) 0 j`（`j < k ≤ |X|`）」**そのもの**で、
**無条件**（`argOK` を使わない）。H12 の「定義からの理由」も正しく、
`Wset.rtg1_take_mp` / `rtg1_take_mpr`（`:890` / `:900`）がその中身。

⟹ **測る必要はありませんでした。** 私も §5 で `Lift1_take`（`:995`）を使ったとき、
その土台がこの補題であることに触れていなかった。**記録しておく。**

### 44.4 ⟹ 現在地（正直な報告）

    `TowerExpBigRow2` の `srow = 1` 枝 … **`ShiftTowerClosedS` に一致**（§43、新事実）
    `srow = 2` 枝                     … 残り
    `|R|` の帰納                      … **死んでいる**（§42）
    `R.dropLast ∈ Wstar` の導出の帰納 … **立たない**（上、`Wstar_closed` と循環）

⟹ **`TowerExpBigRow2` を割る新しい測度は、今日の道具では見つかりませんでした。**
⚠「原理的に不可能」ではない（教訓 13）。**今ある道具立てでは立たない**、の報告。 -/


/-! ## 45. ★★★★★ 課題 L125: **塔の段は無料。難所は `Wself` だけ**

team-lead の観察を定義から確かめた。**正しい。**

`shTower Q e (n+1) = Q ++ shiftr01 e 0 (shTower Q e n)`（§43 `shTower_cons`）なので
**塔の根は `Q` の根のまま**。⟹ `lev (shTower Q e (n+1)) 0 = lev Q 0`。

そして `Wtower2.mem_Wself_iff`（`:2990`、**無条件・緑**）
`M ∈ W u ↔ (M ∈ Wself ∧ lev M 0 ≤ u)` により

> **`shTower Q e n ∈ W u` ⟺ `shTower Q e n ∈ Wself`（`lev Q 0 ≤ u` のもとで）。
> ⟹ 段の勘定は完全に無料。残るのは `Wself` の閉包 1 点。** -/

theorem entry_shTower_root {Q : TrioSeq} (hQne : Q ≠ []) (e n i : ℕ) :
    entry (shTower Q e (n + 1)) i 0 = entry Q i 0 := by
  rw [shTower_cons]
  exact entry_append_left Q _ (List.length_pos_iff.mpr hQne)

theorem lev_shTower_root {Q : TrioSeq} (hQne : Q ≠ []) (e n : ℕ) :
    lev (shTower Q e (n + 1)) 0 = lev Q 0 := by
  unfold lev
  rw [entry_shTower_root hQne, entry_shTower_root hQne]

/-- **`ShiftTowerClosedS` の `Wself` 版**（段を落とした形）。 -/
def ShTowerSelf : Prop :=
  ∀ (e n : ℕ) (Q : TrioSeq), Q ∈ Wself → Q ≠ [] →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
    shTower Q e n ∈ Wself

/-- **★★★★★ 段は無料**: `ShiftTowerClosedS` は `Wself` の閉包 1 点に落ちる。 -/
theorem shiftTowerClosedS_of_self (h : ShTowerSelf) : ShiftTowerClosedS := by
  intro u e n Q hQ hw
  by_cases hQne : Q = []
  · subst hQne
    have : shTower ([] : TrioSeq) e n = [] := by
      unfold shTower
      simp
    rw [this]
    exact W_nil u
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [shTower_zero]
      exact W_nil u
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain ⟨hself, hlev⟩ := (mem_Wself_iff u Q).mp hQ
      refine (mem_Wself_iff u _).mpr ⟨h e (k + 1) Q hself hQne hw, ?_⟩
      rw [lev_shTower_root hQne]
      exact hlev

/-! ### 45.1 ⟹ `srow = 1` 枝は **`Wself` の塔閉包 1 点**

§43 の `towerExp1_of_shiftTowerClosedS` と合わせると:

    `TowerExp` の `srow = 1` 枝  ⟸ `ShiftTowerClosedS` ⟸ **`ShTowerSelf`**

そして `ShTowerSelf` には**段が一切現れない**。R2 が実測した
「段は木のどこでも消費されない」（170 万ノード、破れ 0）と一致する。

### 45.2 ★ `srow = 2` 側でも段は無料

`Wset.entry0_Lift1`（`:948`）`entry (Lift1 X d) 0 i = entry X 0 i` ——
**`Lift1` は行 0 を動かさない**（team-lead の未確認点。開いて確認した。正しい）。
そして `graft R y = R.dropLast ++ shiftr01 e 0 y` は行 0 を `e` ずらすだけ。

⟹ `oper_cons_tower2` の塔 `(0,v,z) :: graft R (Lift1 (X⟦k⟧) e')` も

    根は `(0,v,z)`（深さ 0）、それ以外は `R.dropLast`（`argOK` で深さ ≥ 1）と
    `e = entry R 0 (|R|-1) ≥ 1` だけずれた列 ⟹ **深さ ≥ 1**

で、**根が変わらない ⟹ `lev = 2v+z ≤ a`** ⟹ `mem_Wself_iff` で**段は無料**。
（`lev` は行 1・行 2 だけを見るので、`Lift1` が根の行 1 を上げないことも要る ——
塔の根は `graft` の外にある `(0,v,z)` なので影響を受けない。）

⟹ **`srow = 1` でも `srow = 2` でも、段の勘定は完全に無料。難所は `Wself` の閉包だけ。**

### 45.3 ⚠ `ShTowerSelf` も `W_add` では組めない

§131（team-lead）の算術は `Wself` 版にもそのまま当たる:

    `shTower Q e (n+1) = shTower Q e n ++ shiftr01 (n*e) 0 Q`（`Wtower2.shTower_succ`）
    `A` は `k=0` の塊として `Q` を含み、`Q` の根は深さ 0（`Q = (0,v,z) :: …`）
    `entry B 0 0 = 0 + n*e = n*e ≥ 1`（`n ≥ 1`, `e ≥ 1`）
    ⟹ `not_rsum_of_root_mem`（§14）が当たり **`rsum` は破れる**

⟹ **`Wself` の側を `Aop` の節 2／節 3 で直接攻めるしかない。** -/


/-! ## 46. ★★★★★ 課題 L125: **`srow = 2` 側でも段は無料**（塔全体で `Wself` 1 点）

§45.2 の散文を定理にする。塔は `srow` によらず `(0,v,z) :: …` の形なので、
根の `lev` は `2v+z` のまま。⟹ `Wtower2.mem_Wself_iff` で段が落ちる。 -/

theorem lev_cons_root (v z : ℕ) (L : TrioSeq) :
    lev (((0, v, z) : ℕ × ℕ × ℕ) :: L) 0 = 2 * v + z := by
  unfold lev
  simp [entry]

open Classical in
/-- **★★★★★ 塔は `Wself` かどうかだけ**（`srow = 1` でも `srow = 2` でも、段は無料）。 -/
theorem tower_mem_W_iff_self {v z m a : ℕ} {R : TrioSeq} (hR : argOK R)
    (hRne : R ≠ []) (hva : 2 * v + z ≤ a) (hd : domT R m)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length)
    {n : ℕ} (hn : 1 ≤ n) :
    (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a
      ↔ (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ Wself := by
  have hlevpos : 0 < lev R (R.length - 1) := by rw [hd.1]; omega
  have hsr : srow R (R.length - 1) = 1 ∨ srow R (R.length - 1) = 2 := by
    unfold srow
    unfold lev at hlevpos
    by_cases h2' : 0 < entry R 2 (R.length - 1)
    · rw [if_pos h2']; exact Or.inr rfl
    · rw [if_neg h2', if_pos (by omega)]; exact Or.inl rfl
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hlev : lev ((((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦k + 1⟧) 0 = 2 * v + z := by
    rcases hsr with h1 | h1
    · rw [oper_cons_tower1 hR hRne hd h1 hpM]
      show lev (tow v z R (k + 1)) 0 = 2 * v + z
      simp only [tow]
      exact lev_cons_root v z _
    · rw [oper_cons_tower2 (m := m) hR hRne hd h1 hpM]
      exact lev_cons_root v z _
  rw [mem_Wself_iff]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, by rw [hlev]; exact hva⟩

/-! ### 46.1 ⟹ `TowerExpBigRow2` は **`Wself` の 1 文**

    `∀ v z m a R, argOK R → 2 ≤ |R| → z ≤ 1 → 2v+z ≤ a → domT R m →
       R.dropLast ∈ Wstar → (∃ p ∈ R.dropLast, p.2.2 ≠ z) → hasParent … →
       ∀ n ≥ 1, ((0,v,z) :: R)⟦n⟧ **∈ Wself**`

⟹ **`a` と `2v+z ≤ a` は結論から消える**（`tower_mem_W_iff_self`）。
`srow = 1` でも `srow = 2` でも同じ。**段の勘定はどこにも残っていない。**

### 46.2 ★ H12 の問い「`z = 0` のとき実際に何が効いているか」への回答（1 行）

> **`z = 0` では剥き落とし（孤児性）は使っていません。`constRow2_mem_W`（§38）が
> `c = 0` のとき `Wtower2.zeroRow2_mem_Wself`（`:3011`）に分岐するからです。**

`constRow2_mem_W` の場合分け:

    `c = 0` … **`zeroRow2_mem_Wself hz`（行 2 ≡ 0 ⟹ `Wself`）＋ `W_mono`**  ← `z = 0` はここ
    `c ≥ 1` … `constRow2_mem_W_aux`（末尾は行 2 の孤児 ⟹ `Pred` で剥ける）  ← `z = 1` はここ

⟹ H12 の実測（`z=1` は 100% 孤児、`z=0` は 0〜44%）と**完全に整合**する。
`z = 0` で孤児性が成り立たないのは正しく、**そこでは別の定理を使っている**。
（`srow = 0` の枝の `snoc_flat_root` は `CoreCap` 側（§12.2）の話で、
`tower_of_row2const` とは無関係。H12 の推測はそこだけ外れています。）

### 46.3 ⟹ `|R| = 1` に `srow = 2` が無いこと（H12 の実測）との整合

H12 の実測「`|R| = 1` では `srow = 2` の非孤児が 0 件」は、私の `towerGraft2Single_holds`
（`|R| = 1` の **`srow = 2`** の `TowerGraft2`）が**空虚に真**だという意味ではない。
そちらは `TowerGraft2` の場面（節 3、`domT R m` ＋ 根が復活）で、H12 が測ったのは
`TowerExpBigRow2` の場面（節 2）である。**母集団が違う。**

⚠ ただし H12 の結論「**`|R| = 1` の証明を延長しても `srow = 2` の枝は出てこない**」は
`TowerExpBig` については正しい。私も `tower_of_row2const`（§40）で `|R|` 一般に
伸ばしたときに、`R.dropLast` の行 2 という**新しい条件**が要ることを確認している。 -/


/-! ## 47. ⚠ 自己訂正 ＋ 課題 L126: `srow = 2` の塔は `operTower`

### 47.1 ⚠ **§45 は `L47W.lean` の再発明でした**

`grep shTower lean/L47W.lean` で確認した（**書く前にやるべきだった**）:

    **`L47W.lev_shTower`（`L47W.lean:129`）** ＝ 私の `lev_shTower_root`（§45）
    **`L47W.shiftTowerClosed_iff_wself`（`:155`）**
      `ShiftTowerClosed ↔ ∀ e n Q, Q ∈ Wself → (∀ p ∈ Q, entry Q 0 0 ≤ p.1) →
                            shTower Q e n ∈ Wself`
      ＝ 私の `shiftTowerClosedS_of_self`（§45）の内容。しかも **`↔`（両向き）**
    `L47W.shTower_prefix`（`:110`）/ `shTower_nil`（`:93`）/ `shTower_zeroRow2`（`:97`）
    `L47W.shiftTowerClosed_of_zeroRow2`（`:137`）… 行 2 ≡ 0 なら `(TOW)` は定理

⟹ **「段は無料、難所は `Wself` だけ」は課題 L48 の時点で既に書かれていた。**
私の §45 は `ShiftTowerClosedS`（狭義側条件）版という差しかない。
**H12 に「測る前に grep」と言った直後に、私が書く前に grep しませんでした。**

### 47.2 ★ 課題 L126: `srow = 2` の塔は `shTower` **ではない**

`Wset.oper_cons_tower2` に `graft_eq_shift` を入れると（`srow = 1` と同じ手順）

    `X⟦n+1⟧ = ((0,v,z) :: R.dropLast) ++ shiftr01 d 0 (**Lift1** (X⟦n⟧) e')`
      `d = entry R 0 (|R|-1)`,  `e' = entry R 1 (|R|-1) - v`

`shTower_cons`（§43）は `shTower Q e (n+1) = Q ++ shiftr01 e 0 (shTower Q e n)` なので、
**差は `Lift1 · e'` が 1 段ごとに挟まること**だけ。⟹ 下の `operTower` が正確な形。 -/

/-- **`srow = 2` の塔**（`shTower` の各段に `Lift1 · e` を挟んだもの）。 -/
noncomputable def operTower (Q : TrioSeq) (d e : ℕ) : ℕ → TrioSeq
  | 0 => []
  | n + 1 => Q ++ shiftr01 d 0 (Lift1 (operTower Q d e n) e)

open Classical in
/-- **★★★★★ `srow = 2` の塔は `operTower` そのもの。** -/
theorem tower2_eq_operTower {v z m : ℕ} {R : TrioSeq} (hR : argOK R)
    (hRne : R ≠ []) (hd : domT R m) (hi2 : srow R (R.length - 1) = 2)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    ∀ n, (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧
      = operTower (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast)
          (entry R 0 (R.length - 1)) (entry R 1 (R.length - 1) - v) n := by
  intro n
  induction n with
  | zero =>
      rw [L53.oper_cons_zero (v := v) (z := z) hR hRne hd hpM]
      rfl
  | succ k ih =>
      rw [oper_cons_tower2 (m := m) hR hRne hd hi2 hpM, ih, graft_eq_shift,
        ← List.cons_append]
      rfl

/-! ### 47.3 ⟹ `srow = 1` と `srow = 2` の差は **`Lift1` 1 つ**

    `srow = 1` … `tow v z R n = shTower Q d n`            （§43、`Lift1` 無し）
    `srow = 2` … `X⟦n⟧ = operTower Q d e' n`               （上、各段に `Lift1 · e'`）
      どちらも `Q = (0,v,z) :: R.dropLast`, `d = entry R 0 (|R|-1)`

⟹ **`e' = 0` なら `Lift1 X 0 = X`（`Wset.Lift1_zero`）で `operTower = shTower`。**
`e' = entry R 1 (|R|-1) - v` なので、**`entry R 1 (|R|-1) ≤ v` のとき両者は一致**する。
ところが `srow = 2` の場面では `L53.tower2_vw` が **`v < entry R 1 (|R|-1)`** を与える
（`domT` ＋ `hasParent` から自動）⟹ **`e' ≥ 1`。一致しない。**

⟹ **`srow = 2` が `srow = 1` より真に難しい理由が 1 行で出た:
`srow = 2` では根の復活が行 1 の狭義増加を強制するので、リフト量 `e'` が必ず正になる。**

### 47.4 ⟹ タイの問題がここで**戻ってきます**

`Lift1 W e'` が一様シフト `shiftr01 0 e'` に潰れるのは、根の `le1` 錐が全体のとき
（`Lcone.le1_zero_iff`）＝ **ブロッカー（行 1 ≤ `v` の列）が無いとき**。
潰れれば `operTower` は行 0・行 1 の両方を一様にずらす塔になり、`shTower` と同じ扱いができる。

⟹ **`|R| ≥ 2` の `srow = 2` 枝では、`Q = (0,v,z) :: R.dropLast` に
「行 1 が `v` 以下の列があるか」がふたたび効く。**
午後に削った `liftStage_of_strict`（狭義、仮定ゼロ）/ `liftStage_of_noTie`（無タイ、仮定ゼロ）/
`liftStage_of_zeroRow2`（行 2 ≡ 0、仮定ゼロ、§32）は **ここで再利用できる可能性が高い**。
（`LiftTie` 系は `TowerOK` の核ではなくなったが、**道具としては生きている**。） -/


/-! ## 48. ★★★★★★ 課題 L127: **予測は正しい。しかも既存の補題 2 本で出ます**

team-lead の予測:

> **`(shTower Q e n)⟦m⟧ = shTower Q e (n-1) ++ shiftr01 ((n-1)*e) 0 (Q⟦m⟧)`**
> 「塔の展開は、最後のブロックだけを展開する」

**正しい。** しかも道具は 2 本とも既存・緑:

    **`L53.comm_of_hasParentInBlock`（`L53Subst.lean:922`）**
      `(A ++ N)⟦n⟧ = A ++ N⟦n⟧`（`N` の中に親があれば `A` に逃げない）
    **`Wset.oper_shiftr01`（`Wset.lean:434`）**
      `(shiftr01 d 0 W)⟦n⟧ = shiftr01 d 0 (W⟦n⟧)`（行 0 の一様シフトは展開と可換）

`shTower_succ` で `shTower Q e (n+1) = shTower Q e n ++ shiftr01 (n*e) 0 Q` と割り、
`A := shTower Q e n`、`N := shiftr01 (n*e) 0 Q` に当てるだけ。 -/

theorem srow_shiftr01 (d : ℕ) (W : TrioSeq) (j : ℕ) :
    srow (shiftr01 d 0 W) j = srow W j := by
  unfold srow
  rw [entry2_shiftr01, entry1_shiftr01]

theorem hasParentInBlock_shiftr01 {d : ℕ} {Q : TrioSeq}
    (h : L53.HasParentInBlock Q) : L53.HasParentInBlock (shiftr01 d 0 Q) := by
  unfold L53.HasParentInBlock at h ⊢
  rw [shiftr01_length, srow_shiftr01, hasParent_shiftr01]
  exact h

/-- **★★★★★★ 塔の展開は「最後のブロックだけ」を展開する。** -/
theorem oper_shTower {Q : TrioSeq} (hQne : Q ≠ []) (hQ2 : Q.length - 1 ≠ 0)
    (hzQ : ¬(entry Q 0 (Q.length - 1) = 0 ∧ entry Q 1 (Q.length - 1) = 0 ∧
      entry Q 2 (Q.length - 1) = 0))
    (hblk : L53.HasParentInBlock Q) (e n m : ℕ) :
    (shTower Q e (n + 1))⟦m⟧ = shTower Q e n ++ shiftr01 (n * e) 0 (Q⟦m⟧) := by
  have hQlen : 0 < Q.length := List.length_pos_iff.mpr hQne
  have hNne : shiftr01 (n * e) 0 Q ≠ [] := by
    intro hc
    have hl := congrArg List.length hc
    rw [shiftr01_length] at hl
    exact hQne (List.length_eq_zero_iff.mp hl)
  have hN2 : (shiftr01 (n * e) 0 Q).length - 1 ≠ 0 := by
    rw [shiftr01_length]
    exact hQ2
  have hNz : ¬(entry (shiftr01 (n * e) 0 Q) 0
        ((shiftr01 (n * e) 0 Q).length - 1) = 0 ∧
      entry (shiftr01 (n * e) 0 Q) 1 ((shiftr01 (n * e) 0 Q).length - 1) = 0 ∧
      entry (shiftr01 (n * e) 0 Q) 2 ((shiftr01 (n * e) 0 Q).length - 1) = 0) := by
    rw [shiftr01_length]
    rintro ⟨h0, h1, h2⟩
    rw [entry1_shiftr01] at h1
    rw [entry2_shiftr01] at h2
    rw [entry0_shiftr01 (by omega : Q.length - 1 < Q.length)] at h0
    exact hzQ ⟨by omega, h1, h2⟩
  rw [shTower_succ,
    L53.comm_of_hasParentInBlock m hNne hN2 hNz (hasParentInBlock_shiftr01 hblk),
    oper_shiftr01]

/-! ### 48.1 ⟹ `ShTowerSelf` の帰納の形

`Aop` の節 2（`mem_of_oper_mem`）で `shTower Q e (n+1) ∈ Wself` を示すには
`∀ m ≥ 1, (shTower Q e (n+1))⟦m⟧ ∈ W (lev Q 0)` が要る。上の定理で右辺は

    **`shTower Q e n ++ shiftr01 (n*e) 0 (Q⟦m⟧)`**

`Q ∈ Wself` から `Q⟦m⟧ ∈ W (lev Q 0)`（`Wchar.oper_mem_of_mem`、緑）、
`shTower Q e n` は帰納法の仮定。**⟹ 両端は揃う。**

⚠ **しかしそれを繋ぐのは連結**であり、`rsum` は破れる（§14、`not_rsum_of_root_mem`:
`A = shTower Q e n` は `k=0` の塊として `Q` を含み根の行 0 = 0、
`entry (shiftr01 (n*e) 0 (Q⟦m⟧)) 0 0 = n*e ≥ 1`）。
⟹ **team-lead の但し書きどおり、右辺の連結で詰まる。**

### 48.2 ★ ⟹ しかし `shTower` の形に閉じ込められます

`shTower Q e n ++ shiftr01 (n*e) 0 (Q⟦m⟧)` を見ると:

    前半 `shTower Q e n` … **`Q` を `e` ずつずらした `n` 個のブロック**
    後半               … **`Q⟦m⟧` を `n*e` ずらしたもの**

⟹ **「同じ 1 単位の反復」ではないが、「`Q` の `n` 個のブロック ＋ `Q⟦m⟧` の 1 個」**
という形で、**周期の 1 単位が `Q` から `Q⟦m⟧` に変わるのは最後の 1 個だけ**。

⟹ **`ShTowerSelf` の帰納は `n` について回り、各段で足されるのは
`shiftr01 (n*e) 0 (Q⟦m⟧)` 1 ブロックだけ**である。
⟹ **`Q⟦m⟧` は `Q` より「小さい」（`W` の導出が 1 段浅い）**ので、
**測度は `(n, Q の導出)` の辞書式**になるはず。

⚠ ただし **`shTower Q e n ++ (1 ブロック)` を `W` の中で作る操作**が要る。
それが `WCat` / `rsum` で死んでいる ⟹ **`Aop` の節 3（graft）で作るしかない**。
`shTower Q e n` の末尾は `Q` の末尾（`n-1` 番目のブロックの最終列）なので、
**そこが孤児かどうか**が節 3 の使えるかどうかを決める。**次はそこを見る。** -/


/-! ## 49. ★★★★ 課題 L128: ブロッカーが無ければ `operTower` は**一様 2 方向シフト塔**

`Wtower2.Lift1_eq_shiftr1_of_window`（`:107`）:

    根が行 0 で狭義最浅かつ行 1 でも狭義最小 ⟹ **`Lift1 X d = shiftr01 0 d X`**

⟹ `operTower` の再帰 `Q ++ shiftr01 d 0 (Lift1 T e)` は
`Q ++ shiftr01 d e T` に潰れる（行 0 も行 1 も**一様**にずれる塔）。 -/

theorem shiftr01_comp01 (b c : ℕ) (X : TrioSeq) :
    shiftr01 b 0 (shiftr01 0 c X) = shiftr01 b c X := by
  unfold shiftr01
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro p _
  simp only [Function.comp_apply]
  refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> simp

/-- **★★ collapse ステップ**: 窓条件があれば `operTower` の 1 段は
`shiftr01 d e` に潰れる。 -/
theorem operTower_step_collapse {Q T : TrioSeq} {d e : ℕ}
    (hr : ∀ l, 0 < l → l < T.length → entry T 0 0 < entry T 0 l)
    (hw : ∀ l, 0 < l → l < T.length → entry T 1 0 < entry T 1 l) :
    Q ++ shiftr01 d 0 (Lift1 T e) = Q ++ shiftr01 d e T := by
  rw [Lift1_eq_shiftr1_of_window hr hw e, shiftr01_comp01]

/-- **行 0 と行 1 の両方を一様にずらす塔**（`shTower` の 2 方向版）。 -/
def shTower2 (Q : TrioSeq) (d e : ℕ) (n : ℕ) : TrioSeq :=
  (List.range n).flatMap fun k => shiftr01 (k * d) (k * e) Q

@[simp] theorem shTower2_zero (Q : TrioSeq) (d e : ℕ) : shTower2 Q d e 0 = [] := rfl

@[simp] theorem shTower2_one (Q : TrioSeq) (d e : ℕ) : shTower2 Q d e 1 = Q := by
  unfold shTower2
  simp

theorem shTower2_succ (Q : TrioSeq) (d e n : ℕ) :
    shTower2 Q d e (n + 1)
      = shTower2 Q d e n ++ shiftr01 (n * d) (n * e) Q := by
  unfold shTower2
  rw [List.range_succ, List.flatMap_append]
  simp

theorem shiftr01_comp2 (b c b' c' : ℕ) (X : TrioSeq) :
    shiftr01 b c (shiftr01 b' c' X) = shiftr01 (b + b') (c + c') X := by
  unfold shiftr01
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro p _
  simp only [Function.comp_apply]
  refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> simp <;> omega

theorem shiftr01_append' (d0 d1 : ℕ) (A B : TrioSeq) :
    shiftr01 d0 d1 (A ++ B) = shiftr01 d0 d1 A ++ shiftr01 d0 d1 B :=
  shiftr01_append d0 d1 A B

/-- **`shTower_cons` の 2 方向版。** -/
theorem shTower2_cons (Q : TrioSeq) (d e : ℕ) :
    ∀ n : ℕ, shTower2 Q d e (n + 1) = Q ++ shiftr01 d e (shTower2 Q d e n) := by
  intro n
  induction n with
  | zero =>
      rw [shTower2_zero, shiftr01_nil, List.append_nil]
      exact shTower2_one Q d e
  | succ n ih =>
      rw [shTower2_succ Q d e (n + 1)]
      conv_lhs => rw [ih]
      rw [List.append_assoc]
      congr 1
      have hd : (n + 1) * d = d + n * d := by rw [Nat.succ_mul, Nat.add_comm]
      have he : (n + 1) * e = e + n * e := by rw [Nat.succ_mul, Nat.add_comm]
      rw [hd, he, ← shiftr01_comp2, ← shiftr01_append', ← shTower2_succ Q d e n]

/-! ### 49.1 ⟹ 残るのは窓条件の伝播だけ

`operTower Q d e (n+1) = Q ++ shiftr01 d 0 (Lift1 (operTower Q d e n) e)` と
`shTower2 Q d e (n+1) = Q ++ shiftr01 d e (shTower2 Q d e n)` を見比べると、
**`operTower_step_collapse` を各段で使えれば `operTower = shTower2`。**

必要な窓条件（`T = operTower Q d e n` について）:

    (a) 根が行 0 で狭義最浅 … `Q = (0,v,z) :: (argOK)` と `d ≥ 1` から従うはず
    (b) 根が行 1 で狭義最小 … **`Q` にブロッカー（行 1 ≤ `v` の列）が無い**ことと
        `e ≥ 1`（塔の根が `Lift1` で `v → v+e` と上がる）から従うはず

⚠ **(a)(b) の伝播はまだ証明していません。** 添字の場合分け（`entry (A ++ B)` の分解）が
要るので分量があります。**そこが L128 の残りです。**

⟹ 落ちれば `operTower Q d e n = shTower2 Q d e n`（**`Lift1` が消えた一様 2 方向シフト塔**）で、
`srow = 2` 枝が `srow = 1` 枝と**同じ種類の対象**になります。
残るのは **`Q` にブロッカーがある場合**＝ **`LiftTie` の場面**。 -/


/-! ## 50. ★★★★★ 課題 L128 の残り: **窓条件は伝播する**

`shTower2 Q d e n` について (a)(b) を `n` の帰納で示す。
`shTower2_cons` で `Q ++ shiftr01 d e (shTower2 Q d e n)` に割り、
前半は `Q` の仮定、後半は帰納法の仮定 ＋ シフト量（`d ≥ 1`, `e ≥ 1`）で出る。 -/

theorem entry1_shift {d0 d1 : ℕ} {W : TrioSeq} {p : ℕ} (hp : p < W.length) :
    entry (shiftr01 d0 d1 W) 1 p = entry W 1 p + d1 := by
  show ((shiftr01 d0 d1 W).getD p (0, 0, 0)).2.1
    = ((W.getD p (0, 0, 0)).2.1 : ℕ) + d1
  rw [shiftr01_getD hp]

theorem shTower2_root_entry {Q : TrioSeq} (hQne : Q ≠ []) (d e i n : ℕ) :
    entry (shTower2 Q d e (n + 1)) i 0 = entry Q i 0 := by
  rw [shTower2_cons]
  exact entry_append_left Q _ (List.length_pos_iff.mpr hQne)

theorem shTower2_length (Q : TrioSeq) (d e n : ℕ) :
    (shTower2 Q d e n).length = n * Q.length := by
  induction n with
  | zero => simp [shTower2]
  | succ n ih =>
      rw [shTower2_succ, List.length_append, shiftr01_length, ih, Nat.succ_mul]

/-- **★★★ 窓条件は塔の各段に伝播する。** -/
theorem shTower2_window {Q : TrioSeq} (hQne : Q ≠ []) {d e v : ℕ}
    (hd : 1 ≤ d) (he : 1 ≤ e) (hv : entry Q 1 0 = v)
    (h0 : ∀ l, 1 ≤ l → l < Q.length → 0 < entry Q 0 l)
    (h1 : ∀ l, 1 ≤ l → l < Q.length → v < entry Q 1 l) :
    ∀ n, (∀ l, 1 ≤ l → l < (shTower2 Q d e n).length →
              0 < entry (shTower2 Q d e n) 0 l)
       ∧ (∀ l, 1 ≤ l → l < (shTower2 Q d e n).length →
              v < entry (shTower2 Q d e n) 1 l)
       ∧ (∀ l, l < (shTower2 Q d e n).length →
              v ≤ entry (shTower2 Q d e n) 1 l) := by
  have hQlen : 0 < Q.length := List.length_pos_iff.mpr hQne
  intro n
  induction n with
  | zero =>
      refine ⟨fun l _ hl => ?_, fun l _ hl => ?_, fun l hl => ?_⟩ <;>
        · rw [shTower2_length] at hl; omega
  | succ n ih =>
      obtain ⟨ih0, ih1, ihv⟩ := ih
      have hsplit : shTower2 Q d e (n + 1) = Q ++ shiftr01 d e (shTower2 Q d e n) :=
        shTower2_cons Q d e n
      have hlen : (shTower2 Q d e (n + 1)).length
          = Q.length + (shTower2 Q d e n).length := by
        rw [hsplit, List.length_append, shiftr01_length]
      refine ⟨fun l hl1 hl2 => ?_, fun l hl1 hl2 => ?_, fun l hl2 => ?_⟩
      · rcases Nat.lt_or_ge l Q.length with hlt | hge
        · rw [hsplit, entry_append_left Q _ hlt]
          exact h0 l hl1 hlt
        · obtain ⟨j, rfl⟩ : ∃ j, l = Q.length + j := ⟨l - Q.length, by omega⟩
          rw [hlen] at hl2
          rw [hsplit, entry_append_right]
          rw [entry0_shiftr01 (by rw [shTower2_length] at hl2 ⊢; omega)]
          omega
      · rcases Nat.lt_or_ge l Q.length with hlt | hge
        · rw [hsplit, entry_append_left Q _ hlt]
          exact h1 l hl1 hlt
        · obtain ⟨j, rfl⟩ : ∃ j, l = Q.length + j := ⟨l - Q.length, by omega⟩
          rw [hlen] at hl2
          have hj : j < (shTower2 Q d e n).length := by omega
          rw [hsplit, entry_append_right, entry1_shift hj]
          have := ihv j hj
          omega
      · rcases Nat.lt_or_ge l Q.length with hlt | hge
        · rw [hsplit, entry_append_left Q _ hlt]
          rcases Nat.eq_zero_or_pos l with rfl | hlpos
          · rw [hv]
          · exact le_of_lt (h1 l hlpos hlt)
        · obtain ⟨j, rfl⟩ : ∃ j, l = Q.length + j := ⟨l - Q.length, by omega⟩
          rw [hlen] at hl2
          have hj : j < (shTower2 Q d e n).length := by omega
          rw [hsplit, entry_append_right, entry1_shift hj]
          have := ihv j hj
          omega

/-- **★★★★★★ ブロッカーが無ければ `operTower` は `shTower2` に潰れる。** -/
theorem operTower_eq_shTower2 {Q : TrioSeq} (hQne : Q ≠ []) {d e v : ℕ}
    (hd : 1 ≤ d) (he : 1 ≤ e) (hr0 : entry Q 0 0 = 0) (hv : entry Q 1 0 = v)
    (h0 : ∀ l, 1 ≤ l → l < Q.length → 0 < entry Q 0 l)
    (h1 : ∀ l, 1 ≤ l → l < Q.length → v < entry Q 1 l) :
    ∀ n, operTower Q d e n = shTower2 Q d e n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show Q ++ shiftr01 d 0 (Lift1 (operTower Q d e n) e) = _
      rw [ih, shTower2_cons]
      refine operTower_step_collapse ?_ ?_
      · intro l hl0 hl
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · rw [shTower2_length] at hl; omega
        · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          rw [shTower2_root_entry hQne, hr0]
          exact (shTower2_window hQne hd he hv h0 h1 (k + 1)).1 l hl0 hl
      · intro l hl0 hl
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · rw [shTower2_length] at hl; omega
        · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          rw [shTower2_root_entry hQne, hv]
          exact (shTower2_window hQne hd he hv h0 h1 (k + 1)).2.1 l hl0 hl

/-! ### 50.1 ⟹ **`srow = 2` 枝は「ブロッカーがあるか」だけになった**

    ブロッカー無し … `operTower Q d e n = shTower2 Q d e n`（**`Lift1` が消える**）
                     ⟹ `srow = 1` 枝の `shTower` と**同じ種類の対象**
    ブロッカー有り … 残り ＝ **`LiftTie` の場面**

`Q = (0,v,z) :: R.dropLast` なので、ブロッカーの有無は
**`R.dropLast` に行 1 ≤ `v` の列があるか**である。
`d = entry R 0 (|R|-1) ≥ 1` は `argOK R` から、`e = entry R 1 (|R|-1) - v ≥ 1` は
`L53.tower2_vw` から**どちらも自動**。 -/


/-! ## 51. ★★★★★ 課題 L129 と、H12/R2 の閉じた形の食い違いへの回答

### 51.1 ★ (team-lead の問い) **`Lift1 X (k*e)` と `Lift1^k X e` は同じです**

`Wset.Lift1_Lift1`（`:1230`）`Lift1 (Lift1 X t) s = Lift1 X (t + s)` の帰納で出る。
⟹ **H12 の `Lift1 (…) (k·δ1)` と R2 の `Lift1^j (…)` は同値。どちらでも使えます。** -/

/-- `Lift1` を `k` 回かけるのは 1 回で `k * e` 持ち上げるのと同じ。 -/
theorem Lift1_iterate (X : TrioSeq) (e : ℕ) :
    ∀ k : ℕ, (fun Y => Lift1 Y e)^[k] X = Lift1 X (k * e) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Lift1_Lift1]
      congr 1
      rw [Nat.succ_mul, Nat.add_comm]

/-! ### 51.2 ★ 課題 L129: **`zle1 R` を足すと `z = 1 ∧ srow = 2` は空虚**

R2 の算術（`|R| ≤ 4` の全数 460,441 件で 0 件）を Lean で確定する。
既存の `L53.tower2_zr`（`L53Subst.lean:2380`）が `z < entry R 2 (|R|-1)` を与えるので、
`zle1 R`（`Wset.lean:2470`、`∀ p ∈ M, p.2.2 ≤ 1`）と合わせて `z ≤ 1` と矛盾する。 -/

theorem tower2_not_z1_of_zle1 {v m : ℕ} {R : TrioSeq} (hRne : R ≠ [])
    (hz : zle1 R) (hd : domT R m) (hi2 : srow R (R.length - 1) = 2)
    (hpM : hasParent (((0, v, 1) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) : False := by
  have hlt := L53.tower2_zr (v := v) (z := 1) hRne hd hi2 hpM
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hmem : R.getD (R.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ) ∈ R :=
    entry_pair_mem (B := R) (by omega)
  have hle : entry R 2 (R.length - 1) ≤ 1 := hz _ hmem
  omega

/-- ⟹ `zle1 R` のもとでは `srow = 2` の塔は `z = 0` に限られる。 -/
theorem tower2_z_zero_of_zle1 {v z m : ℕ} {R : TrioSeq} (hRne : R ≠ [])
    (hz1 : z ≤ 1) (hz : zle1 R) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) : z = 0 := by
  rcases Nat.lt_or_ge z 1 with h | h
  · omega
  · exfalso
    have hz1' : z = 1 := by omega
    subst hz1'
    exact tower2_not_z1_of_zle1 hRne hz hd hi2 hpM

/-! ### 51.3 ⟹ `zle1` つきの `TowerOK`

`Wset.TowerOK` / `Wset.Wstar_closed`（`Wset.lean:4372`）は共有ファイルなので触らない。
代わりに **`zle1 R` を足した版**を定義し、`z = 1` の枝が空虚であることを記録する。 -/

/-- `TowerExpBigRow2` に `zle1 R` を足した版。 -/
def TowerExpBigZ : Prop :=
  ∀ (v z m a : ℕ) (R : TrioSeq), argOK R → 2 ≤ R.length → z ≤ 1 → zle1 R →
    2 * v + z ≤ a → domT R m → R.dropLast ∈ Wstar →
    (∃ p ∈ R.dropLast, p.2.2 ≠ z) →
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length →
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a

/-- **★ `zle1` つきの場面では `srow = 2` なら必ず `z = 0`。**
⟹ `z = 1` の `srow = 2` の枝は**空虚**（R2 の実測 0/460,441 の算術）。 -/
theorem towerExpBigZ_srow2_z_zero {v z m : ℕ} {R : TrioSeq}
    (hRne : R ≠ []) (hz1 : z ≤ 1) (hz : zle1 R) (hd : domT R m)
    (hi2 : srow R (R.length - 1) = 2)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) : z = 0 :=
  tower2_z_zero_of_zle1 hRne hz1 hz hd hi2 hpM

/-! ### 51.4 ⚠ `zle1` を本線に入れるには `Wset.lean` の変更が要る

`Wset.TowerOK`（`:4365` 付近）にも `Wset.Wstar_closed`（`:4372`）にも `zle1` の仮定が無い。
消費側（`Wset.mem_of_Aclosed` `:4642` / `mem_Wstar` `:4646` / `mem_of_Aclosed_aux` `:4558`）は
**`zle1` を持っている**（R2 の調査）ので、`Wstar_closed` の内部で `zle1 R` を引き回せれば
足せるはず。⚠ **`Wset.lean` は共有ファイルなので私は触りません。team-lead の判断待ち。**

上の `tower2_not_z1_of_zle1` / `tower2_z_zero_of_zle1` は**その判断が出たらすぐ使える形**で
用意してある（どちらも `zle1 R` だけを追加仮定に取る）。

⟹ 足せれば **`srow = 2` の枝は `z = 0` に限られ**、私の `tower_of_row2const`（§40）の
「`R.dropLast` の行 2 ≡ `z` ＝ `0`」枝は **`zeroRow2_mem_Wself` で無料**になる。
残るのは **`R.dropLast` に行 2 = 1 の列がある**場合だけ。 -/


/-! ## 52. ★★★★★★ 課題 L130: **ブロッカーがある場合の残核は `LiftTieCore` そのもの**

H12 の閉じた形（ブロック `k` ＝ `Lift1 (shiftr01 (k·d) 0 B) (k·e)`）に、
午後に削った**仮定ゼロ**の道具を当てる。

まず `Lift1` と行 0 の一様シフトは**可換**（`Core.le1_shiftr01`（`:3470`）と
`Core.entry0_shiftr01`（`:3401`）/ `entry1_shiftr01`（`:3407`）/ `entry2_shiftr01`（`:3416`）から）。
⟹ **ブロックの所属は `B = (0,v,z) :: R.dropLast` についての `Lift1` に帰着する。**
`B` は cons 形なので、`liftStage_of_strict` / `liftStage_of_noTie` /
`liftTie_case_tieFree` / `liftStage_of_zeroRow2` が**そのまま当たる**。 -/

theorem Lift1_shiftr01 (d e : ℕ) (X : TrioSeq) :
    Lift1 (shiftr01 d 0 X) e = shiftr01 d 0 (Lift1 X e) := by
  classical
  have hlen : (Lift1 (shiftr01 d 0 X) e).length
      = (shiftr01 d 0 (Lift1 X e)).length := by
    rw [Lift1_length, shiftr01_length, shiftr01_length, Lift1_length]
  refine List.ext_getElem hlen ?_
  intro i hi1 _
  rw [Lift1_length, shiftr01_length] at hi1
  have hiS : i < (shiftr01 d 0 X).length := by rw [shiftr01_length]; exact hi1
  have hiL : i < (Lift1 X e).length := by rw [Lift1_length]; exact hi1
  have e0 : entry (Lift1 (shiftr01 d 0 X) e) 0 i
      = entry (shiftr01 d 0 (Lift1 X e)) 0 i := by
    rw [entry0_Lift1, entry0_shiftr01 hi1, entry0_shiftr01 hiL, entry0_Lift1]
  have e1 : entry (Lift1 (shiftr01 d 0 X) e) 1 i
      = entry (shiftr01 d 0 (Lift1 X e)) 1 i := by
    rw [entry1_Lift1 hiS, entry1_shiftr01, entry1_shiftr01, entry1_Lift1 hi1,
      le1_shiftr01]
  have e2 : entry (Lift1 (shiftr01 d 0 X) e) 2 i
      = entry (shiftr01 d 0 (Lift1 X e)) 2 i := by
    rw [entry2_Lift1, entry2_shiftr01, entry2_shiftr01, entry2_Lift1]
  rw [← entry_triple (X := Lift1 (shiftr01 d 0 X) e)
      (by rw [Lift1_length, shiftr01_length]; exact hi1),
    ← entry_triple (X := shiftr01 d 0 (Lift1 X e))
      (by rw [shiftr01_length, Lift1_length]; exact hi1), e0, e1, e2]

/-- **★★★ ブロックの所属は `B` についての `(WL)` に帰着する。** -/
theorem block_mem_of_liftStage {B : TrioSeq} {m d e : ℕ}
    (h : Lift1 B e ∈ W (m + 2 * e)) :
    Lift1 (shiftr01 d 0 B) e ∈ W (m + 2 * e) := by
  rw [Lift1_shiftr01]
  exact W_shift h d

/-! ### 52.1 ★ ブロッカーがある場合の 3 分割（`B = (0,v,z) :: R'`）

**ブロッカー** ＝ 根以外で行 1 ≤ `v` の列。それがあるとき、さらに 3 つに割れる:

    (α) **タイが無い**（`∀ p ∈ R', p.2.1 ≠ v`。ブロッカーは全部 `< v`）
        ⟹ **`L53.liftStage_of_noTie`（仮定ゼロ）** で無料
    (β) **タイがあり `TieFree`**（実測 6.1%）
        ⟹ **`L53.liftTie_case_tieFree`（既存定理）** で無料
    (γ) ⛔ **行 2 ≡ 0 … 構造的に空虚**（H12 の 0 件、証明つき）。下の §52.4 を見よ
    (δ) 残り ＝ **タイあり ∧ `¬TieFree`** ＝ **`LiftTieCore`（§29）そのもの**

⟹ **`TowerExpBig` のブロック所属の残核は、午後に `CoreCap` 側で削った
`LiftTieCore` と同じ命題である。** -/

open Classical in
/-- **★★★★★★ ブロックの所属は `LiftTieCore` に帰着する。** -/
theorem block_mem_of_liftTieCore (h : LiftTieCore) {v z d : ℕ} {R' : TrioSeq}
    (hargOK : argOK R')
    (hB : (((0, v, z) : ℕ × ℕ × ℕ) :: R') ∈ W (2 * v + z)) (e : ℕ) :
    Lift1 (shiftr01 d 0 (((0, v, z) : ℕ × ℕ × ℕ) :: R')) e
      ∈ W (2 * v + z + 2 * e) := by
  refine block_mem_of_liftStage ?_
  exact liftSelf_of_unit (liftTieSelfUnit_of_core h) e v z R' hargOK hB

/-! ### 52.2 ⟹ **両路線は本当に 1 点で出会いました**

    経路 C（`CoreCap` ⟺ `GraftAll`）… 残核は `LiftTieCore`（§29、`d=1`・自己段・タイ・`¬TieFree`）
    経路 D（`TowerOK` ⟸ `TowerExpBig`）
      ブロック 1 個を `W` に入れる … **`LiftTieCore`**（上、緑）
      ブロックを繋ぐ               … `ShiftTowerClosedS`（§43）／`shTower2` 版

⟹ **(1) は同じ命題。(2) だけが経路 D 固有。**
そして (2) は `L47W.shiftTowerClosed_iff_wself`（緑・両向き）で **`Wself` の閉包 1 点**に落ちる。

⚠ **(2) が `WCat` に落ちるかは未確認。** `CORES.md:38` は `ShiftTowerClosedS ⟸ WCat` と
**上流**を記録しているだけで、逆（`ShiftTowerClosedS → WCat`）の補題は `grep` で見つからない。
⟹ **`ShiftTowerClosedS` は `WCat` より弱い可能性が残っている。**
`WCat` は任意の `A ++ B` を要求するが、`shTower` は**同じ 1 単位の反復**しか要求しないので、
**弱いほうに賭ける価値がある**と思う。

### 52.3 ⚠ 残核の割合について（H12 の数字への回答）

H12 の「ブロッカーあり ＝ 残核が `|R|` とともに 37.5% → 83.2% と単調増加」は受け取った。
⚠ ただし **上の 3 分割（α)(β)(γ) がその中をさらに削る**ので、
**「ブロッカーあり」＝ 残核ではない。**

    ブロッカーあり ∧ タイ無し   … (α) で無料
    ブロッカーあり ∧ タイ ∧ `TieFree` … (β) で無料
    行 2 ≡ 0                    … (γ) で無料（ブロッカーの有無に依らない）

⟹ **H12 には「ブロッカーあり」をさらに (α)(β)(γ)(δ) に割って数えてもらうのが正確**。
測るべきは **(δ) の割合**である。 -/



/-! ### 52.4 ⛔ **自己訂正: (γ)「行 2 ≡ 0」は構造的に空虚**

H12 が数え（0 件）、しかも証明した。母集団の前提は
**`∃ p ∈ R.dropLast, p.2.2 ≠ z`**（`TowerExpBigRow2` の定義、§40.1）なので:

    `z = 1` … 根 `(0,v,1)` の行 2 が `1 ≠ 0` ⟹ **行 2 ≡ 0 は不可能**
    `z = 0` … 前提が `∃ p ∈ R.dropLast, p.2.2 ≠ 0` を要求 ⟹ **行 2 ≡ 0 は不可能**

⟹ **`liftStage_of_zeroRow2`（§32）は `TowerExpBigRow2` の場合分けに 1 件も寄与しない。**
私が §52.1 で (γ) として挙げたのは**誤り**だった。**分母を数えていなかった。**

⚠ **`tower_of_row2const`（§40、行 2 ≡ `z`）のほうは有効**である。混同しないこと:

    `liftStage_of_zeroRow2`（§32）… **`= 0` 限定**・主語は**持ち上げ**・段が `+2d`
    `tower_of_row2const`（§40）  … **`= z`**・主語は**塔そのもの**・段は `a` のまま・
                                  `srow = 1` でも `2` でも

### 52.5 ⚠ 自己訂正 2: (α) の範囲

`L53.liftStage_of_noTie` の前提は **`∀ p ∈ R, p.2.1 ≠ v`（`R` 全体、`R.dropLast` ではない）**、
結論は**持ち上げ**（段 `+2d`）であって塔ではない。
⟹ 「ブロッカーが `< v` だけ」＝「タイが無い」であって、
**一様シフトに潰れる（`Lift1` が消える）のはブロッカーが 1 本も無いときだけ**である
（§50 `operTower_eq_shTower2` の前提が `v < entry Q 1 l` ＝ ブロッカー無し）。**2 つは別条件。**

### 52.6 ⚠ 自己訂正 3: (β) には `v ≥ 1` が要る

`L53.liftTie_case_tieFree`（`L53Subst.lean:2615`）は **`1 ≤ entry X 1 0`（＝ `v ≥ 1`）**を要求する。
⟹ **`v = 0` では使えない。** §26 の `LiftTieSelfOpen` / §29 の `LiftTieCore` は
`¬(1 ≤ v ∧ TieFree …)` という形にしてあるので**そこは正しく扱っている**が、
場合分けの割合を数えるときは `v = 0` と `v ≥ 1` を分ける必要がある。 -/

/-! ## 53. ⛔ 課題 L131: **`zle1` は `Wstar_closed` に通せません**（変更前の判定）

team-lead が `Wset.lean` の変更を承認したが、**着手前に実現可能性を確かめたところ通らない。**
`Wset.lean` は**触っていない。**

### 53.1 ★ 止まる場所（`Wset.lean:4629`）

`Wset.mem_of_Aclosed_aux`（`:4556`）の中で `hX`（＝ `Wstar_closed` の実体）は

    `Wset.lean:4629`   `exact A2' (fun M' h => hX (maxlev Q) M' h) hP`

と使われる。**`A2'` は `W (maxlev Q) ⊆ X` を示す最小不動点の帰納**なので、
`hX` は **`W (maxlev Q)` のすべての元 `M'`** に適用される。
⟹ **`M'` が `zle1` である保証は無い。**

### 53.2 ⚠ しかも `zle1` は `Aop` で**安定ではありません**（本質的な理由）

`X' := {M | zle1 M → M ∈ X}` で `A2'` を回そうとすると、`Aop W u X' M` から
`zle1 M → M ∈ X` を示す必要がある。節ごとに見ると:

    節 1 … 底。問題なし
    節 2 `∀ n ≥ 1, M⟦n⟧ ∈ X'` … **`Wset.zle1_oper`（`:2472`、緑）**が
          `zle1 M → zle1 (M⟦n⟧)` を与えるので**通る**
    **節 3 `∀ y ∈ W m, based y → graft M y ∈ X'`** … `y` は **`W m` 全体**を走る。
          `graft M y` の行 2 には `y` の行 2 が入る（`graft_eq_shift`、`:2737`）ので
          **`zle1 (graft M y)` は `zle1 y` を要求するが、`y ∈ W m` からは出ない**
          ⟹ **通らない**

> **⟹ `zle1` は `Aop` の節 3 で壊れる。`W m` に `zle1` の制限が無いから。**
> **⟹ `Wstar_closed` は `zle1` でない `R` についても成り立たなければならない。**

### 53.3 ⟹ 判定

**L131 は今の `Aop` の定義のもとでは実現不可能。**
`zle1` を通すには **`W` そのものを `zle1` 付きで定義し直す**（`Aop` の節 3 の
`Wfam m` を `zle1` 付きの族に置き換える）必要があり、それは
**`Wset.lean` の全面的な作り直し**（`W` の定義から下流の全定理）になる。

⚠ **「原理的に不可能」ではない**（教訓 13）。**今の `W` の定義のもとでは通らない**、の報告。
`W` を張り替える設計変更なら可能だが、**規模が違う**（`Wset.lean` 4760 行の土台）。

### 53.4 ⟹ 代わりに使える形

`zle1` を**核の側に足す**のは自由である（`Wstar_closed` を変えないので）:

    `TowerExpBigZ`（§51.3）… `TowerExpBigRow2` に `zle1 R` を足した版

だが **`TowerExpBigZ → TowerOK` は出ない**（`Wstar_closed` が `zle1` 無しの `R` にも
`TowerOK` を要求するので）。⟹ **核として使えない。**

⟹ **`tower2_not_z1_of_zle1` / `tower2_z_zero_of_zle1`（§51、緑）は、
`zle1` が既知の場面での道具としてのみ有効**である。 -/


/-! ## 54. ★★★★★ 課題 L132: **(2) の `shTower2` 版**

`shTower2` も根が `Q` の根のまま（`shTower2_cons`）なので、`L47W` と同じ理由で
**段は無料**。⟹ `Wself` の閉包 1 文にできる。 -/

theorem lev_shTower2_root {Q : TrioSeq} (hQne : Q ≠ []) (d e n : ℕ) :
    lev (shTower2 Q d e (n + 1)) 0 = lev Q 0 := by
  have hQlen : 0 < Q.length := List.length_pos_iff.mpr hQne
  unfold lev
  rw [shTower2_cons, entry_append_left Q _ hQlen, entry_append_left Q _ hQlen]

/-- **`ShTowerSelf` の 2 方向シフト版**（段が現れない）。 -/
def ShTower2Self : Prop :=
  ∀ (d e n : ℕ) (Q : TrioSeq), Q ∈ Wself → Q ≠ [] →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 1 0 < entry Q 1 j) →
    shTower2 Q d e n ∈ Wself

theorem entry_cons_succ {p : ℕ × ℕ × ℕ} {L : TrioSeq} (i k : ℕ) :
    entry (p :: L) i (k + 1) = entry L i k := by
  unfold entry
  simp

open Classical in
/-- **★★★★★ ブロッカーが無い `srow = 2` の枝は `ShTower2Self` だけで出る。** -/
theorem towerExp2_of_shTower2Self (h : ShTower2Self) {v z m a : ℕ} {R : TrioSeq}
    (hR : argOK R) (hRne : R ≠ []) (hz1 : z ≤ 1) (hva : 2 * v + z ≤ a)
    (hd : domT R m) (hi2 : srow R (R.length - 1) = 2)
    (hdl : R.dropLast ∈ Wstar)
    (hnb : ∀ p ∈ R.dropLast, v < p.2.1)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a := by
  intro n hn
  have hdlarg : argOK R.dropLast := argOK_dropLast hR
  have hQne : (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) ≠ [] := by simp
  have hQlev : lev (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 0 = 2 * v + z :=
    lev_cons_root v z _
  have hQself : (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) ∈ Wself := by
    show (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast)
      ∈ W (lev (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 0)
    rw [hQlev]
    exact hdl hdlarg v z (2 * v + z) hz1 le_rfl
  have hQ00 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 0 0 = 0 := by
    simp [entry]
  have hQ10 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 1 0 = v := by
    simp [entry]
  have hQ0 : ∀ l, 1 ≤ l → l < (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast).length →
      0 < entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 0 l := by
    intro l hl1 hl2
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    simp only [List.length_cons] at hl2
    rw [entry_cons_succ]
    have hk : k < R.dropLast.length := by omega
    have := hdlarg _ (entry_pair_mem (B := R.dropLast) hk)
    have hEq : entry R.dropLast 0 k
        = (R.dropLast.getD k ((0, 0, 0) : ℕ × ℕ × ℕ)).1 := rfl
    omega
  have hQ1 : ∀ l, 1 ≤ l → l < (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast).length →
      v < entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 1 l := by
    intro l hl1 hl2
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    simp only [List.length_cons] at hl2
    rw [entry_cons_succ]
    have hk : k < R.dropLast.length := by omega
    have := hnb _ (entry_pair_mem (B := R.dropLast) hk)
    have hEq : entry R.dropLast 1 k
        = (R.dropLast.getD k ((0, 0, 0) : ℕ × ℕ × ℕ)).2.1 := rfl
    omega
  have hd1 : 1 ≤ entry R 0 (R.length - 1) := by
    have hlt : R.length - 1 < R.length := by
      have := List.length_pos_iff.mpr hRne
      omega
    have := hR _ (entry_pair_mem (B := R) hlt)
    have hEq : entry R 0 (R.length - 1)
        = (R.getD (R.length - 1) ((0, 0, 0) : ℕ × ℕ × ℕ)).1 := rfl
    omega
  have he1 : 1 ≤ entry R 1 (R.length - 1) - v := by
    have := L53.tower2_vw hRne hd hi2 hpM
    omega
  rw [tower2_eq_operTower hR hRne hd hi2 hpM n,
    operTower_eq_shTower2 hQne hd1 he1 hQ00 hQ10 hQ0 hQ1 n]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine (mem_Wself_iff a _).mpr ⟨h _ _ _ _ hQself hQne ?_ ?_, ?_⟩
  · intro j hj1 hj2
    rw [hQ00]
    exact hQ0 j hj1 hj2
  · intro j hj1 hj2
    rw [hQ10]
    exact hQ1 j hj1 hj2
  · rw [lev_shTower2_root hQne, hQlev]
    exact hva

/-! ### 54.1 ⟹ 現在地（`TowerExpBig` の完全な分解）

    `|R| = 1`                    … `towerExp_singleton`（**仮定ゼロ**、§39）
    `R.dropLast` の行 2 ≡ `z`    … `tower_of_row2const`（**仮定ゼロ**、§40）
    `srow = 1`                   … `shTower` ⟹ **`ShiftTowerClosedS`**（§43）
                                   ⟸ `L47W.shiftTowerClosed_iff_wself`（**段は無料**）
    `srow = 2`, ブロッカー無し    … `shTower2` ⟹ **`ShTower2Self`**（上、緑）
    `srow = 2`, ブロッカー有り    … ブロック所属は **`LiftTieCore`**（§52）
                                   ＋ 繋ぎは `ShTower2Self` の**リフト版**

⟹ **(2) の側は `srow` によらず「同じ 1 単位を等差にずらして並べた塔が `Wself` に閉じる」
1 文**（`ShiftTowerClosedS` / `ShTower2Self`）。**段はどこにも現れない。**

⚠ `WCat` は使えない（H12 と私の独立の一致）: `WCat` は両辺に**同じ段**を要求するが、
塔のブロック `k` の根は `lev = 2(v + k·e) + z` で `k` とともに上がり、
`W_mono` は**上げる向きだけ**なので下ろせない。
⟹ **`ShTower2Self` の形（「`Q` だけが `Wself` なら塔全体が `Wself`」——
途中のブロックが `W` にいることを要求しない）が正しい上界。** -/


/-! ## 55. ★★★★★ 課題 L133: **マスクつき塔閉包**の定式化

### 55.1 ⚠ `L51Lift.liftTower` は**一様版**で、我々のものとは別物

    `L51Lift.liftTower Q e n = (range n).flatMap fun k => shiftr01 (e*k) **k** Q`
      … 行 1 も**一様に**ずらす（`shiftr01`）。`L51Lift.LiftTowerClosed`（`:63`）は未証明
    **`L105.operTower Q d e n`（§47）**
      `= Q ++ shiftr01 d 0 (**Lift1** (operTower Q d e n) e)`
      … 行 1 は**根の錐の上でだけ**上がる（`Lift1`）

⚠ `L51Lift` は roots に無いので import できず、名前空間も別（`TRIO.L51Lift` と `TRIO.L105`）。
**衝突はしないが、別物である**ことをここに明記しておく。
H12 の実測どおり **一様版が当たるのは `|R| = 5` で 16.8%** で、残り 83.2% はマスクつき。

### 55.2 H12 と R2 の閉じた形は同じ（`Lift1_shiftr01`、§52） -/

/-- H12 の閉じた形（ブロックごとに `Lift1`）。 -/
noncomputable def mTower (Q : TrioSeq) (d0 d1 : ℕ) (n : ℕ) : TrioSeq :=
  (List.range n).flatMap fun k => Lift1 (shiftr01 (d0 * k) 0 Q) (d1 * k)

/-- **H12 の形 ＝ R2 の形**（`Lift1` と行 0 の一様シフトが可換だから）。 -/
theorem mTower_eq (Q : TrioSeq) (d0 d1 n : ℕ) :
    mTower Q d0 d1 n
      = (List.range n).flatMap fun k => shiftr01 (d0 * k) 0 (Lift1 Q (d1 * k)) := by
  unfold mTower
  refine List.flatMap_congr ?_
  intro k _
  exact Lift1_shiftr01 (d0 * k) (d1 * k) Q

/-! ### 55.3 ⚠ **`mTower` と `operTower` が等しいことは証明されていません**

    `mTower`     … マスクを**ブロックごとに `Q` の中で**計算する
    `operTower`  … マスクを**塔全体の上で**計算する（`oper_cons_tower2` が実際に作る形）

`Wset.le1_take`（`:908`、緑）は**接頭辞局所性**しか与えないので、
第 `k` ブロック（`k ≥ 1`）のマスクが `Q` だけで決まることは**出ません**。
H12 の §211「マスクは全ブロックで同一」は**その主張の実測**である。

⟹ **核は `operTower`（`oper_cons_tower2` から Lean で出る形）で立てる。**
`mTower` で立てると**未証明の同一視を仮定に紛れ込ませる**ことになる（教訓 14）。 -/

theorem lev_operTower_root {Q : TrioSeq} (hQne : Q ≠ []) (d e n : ℕ) :
    lev (operTower Q d e (n + 1)) 0 = lev Q 0 := by
  have hQlen : 0 < Q.length := List.length_pos_iff.mpr hQne
  show lev (Q ++ shiftr01 d 0 (Lift1 (operTower Q d e n) e)) 0 = lev Q 0
  unfold lev
  rw [entry_append_left Q _ hQlen, entry_append_left Q _ hQlen]

/-- **★★★★★ (2) の核（マスクつき塔閉包）。段は現れない。** -/
def OperTowerSelf : Prop :=
  ∀ (d e n : ℕ) (Q : TrioSeq), Q ∈ Wself → Q ≠ [] →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
    operTower Q d e n ∈ Wself

open Classical in
/-- **★★★★★ `srow = 2` の枝は `OperTowerSelf` だけで出る**（ブロッカーの有無に依らない）。 -/
theorem towerExp2_of_operTowerSelf (h : OperTowerSelf) {v z m a : ℕ} {R : TrioSeq}
    (hR : argOK R) (hRne : R ≠ []) (hz1 : z ≤ 1) (hva : 2 * v + z ≤ a)
    (hd : domT R m) (hi2 : srow R (R.length - 1) = 2)
    (hdl : R.dropLast ∈ Wstar)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    ∀ n, 1 ≤ n → (((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧ ∈ W a := by
  intro n hn
  have hdlarg : argOK R.dropLast := argOK_dropLast hR
  have hQne : (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) ≠ [] := by simp
  have hQlev : lev (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 0 = 2 * v + z :=
    lev_cons_root v z _
  have hQself : (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) ∈ Wself := by
    show (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast)
      ∈ W (lev (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 0)
    rw [hQlev]
    exact hdl hdlarg v z (2 * v + z) hz1 le_rfl
  have hQ0 : ∀ j, 1 ≤ j → j < (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast).length →
      entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 0 0
        < entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 0 j := by
    intro j hj1 hj2
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp only [List.length_cons] at hj2
    have hk : k < R.dropLast.length := by omega
    have hpos := hdlarg _ (entry_pair_mem (B := R.dropLast) hk)
    have hEq : entry R.dropLast 0 k
        = (R.dropLast.getD k ((0, 0, 0) : ℕ × ℕ × ℕ)).1 := rfl
    have h00 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 0 0 = 0 := by
      simp [entry]
    rw [h00, entry_cons_succ]
    omega
  rw [tower2_eq_operTower hR hRne hd hi2 hpM n]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine (mem_Wself_iff a _).mpr ⟨h _ _ _ _ hQself hQne hQ0, ?_⟩
  rw [lev_operTower_root hQne, hQlev]
  exact hva

/-- ⟹ `TowerOK` の `srow = 2` 枝は `OperTowerSelf` 1 本。 -/
theorem operTowerSelf_of_shTower2Self_noBlocker (h : ShTower2Self) {d e n : ℕ}
    {Q : TrioSeq} (hQself : Q ∈ Wself) (hQne : Q ≠ []) (hd : 1 ≤ d) (he : 1 ≤ e)
    (hr0 : entry Q 0 0 = 0)
    (h0 : ∀ l, 1 ≤ l → l < Q.length → 0 < entry Q 0 l)
    (h1 : ∀ l, 1 ≤ l → l < Q.length → entry Q 1 0 < entry Q 1 l) :
    operTower Q d e n ∈ Wself := by
  rw [operTower_eq_shTower2 hQne hd he hr0 rfl h0 h1 n]
  refine h d e n Q hQself hQne ?_ ?_
  · intro j hj1 hj2
    rw [hr0]
    exact h0 j hj1 hj2
  · exact h1

/-! ### 55.4 ⟹ 今日の最終的な核（2 本）

    **(1) `LiftTieCore`**（§29）… ブロック 1 個を持ち上げる。**経路 C と D で同じ命題**
        3 量化 / 4 前提、`d = 1`・自己段・タイあり・`¬TieFree`
    **(2) `OperTowerSelf`**（上）… マスクつき塔が `Wself` に閉じる。**段が現れない**
        4 量化 / 3 前提（`Q ∈ Wself` / `Q ≠ []` / 根が行 0 で狭義最浅）

    ブロッカーが無ければ (2) は **`ShTower2Self`**（`Lift1` が消えた一様 2 方向シフト塔）
    に落ちる（`operTowerSelf_of_shTower2Self_noBlocker`、上）。H12 実測で `|R|=5` の 16.8%。

⚠ `L51Lift.LiftTowerClosed`（`:63`、未証明）は**行 1 も一様**な版なので、
証明しても (2) は出ない（覆うのは 16.8% のほう）。**別物として立てた。** -/


/-! ## 56. ★★★★★ 課題 L134: **`shTower2` の展開も「最後のブロックだけ」**

`oper_shTower`（§48、あなたの予測）の 2 方向版。道具はやはり既存:

    `L53.comm_of_hasParentInBlock`（`L53Subst.lean:922`）
    `Wset.oper_shiftr01`（`:434`）      行 0 の一様シフトは無条件で可換
    **`Wset.oper_shiftr1`（`:730`）**   行 1 の一様シフトは
                                       **末尾列の `lev ≠ 0`** のとき可換
    `Wset.srow_shiftr1`（`:673`）/ `Wset.hasParent_shiftr1`（`:650`）

⚠ 行 1 のシフトには **`lev Q (|Q|-1) ≠ 0`（＝ 末尾列の `srow ≥ 1`）**が要る。
行 1 が 0 の列は `+e` で `srow` が `0 → 1` に変わるため。 -/

theorem hasParentInBlock_shiftr1 {d : ℕ} {Q : TrioSeq}
    (hlev : lev Q (Q.length - 1) ≠ 0) (h : L53.HasParentInBlock Q) :
    L53.HasParentInBlock (shiftr01 0 d Q) := by
  unfold L53.HasParentInBlock at h ⊢
  rw [shiftr01_length, Wset.srow_shiftr1 hlev, hasParent_shiftr1]
  exact h

/-- **★★★★★ `shTower2` の展開も「最後のブロックだけ」を展開する。** -/
theorem oper_shTower2 {Q : TrioSeq} (hQne : Q ≠ []) (hQ2 : Q.length - 1 ≠ 0)
    (hlev : lev Q (Q.length - 1) ≠ 0) (hblk : L53.HasParentInBlock Q)
    (d e n m : ℕ) :
    (shTower2 Q d e (n + 1))⟦m⟧
      = shTower2 Q d e n ++ shiftr01 (n * d) (n * e) (Q⟦m⟧) := by
  have hQlen : 0 < Q.length := List.length_pos_iff.mpr hQne
  have hsplit : shiftr01 (n * d) (n * e) Q
      = shiftr01 (n * d) 0 (shiftr01 0 (n * e) Q) := (shiftr01_comp01 _ _ Q).symm
  have hNne : shiftr01 (n * d) (n * e) Q ≠ [] := by
    intro hc
    have hl := congrArg List.length hc
    rw [shiftr01_length] at hl
    exact hQne (List.length_eq_zero_iff.mp hl)
  have hN2 : (shiftr01 (n * d) (n * e) Q).length - 1 ≠ 0 := by
    rw [shiftr01_length]; exact hQ2
  have hlevlt : Q.length - 1 < Q.length := by omega
  have hNz : ¬(entry (shiftr01 (n * d) (n * e) Q) 0
        ((shiftr01 (n * d) (n * e) Q).length - 1) = 0 ∧
      entry (shiftr01 (n * d) (n * e) Q) 1
        ((shiftr01 (n * d) (n * e) Q).length - 1) = 0 ∧
      entry (shiftr01 (n * d) (n * e) Q) 2
        ((shiftr01 (n * d) (n * e) Q).length - 1) = 0) := by
    rw [shiftr01_length]
    rintro ⟨-, h1, h2⟩
    rw [entry1_shift hlevlt] at h1
    rw [entry2_shiftr01] at h2
    unfold lev at hlev
    omega
  have hNblk : L53.HasParentInBlock (shiftr01 (n * d) (n * e) Q) := by
    rw [hsplit]
    exact hasParentInBlock_shiftr01 (hasParentInBlock_shiftr1 hlev hblk)
  rw [shTower2_succ,
    L53.comm_of_hasParentInBlock m hNne hN2 hNz hNblk, hsplit, oper_shiftr01,
    Wset.oper_shiftr1 hlev, shiftr01_comp01]

/-! ### 56.1 ⟹ `ShTower2Self` の帰納の形（`srow = 1` 側と同じ）

節 2（`mem_of_oper_mem`）で `shTower2 Q d e (n+1) ∈ Wself` を示すには

    `∀ m ≥ 1, (shTower2 Q d e (n+1))⟦m⟧ ∈ W (lev Q 0)`
    ＝ **`shTower2 Q d e n ++ shiftr01 (n*d) (n*e) (Q⟦m⟧) ∈ W (lev Q 0)`**

`Q ∈ Wself` ⟹ `Q⟦m⟧ ∈ W (lev Q 0)`（`Wchar.oper_mem_of_mem`、緑）、
`shTower2 Q d e n` は帰納法の仮定 ⟹ **両端は揃う。**

⚠ 繋ぐのは連結で `rsum` は破れる（§14）。⟹ **`Aop` の節 3（graft）が唯一の道**という
`srow = 1` 側（§48.1）とまったく同じ形。**(2) は `srow` に依らず 1 つの問題になった。** -/


/-! ## 57. ★★★★★ 課題 L135: **3 つの「塔」の違い**（次の人が必ず引っかかる場所）

| 名前 | 定義 | マスク | 由来 |
|---|---|---|---|
| `Wset.shTower Q e n` | `flatMap k => shiftr01 (k*e) 0 Q` | 無し（行 0 だけ） | `srow=1` の塔（§43、**証明ずみ**） |
| `L105.shTower2 Q d e n` | `flatMap k => shiftr01 (k*d) (k*e) Q` | 無し（行 0・行 1 とも一様） | ブロッカー無しの `srow=2`（§50、**証明ずみ**） |
| `L51Lift.liftTower Q e n` | `flatMap k => shiftr01 (e*k) k Q` | 無し（行 1 の増分が `k`） | `L51` の一様版。**roots に無い** |
| **`L105.operTower Q d e n`** | `Q ++ shiftr01 d 0 (Lift1 (operTower …) e)` | **有り（塔全体の `le1` 錐）** | **`oper_cons_tower2` が実際に作る形**（§47、**証明ずみ**） |
| `L105.mTower Q d0 d1 n` | `flatMap k => Lift1 (shiftr01 (d0*k) 0 Q) (d1*k)` | **有り（ブロックごとに `Q` の中）** | H12 / R2 の**実測**の形（§55、**同一視は未証明**） |

⚠ **改名した**（旧 `L105.liftTower` → **`operTower`**）。`L51Lift.liftTower`（一様）とも
`mTower`（ブロック局所）とも混ざらない名前にした。 -/

/-! ### 57.1 ★★★ **`operTower` と `mTower` の違いは「どちら向きに割れるか」**

`shTower` / `shTower2` / `mTower` は **flatMap** なので**両向きに割れる**:

    cons 形（先頭を切る）… `Q ++ …`
    succ 形（末尾を切る）… `… ++ (最後のブロック)`

⚠ ところが **`operTower` は cons 形しか無い**（定義がその再帰）。
**succ 形（末尾のブロックを切り出す）は、マスクがブロック局所でないと書けない。**

⟹ そして **`oper_shTower`（§48）/ `oper_shTower2`（§56）の技法は
`succ` 形（末尾を切る）を使う**（`comm_of_hasParentInBlock` の `A ++ N` で `N` が最後のブロック）。

> **⟹ `operTower` には `oper_shTower` の技法が使えない。使えるようになる条件が
> ちょうど `mTower = operTower`（マスクのブロック局所性）である。**

⟹ **H12 / R2 に振った測定は、まさにこの一点を決める。** -/

theorem mTower_succ (Q : TrioSeq) (d0 d1 n : ℕ) :
    mTower Q d0 d1 (n + 1)
      = mTower Q d0 d1 n ++ Lift1 (shiftr01 (d0 * n) 0 Q) (d1 * n) := by
  unfold mTower
  rw [List.range_succ, List.flatMap_append]
  simp

theorem mTower_zero (Q : TrioSeq) (d0 d1 : ℕ) : mTower Q d0 d1 0 = [] := rfl

theorem mTower_one (Q : TrioSeq) (d0 d1 : ℕ) : mTower Q d0 d1 1 = Q := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, mTower_succ, mTower_zero, List.nil_append]
  simp

/-! ### 57.2 ⟹ `mTower = operTower` が真なら何が出るか

`mTower_succ` があるので、`operTower = mTower` が分かれば **`operTower` にも succ 形**が付き、
§56 とまったく同じ手順で

    `(operTower Q d e (n+1))⟦m⟧
      = operTower Q d e n ++ (Lift1 (shiftr01 (n*d) 0 Q) (n*e))⟦m⟧`

が出る。あとは最後のブロックの展開だけを見ればよく、**それは `Q` 1 個の話**になる。
⟹ **(2) の帰納が `srow = 1` 側とまったく同じ形になる。**

⚠ 逆に偽なら、`operTower` の展開は `(Lift1 (塔全体) e)⟦m⟧` を見ることになり、
**`Lift1` と `oper` の非可換性（`Wtower2.Le1_Lift1_oper` `:4415` /
`Le1_oper_Lift1_shiftr01` `:4482` の挟み込みしか無い）**が正面から出る。
⟹ **そのときは (2) が (1) と同じ壁（凸性）に落ちる。**

**⟹ どちらに転んでも次の一手が決まる。測定待ち。** -/


/-! ## 58. 課題 L135: 段 0 と `v = 0 ⟹ z = 0`

### 58.1 ⛔ **`v = 0 ⟹ z = 0` は一般には偽です**（H12 の観測は箱の産物）

機構は `v` ではなく**行 2 の上界**である。`L53.tower2_zr`（`:2380`）が

    `domT R m` ＋ `srow = 2` ＋ `hasParent` ⟹ **`z < entry R 2 (|R|-1) = c`**

を与えるので、`z ≤ 1` のもとで **`z = 1` ⟺ `c ≥ 2`**。
⟹ **箱の行 2 が `≤ 1` なら `z = 0`（`v` に依らず）**。それが §51 の
`tower2_z_zero_of_zle1`（緑、`zle1 R` だけを追加仮定に取る）である。

⚠ **`c ≥ 2` を許せば `v = 0, z = 1` は起きる。** R2 自身が最小例を出している:

    `R = [(1,0,0), (1,1,2)]`, `v = 0`, `z = 1`, `c = 2`

（`argOK R` ✓／`srow R 1 = 2` ✓／`R` の中で末尾は孤児（`le0 R 0 1` が
`1 < 1` で偽）⟹ `domT R 3` ✓／`(0,0,1) :: R` では根が行 2 の親になる ✓。）

⟹ **H12 の「`v = 0 ⟹ z = 0`、94334 件で例外 0」は、箱の行 2 が `≤ 1` だったことの帰結。**
`v = 0` は関係ない。**H12 / R2 に箱の行 2 の範囲を確認してもらうこと。**

### 58.2 ★ 段 0 では `Aop` の節 3 が使えない（team-lead の指摘、確認）

`Wset.Aop`（`:171`）の節 3 は `∃ m : ℕ, m < u ∧ …` なので、**`u = 0` では `m < 0` が
不可能** ⟹ 節 3 は空。⟹ **`W 0` は節 1 と節 2 だけで決まる。** -/

theorem mem_W_zero_iff {M : TrioSeq} :
    M ∈ W 0 ↔ ((M.length ≤ 1 ∧ lev M 0 = 0) ∨ (∀ n : ℕ, 1 ≤ n → M⟦n⟧ ∈ W 0)) := by
  constructor
  · intro h
    rw [← A1 0] at h
    rcases h with h | h | ⟨m, hm, -, -⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd hm (Nat.not_lt_zero m)
  · intro h
    exact A1_intro (h.imp id Or.inl)

/-! ### 58.3 ⚠ ただし「新しい特徴づけ」ではありません

`Wchar` が**すべての段について**同じことを既に与えている（教訓 24 の確認）:

    `Wchar.mem_iff_oper_mem`（`:75`、緑）… `2 ≤ |S| ⟹ (S ∈ W a ⟺ ∀ n ≥ 1, S⟦n⟧ ∈ W a)`
      ＝ **長さ 2 以上では節 3 は節 2 に吸収される**（`aop_clause3_to_clause2` `:39`）
    `Wchar.mem_iff_lev_le`（`:106`、緑）… `[(d,v,z)] ∈ W a ⟺ 2v+z ≤ a`

⟹ `mem_W_zero_iff` が足すのは **`|M| ≤ 1` の枝の形**だけ。
**段 0 の本当の内容は「`W 0` の単元は `(d,0,0)` に限る」**（`mem_iff_lev_le` で `2v+z ≤ 0`）。

### 58.4 ★ ⟹ 段 0 で本当に効くこと

> **段 0 では `graft` の機械が**証明の道具として**使えない。**
> 長さ 2 以上では `Wchar.mem_iff_oper_mem` により節 3 は節 2 に吸収されるので
> **結論は変わらない**が、**「節 3 で作る」という証明戦略が消える。**

⟹ 私が §42/§48 で「節 3（graft）が唯一の道」と書いた議論は、**段 0 では成り立たない**。
段 0 では**節 2 で降りるしかなく、着地点は `(d,0,0)` の単元だけ**である。

⟹ **`v = 0, z = 0` の塔（`lev` 根 = 0、段 `a = 0`）は、
「展開木が全部 `(d,0,0)` に着く」ことを示す問題**になる。
これは `Wset.zeroRow2_mem_Wself`（行 2 ≡ 0 ⟹ `Wself`）が扱う形に近いが、
`v = 0, z = 0` でも **`R.dropLast` の行 2 は非零**（`TowerExpBigRow2` の前提）なので
そのままでは当たらない。**そこが残る。** -/


/-! ## 59. ★★★★★ 課題 L135-3: **`v = 0` の残核は「`W 0` から `Wself` へ」1 文**

R2 の実測「`v = 0` には無料の枝が 1 本も無い（(α)(β)(γ) すべて 0 件）、
しかも (δ) の 71.6% が `v = 0`」を受けて、そこだけ取り出す。

`LiftTieCore`（§29）に `v = 0`, `z = 0` を入れると:

    前提 `¬(1 ≤ v ∧ TieFree …)` … **`1 ≤ 0` が偽なので自動的に満たされる**
    段 `2*v+z = 0`、結論の段 `2*v+z+2 = 2`

⟹ **`((0,0,0) :: R) ∈ W 0` ⟹ `Lift1 ((0,0,0) :: R) 1 ∈ W 2`**

そして `lev (Lift1 ((0,0,0) :: R) 1) 0 = 2*(0+1)+0 = 2` なので、
`Wtower2.mem_Wself_iff` より **結論は `∈ Wself` と同値**。

> **⟹ `v = 0` の残核は「`W 0` の元を 1 段持ち上げると `Wself` に入る」という 1 文。**
> 段は `0 → 2` で、これは `lev` の増分ちょうど。**余裕はゼロ。** -/

/-- **`LiftTieCore` の `v = 0`, `z = 0` の場合**（(δ) の 71.6%）。 -/
def LiftTieCoreZero : Prop :=
  ∀ (R : TrioSeq), argOK R → (∃ p ∈ R, p.2.1 = 0) →
    (((0, 0, 0) : ℕ × ℕ × ℕ) :: R) ∈ W 0 →
    Lift1 (((0, 0, 0) : ℕ × ℕ × ℕ) :: R) 1 ∈ W 2

theorem liftTieCoreZero_of_core (h : LiftTieCore) : LiftTieCoreZero := by
  intro R hR ht hX
  have hres := h 0 0 R hR ht (by rintro ⟨h1, -⟩; omega) (by simpa using hX)
  simpa using hres

/-- **★ `v = 0` の残核の結論は `Wself` 所属と同値**（段はちょうど `lev`）。 -/
theorem liftTieCoreZero_iff_wself {R : TrioSeq} :
    Lift1 (((0, 0, 0) : ℕ × ℕ × ℕ) :: R) 1 ∈ W 2
      ↔ Lift1 (((0, 0, 0) : ℕ × ℕ × ℕ) :: R) 1 ∈ Wself := by
  have hne : (((0, 0, 0) : ℕ × ℕ × ℕ) :: R) ≠ [] := by simp
  have hlev : lev (Lift1 (((0, 0, 0) : ℕ × ℕ × ℕ) :: R) 1) 0 = 2 := by
    unfold lev
    rw [L53.entry1_Lift1_zero hne, entry2_Lift1]
    simp [entry]
  rw [mem_Wself_iff]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, by rw [hlev]⟩

/-! ### 59.1 ⟹ `v = 0` の錐はいちばん単純な形

`Lcone.le1_zero_iff`（`:36`）に `v = 0` を入れると

    `le1 X 0 j` ⟺ **`j` の根以外の行 0 祖先がすべて 行 1 ≥ 1**

⟹ **ブロッカー ＝ 行 1 が 0 の列**。R2 の実測「`v = 0` では
ブロッカー ⟺ タイ（4,977/4,977）」は**この同値の言い換え**である
（`v = 0` なので「行 1 ≤ v」と「行 1 = v」が同じ）。

⟹ **`v = 0` の残核 ＝ 「行 1 が 0 の列がある `W 0` の元を 1 段持ち上げても `Wself`」**。

### 59.2 ⚠ 段 0 の効き方（§58.4 の続き）

段 0 では節 3 が使えないので、**前提 `((0,0,0) :: R) ∈ W 0` は
「展開木が全部 `(d,0,0)` の単元に着く」以上の情報を持たない**
（`Wchar.mem_iff_oper_mem` ＋ `mem_iff_lev_le`）。
⟹ **前提から使えるのは「展開が終わる」ことだけ**で、graft の与件は無い。

一方 **結論の段は 2** なので、そちらでは節 3 が使える（`m < 2` に `m = 0, 1` がある）。
⟹ **前提側は節 2 だけ、結論側は節 2 と節 3 の両方**という**非対称**な形。

⟹ **`v = 0` の残核を攻めるなら、結論側の節 3 を使って作るのが筋**である
（前提側には無いので）。**次の一手はそこ。** -/


/-! ## 60. ★★★★ 課題 H73 の補題: **半分は 2 行で出る。残り半分に穴の可能性**

H12 の主張は「`operTower` の第 `k` ブロックの `le1` 錐が、そのブロック単体の錐と一致する」。
**これは 2 つの主張に分かれる。** -/

/-- **★ 易しい半分（緑・2 行）: ブロック単体の錐は `Q` の錐と同じ。**
`Wset.le1_Lift1`（`:1213`、無条件）＋ `Core.le1_shiftr01`（`:3470`、無条件）。 -/
theorem le1_block {Q : TrioSeq} {d0 d1 a b : ℕ} :
    le1 (Lift1 (shiftr01 d0 0 Q) d1) a b ↔ le1 Q a b := by
  rw [le1_Lift1, le1_shiftr01]

/-! ### 60.1 ⚠ **難しい半分**: 塔全体で計算した錐がブロックに制限されるか

`le1_block`（上）が言うのは「**ブロック単体で計算した錐は `Q` の錐**」だけ。
H12 が要るのは

    **`le1 (塔全体) 0 (第 `k` ブロックの位置 j)` ⟺ `le1 (第 `k` ブロック) 0' j`**

で、**左辺は塔全体の根（第 0 ブロックの根）から、右辺はそのブロックの根から**測る。
**根が違う。** ⟹ `le1_block` からは出ない。

### 60.2 ⚠ ★ 穴の可能性（**陰性対照の設計**）

`Lcone.le1_zero_iff`（`:36`、根が行 0 で狭義最浅のとき）:

    `le1 T 0 i` ⟺ **`i` の根以外の行 0 祖先がすべて 行 1 > v**

第 `k` ブロック（`k ≥ 1`）の列 `i` の行 0 祖先鎖は、**ブロック内の祖先**（`Q` の祖先の像。
行 1 は `Q` の行 1 ＋ リフト ⟹ 減らない）に加えて、
**ブロック `k` の根から前のブロックへ渡る鎖**を含む。

⟹ **その渡る鎖が第 0 ブロック（＝ `Q` 自身）のブロッカー（行 1 ≤ `v` の列）を通ると、
左辺は偽・右辺は真になりうる。**

具体的には: 第 1 ブロックの根は `Q` の根を行 0 で `d` ずらしたもの（行 0 = `d`）。
その行 0 の親は **`Q` の中で行 0 が `d` より真に浅い最も近い列**である。
⟹ **`Q = (0,v,z) :: R.dropLast` に「行 0 < `d` かつ 行 1 ≤ `v`」の列があると破れる**はず。

> **⟹ 陰性対照の設計: `R.dropLast` に「行 0 が `entry R 0 (|R|-1)` より小さく、
> かつ 行 1 が `v` 以下」の列を持つ `R` を探してもらう。**
> **H12 の 34326 ブロックにその形が入っていなければ、0 件は当然である。**

⚠ 逆に、塔の場面では `d = entry R 0 (|R|-1)` が `R.dropLast` のどの行 0 よりも
**小さい**（＝ 末尾列が `R` の中でいちばん浅い）という制約があるなら、
渡る鎖は必ず**根に直行**するので破れない。**その制約が `domT` から出るかを確かめる価値がある。**
（`domT` は行 `srow` の孤児性を言うだけなので、行 0 については直接は言わない。
`nextrel2` が `le1` を要求し `le1` が `le0` を要求する経路で間接的に効く可能性はある。）

### 60.3 ⟹ 報告

**易しい半分は緑にした（`le1_block`）。難しい半分は未証明で、しかも穴の可能性がある。**
⚠ **H12 の実測 0 件は、上の形が母集団に入っていなければ当然**なので、
**陰性対照を先に走らせてほしい**（今日 3 回、この手順で偽の候補を潰している）。 -/


/-! ## 61. 課題 L136: `v = 0, z = 1` の版 ＋ H73 の的を `Prop` にする

### 61.1 ★ `v = 0, z = 1` は本物（R2 が箱を振って確認）

私の §58.1 の指摘どおり、H12 の「例外 0」は箱が行 2 ≤ 1 だったため。
`zle1` は核に課せない（§53）ので **`v = 0, z = 1` は本物の場合**であり、
そこでは前提の段が **1**、結論の段が **3** になる。 -/

/-- **`LiftTieCore` の `v = 0`, `z = 1` の場合。** -/
def LiftTieCoreOne : Prop :=
  ∀ (R : TrioSeq), argOK R → (∃ p ∈ R, p.2.1 = 0) →
    (((0, 0, 1) : ℕ × ℕ × ℕ) :: R) ∈ W 1 →
    Lift1 (((0, 0, 1) : ℕ × ℕ × ℕ) :: R) 1 ∈ W 3

theorem liftTieCoreOne_of_core (h : LiftTieCore) : LiftTieCoreOne := by
  intro R hR ht hX
  have hres := h 0 1 R hR ht (by rintro ⟨h1, -⟩; omega) (by simpa using hX)
  simpa using hres

theorem liftTieCoreOne_iff_wself {R : TrioSeq} :
    Lift1 (((0, 0, 1) : ℕ × ℕ × ℕ) :: R) 1 ∈ W 3
      ↔ Lift1 (((0, 0, 1) : ℕ × ℕ × ℕ) :: R) 1 ∈ Wself := by
  have hne : (((0, 0, 1) : ℕ × ℕ × ℕ) :: R) ≠ [] := by simp
  have hlev : lev (Lift1 (((0, 0, 1) : ℕ × ℕ × ℕ) :: R) 1) 0 = 3 := by
    unfold lev
    rw [L53.entry1_Lift1_zero hne, entry2_Lift1]
    simp [entry]
  rw [mem_Wself_iff]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, by rw [hlev]⟩

/-! ### 61.2 ⟹ `v = 0` の残核は **2 本**（段が違う）

    `z = 0` … 前提の段 **0**（節 3 が**無い**）／結論の段 **2**（節 3 が使える）
    `z = 1` … 前提の段 **1**（節 3 が `m = 0` で**使える**）／結論の段 **3**

⟹ **前提側の道具が違う。** `z = 0` は「節 2 で降りるだけ」、
`z = 1` は「前提側でも `m = 0` の graft が使える」。**別々に扱う。**

## 62. ★★★★★ 課題 H73: R2 の機構を `Prop` にして、そこから先を全部繋ぐ

R2 の機構「**錐の外の列は必ず自分のブロックの中にブロッカーを持つ**」
（311,688 列、外のブロックにしか無い ＝ **0 件**）を Lean の 1 文にすると、
**`Lift1` が flatMap を通り抜ける**ことである。 -/

/-- **★ H73 の的**: `Lift1` が塔の flatMap を通り抜ける（＝ 錐がブロック局所）。
R2 の実測 100%（塔 276,876 / ブロック 1,245,942 / 列 6,846,876、例外 0）。**未証明。** -/
def LiftFlatMapLocal : Prop :=
  ∀ (Q : TrioSeq) (d e n : ℕ),
    Lift1 (mTower Q d e n) e
      = (List.range n).flatMap fun k =>
          Lift1 (Lift1 (shiftr01 (d * k) 0 Q) (e * k)) e

theorem shiftr01_flatMap (d0 d1 : ℕ) (l : List ℕ) (f : ℕ → TrioSeq) :
    shiftr01 d0 d1 (l.flatMap f) = l.flatMap fun k => shiftr01 d0 d1 (f k) := by
  unfold shiftr01
  rw [List.map_flatMap]

theorem mTower_block_succ (Q : TrioSeq) (d e k : ℕ) :
    Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1))
      = shiftr01 d 0 (Lift1 (Lift1 (shiftr01 (d * k) 0 Q) (e * k)) e) := by
  have hd : d * (k + 1) = d + d * k := by rw [Nat.mul_succ, Nat.add_comm]
  have he : e * (k + 1) = e * k + e := Nat.mul_succ e k
  simp only [hd, he, Lift1_shiftr01, Lift1_Lift1, shiftr01_comp]

theorem mTower_cons (Q : TrioSeq) (d e n : ℕ) :
    mTower Q d e (n + 1)
      = Q ++ (List.range n).flatMap fun k =>
          Lift1 (shiftr01 (d * (k + 1)) 0 Q) (e * (k + 1)) := by
  unfold mTower
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  simp

/-- **★★★★★ 的が落ちれば `operTower = mTower`。** -/
theorem operTower_eq_mTower (h : LiftFlatMapLocal) (Q : TrioSeq) (d e : ℕ) :
    ∀ n, operTower Q d e n = mTower Q d e n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show Q ++ shiftr01 d 0 (Lift1 (operTower Q d e n) e) = _
      rw [ih, h Q d e n, mTower_cons]
      congr 1
      rw [shiftr01_flatMap]
      refine List.flatMap_congr ?_
      intro k _
      exact (mTower_block_succ Q d e k).symm

/-- ⟹ そのとき `operTower` に **succ 形**が付く（§57.1 の分かれ目）。 -/
theorem operTower_succ (h : LiftFlatMapLocal) (Q : TrioSeq) (d e n : ℕ) :
    operTower Q d e (n + 1)
      = operTower Q d e n ++ Lift1 (shiftr01 (d * n) 0 Q) (e * n) := by
  rw [operTower_eq_mTower h, operTower_eq_mTower h, mTower_succ]

/-! ### 62.1 ⟹ 的が落ちたあとの道筋（全部緑で繋いである）

    `LiftFlatMapLocal`（**未証明**、R2 の機構）
      ⟹ `operTower_eq_mTower`（上、緑）
      ⟹ **`operTower_succ`**（上、緑）＝ §57.1 の「succ 形が書ける」条件
      ⟹ `oper_shTower`（§48）/ `oper_shTower2`（§56）と同じ技法が使える
      ⟹ **(2) の帰納が `srow = 1` 側とまったく同じ形になる**

⚠ **`LiftFlatMapLocal` 自体は未証明。** R2 の但し書きどおり、
実測は「証明の目標」であって「証明」ではない。**`operTower` で核を立てたままにしてある。**

### 62.2 ⟹ 証明の道（R2 の機構から）

`Lcone.le1_zero_iff`（`:36`）で両辺を書き下すと、要るのは

    **`le1 (mTower Q d e n) 0 (第 `k` ブロックの位置 `j`)`
      ⟺ `le1 (第 `k` ブロック) 0 j`**

で、`le1_block`（§60、緑）が右辺を **`le1 Q 0 j`** に直す。
⟹ **残るのは「塔全体の錐がブロックに制限される」**で、R2 の機構は
「**錐の外の列は必ず同ブロック内にブロッカーを持つ**」＝ その `⟸` 側である。

⚠ 私の §60.2 の懸念（前のブロックのブロッカーで破れる可能性）は
**R2 が 0 件と測った**（外のブロックにしか無いケース）。⟹ **機構は正しそう。**
残るのは**なぜ外のブロックのブロッカーが効かないか**で、そこが証明の核心。 -/

/-! ## 12. ★★★★★ 課題 L105 の結論

### 12.1 `CoreCap` の正体

    **`CoreCap` = `WSnoc` を「装備つき主ブロック」に制限したもの。**

`t = 0` では `capBase M v z 0 = (0,v,z) :: M.dropLast` なので、`CapSnocOpen'` は

    土台 `C`  … `(0,v,z) :: R` の形（`argOK R`、`z ≤ 1`）＋ `CtxOK`
    足す列 `q` … 行 0 は `entry M 0 (|M|-1)` に固定（行 1・行 2 は任意）
    無料の追加与件 … **根が行 0 で全列の祖先**（`argOK` 由来）

に等しい。`t ≥ 1` はこれを `Lift1 · t` で写しただけで、**新しい要求はゼロ**
（`Lift1_snoc`）。

**厳密な形は `CapSnocOpenExact`（§13）で、`capSnocOpenExact_iff_coreCap` により
`CoreCap` と `⟺`。** 無料の枝を全部落とし、`argOK` 由来の根祖先性を与件に加えてある。

### 12.2 場合分けの網羅（課題 L105 (1)）

    `t` による場合分け        … **不要**（`Lift1_snoc` で吸収）
    親なし（孤児）            … **無料**（`snoc_orphan_W`、段によらない）
    `C` の行 2 ≡ 0            … **無料**（`snoc_zeroRow2` ＋ `W_mono`）
    `srow = 0` かつ親が根      … **無料**（`snoc_flat_root`）
    `srow = 0` かつ親が根でない … `PrefixCopies`（L2 の `wsnoc_srow0_of_prefixCopies`）
    **`srow ≥ 1`**            … **残り**（`CapSnocOpen'`）

### 12.3 `t ≥ 1` が余分に要求するもの（課題 L105 (2)）

    **ゼロ。** `liftStage_of_noTie` / `liftStage_of_wsnoc` / `Lift1_Lift1` は
    `CoreCap` には**要らない**。`Lift1` は snoc と可換なので、`t` は
    「足す 1 列の行 1 の値」を変えるだけで、`W` 所属の議論には現れない。

### 12.4 `CtxOK M v z` が要求するもの（課題 L105 (3)）

    `∀ k < |M|, ∀ t, ∀ a ≥ 2(v+t)+z,  Lift1 ((0,v,z) :: M.take k) t ∈ W a`

2 つの全称を分けて読む:

    **`∀ k`（接頭辞）… 無料**。`Wset.W_take`（`Wset.lean:2120`）が
      `M ∈ W u → M.take k ∈ W u` を無条件で与えるので、
      `k = |M|-1` の項から `k < |M|-1` の項が全部出る（§8 の空振り）。
    **`∀ t`（リフト）… 無料ではない**。これは
      「`(0,v,z) :: M.dropLast` の**接頭辞たち**に限った `LiftStage`」そのもの
      （`LiftStage : X ∈ W m → Lift1 X d ∈ W (m + 2d)`、`Wtower2.lean:36`）。

⚠ **訂正**: この file の初稿では「`CtxOK` は `capBase M v z t ∈ W a` 1 行と同値」と
書いたが、**それは目標の `(a, t)` を固定したときの話**で、`∀ t` の項は落ちない。

⟹ **`∀ t` の項の正体は「土台についての `LiftStage`」**（§15、`liftStage_capBase`）。
`Lift1_Lift1` で `Lift1 (capBase M v z t) e = capBase M v z (t+e)` なので、
`CtxOK` はそのまま `Lift1 (capBase) e ∈ W (2(v+t)+z + 2e)` を与える —— これは
`LiftStage` の結論と**段まで一致**する。⟹ 塔の第 `k` 写しの行 1 リフト `k*d1` は
無料。**残るのは段の帳尻だけ**で、それは §14 のとおり `W_add` では組めない。

⟹ 系: **`CapSnocOpen'` から `WSnoc` は出ない**（一般の `C ∈ W u` に対して
`CtxOK` を作るには `LiftStage` が要る）。§8 の `SnocPrefixOpen` と違い、
`CapSnocOpen'` は本当に `WSnoc` より弱い。

### 12.5 ⚠ `c ≤ 1` に制限できるか（SESSION §130.5 の申し送りへの回答）

**Lean の文の上では制限できない。** `CoreCap` の `c` は `cap` の末尾列の行 2 で、
`coreSingleton_of_cap`（`Lind.lean:181`）は `CoreSingleton = ∀ b c, [(0,b,c)] ∈ GX`
の `∀ c` をそのまま要求する。そして `CorePlantCtxLift`（`Gamma.lean:723`）の `M` には
**行 2 の上界がどこにも無い**（`argOK M := ∀ p ∈ M, 0 < p.1` は行 0 だけ、
`CtxOK` は `W` 所属で根の `lev` しか抑えない）。
⟹ 「断片では `c ≤ 1`」を使うには **`argOK` か `CtxOK` に行 2 ≤ 1 を足す**必要があり、
それは `Gamma.lean` / `Lind.lean` の共有ファイルの変更になる。
**H11 の実測（`c ≥ 2` でも違反 0）どおり、制限しなくても危険は無い。**

### 12.7 課題 L107 の回答（§17 / §18）

    **`srow` を決めているのは `(b, c)` そのもの**（`srow_snoc_last`）
      `srow = 2` ⟺ **`0 < c`**（`srow_cap_eq_two_iff`）
      `srow = 0` ⟹ `b = 0` かつ `c = 0`（`srow_cap_eq_zero`）
      リフト `t` は行 1 を**増やす**方向にしか動かさない（`Lift1_snoc_row1`）
    ⚠ **`c ≤ 1` では `srow = 2` は消えない**（必要十分が `0 < c` なので `c = 1` で出る）
    ★ **`srow = 2` は起きる。しかも本線で**（`srow2_branch_live`）
      土台 `(0,0,0)(1,1,1) = ψ(Ω_ω)` に `(2,1,1)` を足す ＝ **2 行から 3 行に出る一歩**
    ★ `j0 = 0` のとき写しは `CtxOK` から**無料**（`copy_mem_of_ctxOK`）。
      残るのは**段の帳尻だけ**で、連結では組めない（§14）
    ★ `t = 0` かつ `j0 = 0` かつ `srow = 2` は **`oper_cons_tower2` そのもの**（§18.1）。
      `domT (cap M b c) m` ⟺ `j0 = 0`。そこでは残核が `graft` の再帰になる ＝
      `GX` の義務そのもの ＝ `Lind` の長さ帰納の姿

### 12.6 次の一手

1. **`CapSnocOpen'` の `srow = 1` 枝**: `oper` の定義から `d1 = 0`
   （`d1 = if 1 < i1 then … else 0`）なので、写しは**行 0 だけが増える**。
   `le0` の根祖先性（§10）と合わせると、親 `j0 = 0` の場合の写しは
   **`C` の行 0 一様シフト**になる ⟹ `shiftr01 · 0` の `W` 不変性が効くはず。
2. `srow = 2` 枝が本丸（`d1 > 0`）。ここで `CtxOK` の `∀ t` を使う（§12.4）。
3. 親 `j0 = 0`（根）の場合は塔恒等式 `oper_cons_tower1` / `oper_cons_tower2`
   （`Wset.lean:2789` / `:3231`）がそのまま当たる形になっている。その証明中の
   `key : gcopy M 0 (|M|-1) d0 0 k = shiftr01 (k*d0) 0 M.dropLast` は
   §10 の「根が全列の行 0 祖先」と同じ内容。**⟹ 開いているのは `j0 ≥ 1`。**
-/

end L105
end TRIO
