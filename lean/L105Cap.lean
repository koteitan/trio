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
    · push_neg at hz2
      have hClen : 0 < C.length := List.length_pos_iff.mpr hCne
      have hself : (C ++ [p]) ∈ Wself :=
        snoc_zeroRow2 (M' := C) (fun q hq => by have := hz2 q hq; omega) p
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

end L105
end TRIO
