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
