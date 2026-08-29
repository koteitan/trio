/-
L105Cap.lean: 課題 L105 —— **`CoreCap`（`Lind.lean:176`）を狙う**。

⚠⚠⚠ **このファイル全体への注意（2026-08-31、team-lead）**

**本文中の「実測 N 件・例外 0」はすべて、特定の母集団（箱）で測ったものである。**
箱は `tools/dbms/H1-NOTES.md`（H12）と `tools/dbms/R2-NOTES.md`（R2）に記録してあり、
**この file には転記されていないことがある。**

> **⟹ 実測の数字を、前提のない `∀` 文の裏づけとして読んではいけない。**

実際にそれで事故が起きた: `LiftFlatMapLocal`（§62）は
「R2 の実測 100%（684 万列、例外 0）」を添えて立てられたが、
**R2 が測ったのは `TowerExpBigRow2` の場面から来る `(Q,d,e)` だけ**で、
**文には前提が 1 つも無かった** ⟹ **文のままでは偽**（H12 が全数 111,132 組で反例）。
**箱が転記の途中で落ちたのは team-lead（中継役）の誤り。**

⟹ **実測を根拠として文を立てるときは、必ず「どの母集団で測ったか」を併記する**
（H12 の教訓 29、`lean/CORES.md` 冒頭）。
⟹ **「100%・例外 0」だけでは、文の全称と母集団の範囲がずれていても気づけない。**

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

⛔⛔ **この文は、このままでは偽である**（2026-08-31、H12 が全数 111,132 組で反例）。
**前提が 1 つも無い `∀ Q d e n`** だから。反例:

    `Q = (0,0,0)`,          `d = 0`, `e = 1`, `n = 2`
      左 `(0,1,0)(0,1,0)` / 右 `(0,1,0)(0,2,0)`
    `Q = (0,0,0)(1,0,0)`,   `d = 2`, `e = 1`, `n = 2`
      左 `…(2,1,0)…` / 右 `…(2,2,0)…`
      （ブロック 1 の根は**自分のブロックの錐には反射で入る**が、
        間の `(1,0,0)` が `nextrel1` の最小性を破るので**塔全体の錐には入らない**）

⚠ **「R2 の実測 100%（塔 276,876 / ブロック 1,245,942 / 列 6,846,876、例外 0）」は
この文の裏づけではない。** R2 が測ったのは **`TowerExpBigRow2` の場面から来る
`(Q,d,e)` だけ**（`d = entry R 0 (|R|-1)`、`e = entry R 1 (|R|-1) - v`、
`Q = (0,v,z) :: R.dropLast`）。**箱が転記の途中で落ちた**（team-lead の中継の誤り）。

**直し方は 2 通り。どちらも全数で反例 0:**

    (a) **`R` の言葉で述べ直す**（H12 の案）——`TowerExpBigRow2` と同じ引数
        （`R`, `v`, `z` ＋ 同じ前提）で述べ、`Q, d, e` はその中で定義する。
        **332,752 検査で反例 0。** 自由な反例 3288 件は全部どこかの前提で落ち、
        **到達可能なものは 0 件。**
        ⚠ **`Q, d, e` に前提を足すやり方では直らない**——
          `Q[0][0]=0` ＋ `argOK` ＋ `d>=1` ＋ 根が狭義最浅 を全部足しても反例が残る。
          生き残る反例を `R` に戻すと `R = (1,0,0)(2,1,1)` で **`domT R m` が落ちる**。
          **`domT` は `Q,d,e` の言葉では書けない**（`R` の末尾列の性質だから）。
    (b) **(D) を明示の前提にする**（R2 の案、推奨）——
        (i) 根が行 0 で狭義最浅（`L53.root_row0_min`（`:1604`）が場面で与える）
        (ii) **(D)**: `mTower Q d e n` の各列の「ブロック外・非根」の行 0 祖先は行 1 > `v`
        **24,510 検査で反例 0。しかも (D) が破れる 7,944 件は 1 つ残らず反例**（必要十分）。
        ★ **(D) は「ブロッカー無し」より真に弱く、ブロッカーがある 14,736 件
          （＝ 残核の側）を覆う。**
        ★ **(ii) は塔の場面では `tower_anc0_not_blocker`（§63、緑）から出る**
          （ブロック添字の扱いが要る）。⟹ **実測を仮定にせずに済む。**

⟹ **(b) で決着**（H12 が R2 より広い箱・全数 152,208 件で**独立に検算**、2026-08-31）:

    根が狭義最浅 ∧ **(D)**          **60,384 件  反例 0**
    　うち **ブロッカーあり**        **40,800 件（67.6%）反例 0**
    根が狭義最浅 ∧ **(D) 破れ**      26,160 件  **26,160 件すべて反例**

★★ **(D) は「根が狭義最浅」のもとで必要十分**（破れる側が 1 つ残らず反例）
★ **ブロッカーがある場合を 67.6% 覆う** ⟹ 「ブロッカー無し」（既に無料）の外へ確かに出ている
⟹ **`Q d e` のまま `iff` の形で立てられる。下流も触らずに済む。
   (a)（`R` の言葉で述べ直す）は不要。** -/
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


/-! ## 63. ★★★★★★ R2 の (D) に **機構が付きました**

R2 が「機構は導けていない」と書いた (D)

> **塔の第 `k` ブロック（`k ≥ 1`）の行 0 祖先鎖の、ブロック外の祖先は
> 1 本もブロッカーでない（行 1 > `v`）**（346,320 件・例外 0）

は、**塔の場面の仮定 `hasParent` からそのまま出ます。**

### 63.1 骨（`le1_zero_iff` の直接の帰結）

`srow = 2` の塔では `L53.tower2_root_spec`（`L53Subst.lean:2360`）が
**`nextrel2 ((0,v,z) :: R) 0 |R|`** を与える。その第 5 連言が **`le1 X 0 |R|`**。
そして `Lcone.le1_zero_iff`（`:36`、根が行 0 で狭義最浅 ＝ `L53.root_row0_min`）は

    `le1 X 0 |R|` ⟺ **`|R|` の根以外の行 0 祖先 `y` がすべて `entry X 1 0 = v < entry X 1 y`**

⟹ **`X` の末尾列の（根以外の）行 0 祖先は 1 本もブロッカーでない。** -/

theorem tower_anc0_not_blocker {v z m : ℕ} {R : TrioSeq} (hR : argOK R)
    (hRne : R ≠ []) (hd : domT R m) (hi2 : srow R (R.length - 1) = 2)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) :
    ∀ y, Relation.ReflTransGen (nextrel0 (((0, v, z) : ℕ × ℕ × ℕ) :: R)) y R.length →
      y ≠ 0 → v < entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 y := by
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hlt : R.length < (((0, v, z) : ℕ × ℕ × ℕ) :: R).length := by
    simp only [List.length_cons]; omega
  have hle1 : le1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 R.length :=
    (L53.tower2_root_spec hRne hd hi2 hpM).2.2.2.2.1
  have hv : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 0 = v := by simp [entry]
  have hres := (le1_zero_iff (L53.root_row0_min hR) hlt).mp hle1
  intro y hy hy0
  have := hres y hy hy0
  rwa [hv] at this

/-! ### 63.2 ⟹ なぜそれが (D) になるか（設計図）

塔のブロック `k`（`k ≥ 1`）の**根**は、`Q = (0,v,z) :: R.dropLast` の根を
行 0 で `k*d` ずらしたもの（`d = entry R 0 (|R|-1)`）。
一方 `X = (0,v,z) :: R` の**末尾列**は行 0 が `d`。

⟹ **`k*d = d + (k-1)*d`** なので、**ブロック `k` の根は「`X` の末尾列をブロック `k-1` の
座標系に置いたもの」**であり、その行 0 の親も同じ対応でうつる。

⟹ **ブロック `k` の根のブロック外の祖先 ＝ `X` の末尾列の（根以外の）行 0 祖先の像。**
そして上の `tower_anc0_not_blocker` がそれらを**すべて非ブロッカー**にする。
（ブロック `k'` に落ちた像の行 1 は `Q` の行 1 ＋ `k'*e`（錐の上）で、**減らない** ⟹
`v` より大きいまま。）

⟹ **(D) の機構はこれ。R2 の実測 346,320 件・例外 0 と一致する。**

⚠ **まだ (D) 自体の証明ではない。** 上の「対応」を Lean で書くには
ブロックの添字づけ（`mTower` の flatMap の第 `k` 成分）を扱う必要がある。
だが **機構が仮定から出ることは確定した**ので、
**`LiftFlatMapLocal`（§62）は「実測で真」から「仮定から出るはず」に格上げされた。**

### 63.3 ⟹ R2 の設計図の現状

    1. `le1 Bk 0 i ↔ le1 Q 0 i`             ← **`le1_block`（§60、緑）**
    2. 鎖のブロック内部分 ＝ 単体の鎖         ← `Core.le0_shiftr01` ＋ `Wset.le1_Lift1`（緑）で出るはず
    3. **鎖のブロック外の祖先は行 1 > `v`**   ← **`tower_anc0_not_blocker`（上、緑）が中身**
    4. 1+2+3 ＋ `le1_zero_iff` ⟹ (B) ⟹ §231 ⟹ `mTower = operTower`

**⟹ 3 の「本当の補題」は塔の仮定から出た。残るのは 2 と、ブロック添字の機械的な扱いだけ。** -/

/-! ## 64. ★★★★★★ 課題 L136-2: **`v = 0` の残核は 2 本ではなく 1 本**

### 64.1 ⚠ §61.2 の自己訂正: 段は `z = 0` でも `z = 1` でも両側から消える

私は §61.2 で「`z = 0` と `z = 1` は前提の段が `0` と `1` で違うから**別々に扱う**」と
書いた。**文の形としては誤りである。** `LiftTieCore` は前提の段も結論の段も
**根の `lev` ちょうど**なので、`Wtower2.mem_Wself_iff` で**両側から段が消える**:

    `lev ((0,v,z) :: R) 0            = 2v + z`       （`lev_cons_root`、§46）
    `lev (Lift1 ((0,v,z) :: R) d) 0  = 2(v+d) + z`   （下の `lev_cons_lift`）

⟹ **`LiftTieCore` は段をまったく含まない 1 文と同値**であり、`z` は文の形を変えない。
段の違いが効くのは**証明の道具**（前提側で節 3 が使えるか）だけで、**核の本数ではない**。 -/

theorem lev_cons_lift (v z d : ℕ) (R : TrioSeq) :
    lev (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d) 0 = 2 * (v + d) + z := by
  have hne : (((0, v, z) : ℕ × ℕ × ℕ) :: R) ≠ [] := by simp
  unfold lev
  rw [L53.entry1_Lift1_zero hne, entry2_Lift1]
  simp [entry]

/-- **前提側の段は無料。** -/
theorem cons_mem_W_iff_self (v z : ℕ) (R : TrioSeq) :
    (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ W (2 * v + z)
      ↔ (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ Wself := by
  rw [mem_Wself_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, by rw [lev_cons_root]⟩⟩

/-- **結論側の段も無料。** -/
theorem lift_cons_mem_W_iff_self (v z d : ℕ) (R : TrioSeq) :
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d ∈ W (2 * (v + d) + z)
      ↔ Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) d ∈ Wself := by
  rw [mem_Wself_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, by rw [lev_cons_lift]⟩⟩

/-- **★★★★★★ `LiftTieCore` の段抜き版**: `W` の添字が 1 つも現れない。 -/
def LiftTieCoreSelf : Prop :=
  ∀ (v z : ℕ) (R : TrioSeq), argOK R → (∃ p ∈ R, p.2.1 = v) →
    ¬ (1 ≤ v ∧ TieFree (((0, v, z) : ℕ × ℕ × ℕ) :: R)) →
    (((0, v, z) : ℕ × ℕ × ℕ) :: R) ∈ Wself →
    Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 ∈ Wself

/-- **★★★★★★ 段抜き版は元の核と同値。** -/
theorem liftTieCoreSelf_iff_core : LiftTieCoreSelf ↔ LiftTieCore := by
  have harith : ∀ v z : ℕ, 2 * v + z + 2 = 2 * (v + 1) + z := by intro v z; omega
  constructor
  · intro h v z R hR ht htf hX
    rw [harith v z, lift_cons_mem_W_iff_self]
    exact h v z R hR ht htf ((cons_mem_W_iff_self v z R).mp hX)
  · intro h v z R hR ht htf hX
    have hres := h v z R hR ht htf ((cons_mem_W_iff_self v z R).mpr hX)
    rw [harith v z, lift_cons_mem_W_iff_self] at hres
    exact hres

/-! ### 64.1.1 ⟹ `v = 0` の残核は **1 文**（`z` は助変数）

`z = 0` と `z = 1` を段抜きの形で書くと**まったく同じ文**になる。 -/

/-- **★★★★★ `v = 0` の残核**（§59 の `LiftTieCoreZero` と §61 の `LiftTieCoreOne` を
1 文にまとめたもの。段が消えているので `z` は形を変えない）。 -/
def LiftTieZeroSelf : Prop :=
  ∀ (z : ℕ) (R : TrioSeq), argOK R → (∃ p ∈ R, p.2.1 = 0) →
    (((0, 0, z) : ℕ × ℕ × ℕ) :: R) ∈ Wself →
    Lift1 (((0, 0, z) : ℕ × ℕ × ℕ) :: R) 1 ∈ Wself

theorem liftTieZeroSelf_of_core (h : LiftTieCoreSelf) : LiftTieZeroSelf :=
  fun z R hR ht hX => h 0 z R hR ht (by rintro ⟨h1, -⟩; omega) hX

theorem liftTieCoreZero_of_zeroSelf (h : LiftTieZeroSelf) : LiftTieCoreZero := by
  intro R hR ht hX
  have hin : (((0, 0, 0) : ℕ × ℕ × ℕ) :: R) ∈ W (2 * 0 + 0) := by simpa using hX
  have hres := h 0 R hR ht ((cons_mem_W_iff_self 0 0 R).mp hin)
  have hout := (lift_cons_mem_W_iff_self 0 0 1 R).mpr hres
  simpa using hout

theorem liftTieCoreOne_of_zeroSelf (h : LiftTieZeroSelf) : LiftTieCoreOne := by
  intro R hR ht hX
  have hin : (((0, 0, 1) : ℕ × ℕ × ℕ) :: R) ∈ W (2 * 0 + 1) := by simpa using hX
  have hres := h 1 R hR ht ((cons_mem_W_iff_self 0 1 R).mp hin)
  have hout := (lift_cons_mem_W_iff_self 0 1 1 R).mpr hres
  simpa using hout

/-! ## 65. ⚠ 課題 L135-2 の答え: **結論側の節 3 は新しいものを与えません**

team-lead の指示「**結論側の節 3 で作る**」を定義から詰めた。答えは**否**である。

`Aop` の節 3 は `domT M m` を要求し、`domT` の第 2 成分は **`¬ hasParent`** である
（`Wset.lean:61`）。そして `Lift1` は **長さも `srow` も `hasParent` も変えない**
（`Lift1_length` / `Wset.srow_Lift1` / `Wset.hasParent_Lift1`）ので

    **`domT (Lift1 X d) m` ⟹ `¬ hasParent X (srow X (|X|-1)) (|X|-1)`**

そして親が無ければ `Wtower2.lift_oper_of_noParent` で **`Lift1` は `oper` と可換**、
つまり **(WL) はそこではすでに無料**である。

> **⟹ 結論側で節 3 が使える場所 ＝ すでに無料の場所。**
> 節 3 は残差（親あり）にはまったく届かない。 -/

theorem noParent_of_domT_Lift1 {X : TrioSeq} {d m : ℕ} (h2 : 2 ≤ X.length)
    (h : domT (Lift1 X d) m) :
    ¬ hasParent X (srow X (X.length - 1)) (X.length - 1) := by
  have hlen : (Lift1 X d).length = X.length := Lift1_length X d
  have hL : X.length - 1 ≠ 0 := by omega
  have hnp := h.2
  rw [hlen, Wset.srow_Lift1 hL, hasParent_Lift1] at hnp
  exact hnp

/-- ⟹ **節 3 が使える場面では `Lift1` と `oper` の可換性がすでに無料**。 -/
theorem lift_oper_comm_of_domT_Lift1 {X : TrioSeq} {d m n : ℕ} (h2 : 2 ≤ X.length)
    (h : domT (Lift1 X d) m) :
    (Lift1 X d)⟦n⟧ = Lift1 (X⟦n⟧) d :=
  lift_oper_of_noParent h2 (noParent_of_domT_Lift1 h2 h)

/-! ## 66. ★★★★★ 段 0 の残差を**厳密に**書く

`A2'` の帰納を段 0 で全部回すと、残るのは**ちょうど 1 つの場面**である。

    節 1（`|X| ≤ 1`）     … 無料（`Lift1_of_length_one` ＋ `singleton_mem_W`）
    節 3（`∃ m < 0`）     … **空**（段 0 なので）
    節 2 の `|X| ≤ 1`     … 無料（`oper_eq_self_of_short`）
    節 2 の **親なし**    … 無料（`lift_oper_of_noParent`）
    節 2 の **親あり**    … **残差**

帰納法の仮定は **2 成分**（`X⟦n⟧ ∈ W 0` と `Lift1 (X⟦n⟧) 1 ∈ W 2`）で持てるので、
そこまで込みで書く。根の `lev` が `0` であることも `lev_root_le_of_mem_W` で無料。 -/

/-- **★★★★★ 段 0 の残差**（`A2'` の帰納を全部回した後に残る 1 文）。 -/
def LiftParented0 : Prop :=
  ∀ (X : TrioSeq), 2 ≤ X.length → lev X 0 = 0 →
    hasParent X (srow X (X.length - 1)) (X.length - 1) →
    (∀ n, 1 ≤ n → X⟦n⟧ ∈ W 0 ∧ Lift1 (X⟦n⟧) 1 ∈ W 2) →
    ∀ n, 1 ≤ n → (Lift1 X 1)⟦n⟧ ∈ W 2

/-- **★★★★★ 段 0 の (WL) は残差だけから出る。** -/
theorem liftStage0_of_parented0 (h : LiftParented0) :
    ∀ X ∈ W 0, Lift1 X 1 ∈ W 2 := by
  have hsub : W 0 ⊆ {X : TrioSeq | X ∈ W 0 ∧ Lift1 X 1 ∈ W 2} := by
    refine A2' ?_
    rintro X (⟨hl, hlev⟩ | hop | ⟨m', hm', -, -⟩)
    · refine ⟨A1_intro (Or.inl ⟨hl, hlev⟩), ?_⟩
      rcases Nat.eq_zero_or_pos X.length with h0 | hpos
      · have hnil : X = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        show Lift1 ([] : TrioSeq) 1 ∈ W 2
        simpa using W_nil 2
      · have h1 : X.length = 1 := by omega
        show Lift1 X 1 ∈ W 2
        rw [Lift1_of_length_one h1 1]
        have hbc : entry X 1 0 = 0 ∧ entry X 2 0 = 0 := by
          unfold lev at hlev; omega
        rw [hbc.1, hbc.2]
        exact singleton_mem_W (by omega)
    · have hX0 : X ∈ W 0 := mem_of_oper_mem (fun n hn => (hop n hn).1)
      refine ⟨hX0, ?_⟩
      rcases Nat.lt_or_ge X.length 2 with hsm | hbig
      · have hres := (hop 1 le_rfl).2
        rwa [oper_eq_self_of_short 1 (by omega)] at hres
      · have hXne : X ≠ [] := by
          intro hc
          rw [hc] at hbig
          simp at hbig
        have hlev0 : lev X 0 = 0 := Nat.le_zero.mp (lev_root_le_of_mem_W hX0 hXne)
        by_cases hp : hasParent X (srow X (X.length - 1)) (X.length - 1)
        · exact mem_of_oper_mem (h X hbig hlev0 hp (fun n hn => hop n hn))
        · refine mem_of_oper_mem (fun n hn => ?_)
          rw [lift_oper_of_noParent hbig hp]
          exact (hop n hn).2
    · exact absurd hm' (Nat.not_lt_zero m')
  exact fun X hX => (hsub hX).2

/-- ⟹ **`v = 0, z = 0` の核は残差から出る**（`argOK` もタイも要らない）。 -/
theorem liftTieCoreZero_of_parented0 (h : LiftParented0) : LiftTieCoreZero :=
  fun _ _ _ hX => liftStage0_of_parented0 h _ hX

/-! ### 66.1 ⟹ 残差の中身

`LiftParented0` の場面では、`X ∈ W 0`（帰納法の仮定の第 1 成分から `mem_of_oper_mem`）
なので **根は `(d, 0, 0)`**（`lev X 0 = 0`）。⟹ `Lcone.le1_zero_iff` により

    **`le1 X 0 j` ⟺ `j` の（根以外の）行 0 祖先がすべて 行 1 ≥ 1**
    **ブロッカー ＝ 行 1 が 0 の列**（`v = 0` なのでタイとブロッカーが一致。§59.1）

そして残差の目標は `(Lift1 X 1)⟦n⟧ ∈ W 2` で、帰納法の仮定は
`Lift1 (X⟦n⟧) 1 ∈ W 2`。両者は `Wtower2` のサンドイッチ

    `Le1 (Lift1 (X⟦n⟧) 1) ((Lift1 X 1)⟦n⟧)`          （`Le1_Lift1_oper`、緑）
    `Le1 ((Lift1 X 1)⟦n⟧) (shiftr01 0 1 (X⟦n⟧))`      （`Le1_oper_Lift1_shiftr01`、緑）

で**上下から挟まれている**。⟹ **残差は「挟まれた中間が `W 2` に入る」ことに等しい**
（上端は `ulift_mem_W` で無料、下端は帰納法の仮定）。

⚠ **これは `WConvex` の段 0・`d = 1` の場合そのもの**なので、
**この道は既知の核 `WConvex` に合流する**。段 0 だからといって近道にはならない。
（`liftStage_of_wconvex`（`Wtower2.lean`、緑）が一般の段でこれをやっている。）

### 66.2 ⟹ 段 0 で本当に得したもの

    **節 3 が消える**（`∃ m < 0` が空）… `aop_clause3_to_clause2` を使わなくてよい
    **根が `(d,0,0)` に固定**       … ブロッカー ＝ 行 1 が 0 の列（いちばん単純な錐）
    **帰納法の仮定が 2 成分**       … `X⟦n⟧ ∈ W 0` も同時に持てる

⟹ **得たのは場面の単純さだけで、新しい推論規則は増えていない。**
段 0 でも本質は「親ありの 1 歩で `Lift1` と `oper` が可換でない」ところに集約される。 -/

/-! ## 67. ★★★★★★ 課題 L136-3: **(WL) の 1 歩の残差は「悪根 ＝ 根」だけ**

⚠ **新しい補題はひとつも証明していない。** 既存の `Lcone.liftInner_holds`（無条件・緑）を
私の残差（§66）に当てただけである。だが**`LiftTieCore` の残差の位置が確定する。**

`Wset.LiftInner`（`Wset.lean:4028`）は

    `argOK R` ＋ `R ≠ []` ＋ **`hasParent R (srow R (|R|-1)) (|R|-1)`**
      ⟹ `(Lift1 ((0,v,z) :: R) t)⟦n⟧ = Lift1 (((0,v,z) :: R)⟦n⟧) t`

で、**`Lcone.liftInner_holds`（`Lcone.lean:507`）が仮定ゼロで証明している**。
前提の `hasParent` は **`R` の中**の親、つまり `X = (0,v,z) :: R` で見て
**悪根 `j0 ≥ 1`**（引数ブロックの内側）である。

⟹ `X = (0,v,z) :: R` の **1 歩**については、可換でない可能性があるのは 1 通りだけ:

    (A) `¬ hasParent X (srow X (|X|-1)) (|X|-1)` … `lift_oper_of_noParent` で**可換**
    (B) `hasParent R (srow R (|R|-1)) (|R|-1)`   … **`liftInner_holds` で可換**
    (C) どちらでもない                          … **残差 ＝ 悪根が根 (`j0 = 0`)**
-/

/-- (A) 親なしの枝（`Wtower2.lift_oper_of_noParent` の cons 版）。 -/
theorem lift_oper_comm_cons_noParent {v z t n : ℕ} {R : TrioSeq} (hne : R ≠ [])
    (hnp : ¬ hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R)
        (srow (((0, v, z) : ℕ × ℕ × ℕ) :: R) R.length) R.length) :
    (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t)⟦n⟧
      = Lift1 ((((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧) t := by
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hne
  have h2 : 2 ≤ (((0, v, z) : ℕ × ℕ × ℕ) :: R).length := by
    simp only [List.length_cons]; omega
  refine lift_oper_of_noParent h2 ?_
  have hL : (((0, v, z) : ℕ × ℕ × ℕ) :: R).length - 1 = R.length := by
    simp only [List.length_cons]
    omega
  rw [hL]
  exact hnp

/-- **★★★★★ (A) ∪ (B) では `Lift1` と `oper` は可換**。 -/
theorem lift_oper_comm_cons {v z t n : ℕ} {R : TrioSeq} (hR : argOK R) (hne : R ≠ [])
    (h : hasParent R (srow R (R.length - 1)) (R.length - 1) ∨
        ¬ hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R)
            (srow (((0, v, z) : ℕ × ℕ × ℕ) :: R) R.length) R.length) :
    (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t)⟦n⟧
      = Lift1 ((((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧) t := by
  rcases h with hp | hnp
  · exact liftInner_holds v z t n R hR hne hp
  · exact lift_oper_comm_cons_noParent hne hnp

/-- **★★★★★★ 残差の場面 (C)**: `R` の末尾列は `R` の中では**孤児**だが、
根を足すと**親を持つ** ＝ **悪根が根**。 -/
def RootBadScene (v z : ℕ) (R : TrioSeq) : Prop :=
  ¬ hasParent R (srow R (R.length - 1)) (R.length - 1) ∧
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R)
      (srow (((0, v, z) : ℕ × ℕ × ℕ) :: R) R.length) R.length

/-- **★★★★★★ 残差の場面でなければ 1 歩は無料。** -/
theorem lift_oper_comm_of_not_rootBad {v z t n : ℕ} {R : TrioSeq} (hR : argOK R)
    (hne : R ≠ []) (h : ¬ RootBadScene v z R) :
    (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t)⟦n⟧
      = Lift1 ((((0, v, z) : ℕ × ℕ × ℕ) :: R)⟦n⟧) t := by
  refine lift_oper_comm_cons hR hne ?_
  by_cases hp : hasParent R (srow R (R.length - 1)) (R.length - 1)
  · exact Or.inl hp
  · exact Or.inr (fun hc => h ⟨hp, hc⟩)

/-! ### 67.1 ⟹ 残差の場面は **`domT` の場面**（＝ 塔の場面）

`RootBadScene` の第 1 成分は **`domT R m` の第 2 成分そのもの**である
（`domT R m := lev R (|R|-1) = m+1 ∧ ¬ hasParent R (srow R (|R|-1)) (|R|-1)`）。 -/

/-! ⚠ **自己訂正（5 回目）**: ここで `srow_cons_last` と `entry_cons_last` を
書きかけたが、**両方とも `Wset` に既にある**（`Wset.lean:1765` / `:1745`）。
**書く前に grep** —— 自分で H12 に言った規律にまた違反した。以下は `Wset` のものを使う。 -/

/-- ⟹ **残差の場面は `LiftTower1` / `LiftTowerExp2` の `hasParent` 前提そのもの**。 -/
theorem hasParent_rootBadScene {v z : ℕ} {R : TrioSeq} (hne : R ≠ [])
    (h : RootBadScene v z R) :
    hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length := by
  have := h.2
  rwa [srow_cons_last hne] at this

theorem domT_of_rootBadScene {v z m : ℕ} {R : TrioSeq} (h : RootBadScene v z R)
    (hlev : lev R (R.length - 1) = m + 1) : domT R m :=
  ⟨hlev, h.1⟩

/-- **★★★★★★ 残差の場面では悪根は本当に根**（`lev R (|R|-1) ≥ 1` のとき）。
`Wset.parent_cons_eq_zero`（`:2762`、緑）をそのまま当てる。 -/
theorem parent_eq_zero_of_rootBadScene {v z m : ℕ} {R : TrioSeq} (hne : R ≠ [])
    (h : RootBadScene v z R) (hlev : lev R (R.length - 1) = m + 1) :
    parent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1)) R.length = 0 :=
  parent_cons_eq_zero hne (domT_of_rootBadScene h hlev) (hasParent_rootBadScene hne h)

/-- `lev = 0` なら `srow = 0`（行 1 も行 2 も 0）。 -/
theorem srow_eq_zero_of_lev_zero {R : TrioSeq} {j : ℕ} (h : lev R j = 0) :
    srow R j = 0 := by
  unfold lev at h
  unfold srow
  rw [if_neg (by omega), if_neg (by omega)]

/-! ### 67.2 ★★★★★★ ⟹ **`LiftTieCore` の残差 ＝ 既存の塔核 2 本**

`RootBadScene v z R` のもとで `lev R (|R|-1)` を場合分けすると:

    `lev R (|R|-1) = 0`     ⟹ `srow R (|R|-1) = 0`（`srow_eq_zero_of_lev_zero`）
                              ⟹ **`snoc_flat_root` の場面 ＝ 無料**（§12.2）
    `lev R (|R|-1) = m+1`   ⟹ **`domT R m`**（`domT_of_rootBadScene`）
        `srow R (|R|-1) = 1` ⟹ **`Wset.LiftTower1`**（`Wset.lean:4034`）の前提そのもの
        `srow R (|R|-1) = 2` ⟹ **`Wset.LiftTowerExp2`**（`Wset.lean:4045`）の前提そのもの

⟹ **`LiftTieCore` の 1 歩の残差は、本線の既存核 `LiftTower1` / `LiftTowerExp2` と
同じ場面である。** 私が §29 以来「経路 C」と呼んでいたものは、
**`Wset.Wstar2_closed`（`Wset.lean:4221`、緑）が使っている分解と同じ場所に落ちる。**

> **⟹ 核 (1)「`LiftTieCore`」と 核 (2)「塔が `Wself` に閉じる」は独立ではない。**
> **同じ場面（悪根 ＝ 根、`srow ∈ {1,2}`）の 2 つの言い方である。**

⚠ **ただし「(1) が (2) から出る」とはまだ言えない。** 上は **1 歩**の可換性の話で、
`LiftTieCore` の帰納をこれで回すには `X = (0,v,z) :: R` という**形と `argOK R` が
展開で保たれる**ことが要る。それを保つための道具が本線の `Wstar2`
（`Wset.lean:3451`、`v z a t` を束ねた Π 命題）で、**その閉包定理
`Wstar2_closed` はすでに `LiftInner ＋ LiftTower1 ＋ LiftTowerExp2` に還元済み**である。

### 67.3 ⚠ (C) では本当に可換でない（`srow = 0` の具体例）

`srow X (|X|-1) = 0` かつ悪根 `= 0` のとき `oper` の定義から
`i1 = 0` ⟹ `d0 = 0` かつ `d1 = 0` なので、`X⟦n⟧` は **`X.dropLast` をそのまま `n` 個
並べたもの**になる。各写しの先頭は行 0 が `0` なので**行 0 の根**であり、
`k ≥ 1` の写しの列は `le0 (X⟦n⟧) 0 ·` を**満たさない** ⟹ `Lift1 (X⟦n⟧) 1` はそこを
**持ち上げない**。一方 `(Lift1 X 1)⟦n⟧` は持ち上げ済みの値を全写しに複製する。
⟹ **一致しない。**（この枝は `snoc_flat_root` が別経路で片づけるので害は無い。）

⟹ **(C) は「可換性では閉じない」ことが定義から見える。** サンドイッチ
（`Le1_Lift1_oper` / `Le1_oper_Lift1_shiftr01`）が要るのはここだけである。 -/

/-! ## 68. ★★★★★★ 課題 H73 の答え: **`mTower` は `oper` そのもの**

§67 で残差が「**悪根 ＝ 根**」に絞れた。そこで `Lcone.oper_eq_gexp_gen`
（`Lcone.lean:487`、**任意の悪根**、緑）を **`j0 = 0`** で読むと、`gexp` の
`M.take j0` の部分が**空**になり

    `M⟦n⟧ = gexp M 0 (|M|-1) d0 d1 n = gcopies M 0 (|M|-1) d0 d1 n`

そして `gcopy M 0 L d0 d1 k` は定義から

    `(range' 0 L).map fun j => (entry M 0 j + k*d0,
                               entry M 1 j + (if le1 M 0 j then k*d1 else 0),
                               entry M 2 j)`

で、これは **`Lift1 (shiftr01 (d0*k) 0 (M.take L)) (d1*k)`** に等しい
（`Core.le1_shiftr01` ＋ `Wset.le1_take` で錐が一致するから）。
**⟹ `mTower` の第 `k` ブロックそのもの。**

> **★★★★★★ `M⟦n⟧ = mTower M.dropLast d0 d1 n`。`mTower` は `oper` の別名だった。** -/

theorem gcopy_zero_eq_lift {M : TrioSeq} {L d0 d1 k : ℕ} (hL : L ≤ M.length) :
    gcopy M 0 L d0 d1 k = Lift1 (shiftr01 (d0 * k) 0 (M.take L)) (d1 * k) := by
  have hlen : (shiftr01 (d0 * k) 0 (M.take L)).length = L := by
    rw [shiftr01_length, List.length_take]; omega
  unfold gcopy Lift1
  rw [hlen, ← List.range_eq_range']
  refine List.map_congr_left ?_
  intro j hj
  have hjL : j < L := List.mem_range.mp hj
  have hjT : j < (M.take L).length := by rw [List.length_take]; omega
  have h0 : entry (shiftr01 (d0 * k) 0 (M.take L)) 0 j = entry M 0 j + d0 * k := by
    rw [entry0_shiftr01 hjT, entry_take hjL]
  have h1 : entry (shiftr01 (d0 * k) 0 (M.take L)) 1 j = entry M 1 j := by
    rw [entry1_shiftr01, entry_take hjL]
  have h2 : entry (shiftr01 (d0 * k) 0 (M.take L)) 2 j = entry M 2 j := by
    rw [entry2_shiftr01, entry_take hjL]
  have hc : le1 (shiftr01 (d0 * k) 0 (M.take L)) 0 j ↔ le1 M 0 j := by
    rw [le1_shiftr01, le1_take hL hjL]
  have hif : (if le1 M 0 j then k * d1 else 0)
      = (if le1 (shiftr01 (d0 * k) 0 (M.take L)) 0 j then d1 * k else 0) := by
    by_cases hcone : le1 M 0 j
    · rw [if_pos hcone, if_pos (hc.mpr hcone), Nat.mul_comm]
    · rw [if_neg hcone, if_neg (fun hh => hcone (hc.mp hh))]
  rw [h0, h1, h2, hif, Nat.mul_comm k d0]

/-- **★★★★★ `j0 = 0` の `gexp` は `mTower`**。 -/
theorem gexp_zero_eq_mTower {M : TrioSeq} {L d0 d1 n : ℕ} (hL : L ≤ M.length) :
    gexp M 0 L d0 d1 n = mTower (M.take L) d0 d1 n := by
  unfold gexp gcopies mTower
  rw [List.take_zero, List.nil_append]
  exact List.flatMap_congr (fun k _ => gcopy_zero_eq_lift hL)

open Classical in
/-- **★★★★★★ 悪根が根なら展開は `mTower` そのもの。** -/
theorem oper_eq_mTower {M : TrioSeq} (n : ℕ) (hL : M.length - 1 ≠ 0)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hj0 : parent M (srow M (M.length - 1)) (M.length - 1) = 0) :
    M⟦n⟧ = mTower M.dropLast
      (if 0 < srow M (M.length - 1) then entry M 0 (M.length - 1) - entry M 0 0
        else 0)
      (if 1 < srow M (M.length - 1) then entry M 1 (M.length - 1) - entry M 1 0
        else 0) n := by
  have hgen := oper_eq_gexp_gen (M := M) n hL hz hp
  rw [hj0] at hgen
  rw [hgen, show M.length - 1 - 0 = M.length - 1 from by omega,
    gexp_zero_eq_mTower (by omega), List.dropLast_eq_take]

/-! ## 69. ★★★★★★ **`operTower = mTower` は定理**（H73 / `LiftFlatMapLocal` は不要）

§68 で `M⟦n⟧ = mTower M.dropLast d0 d1 n`（悪根が根）が出た。一方 §47 の
`tower2_eq_operTower` は同じ `X⟦n⟧` を **`operTower`** で書いている。
**⟹ 両者は同じものの 2 通りの書き方なので、等しい。仮定は要らない。**

> **★★★★★★ R2 の実測「`mTower = operTower` 100%（276,876 塔・例外 0）」は定理だった。**
> **`LiftFlatMapLocal`（§62）を経由する必要はない。** -/

open Classical in
/-- **★★★★★★ 塔の場面では `operTower` と `mTower` は等しい**（仮定は場面のみ）。 -/
theorem operTower_eq_mTower_tower2 {v z m : ℕ} {R : TrioSeq} (hR : argOK R)
    (hRne : R ≠ []) (hd : domT R m) (hi2 : srow R (R.length - 1) = 2)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) (n : ℕ) :
    operTower (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) (entry R 0 (R.length - 1))
        (entry R 1 (R.length - 1) - v) n
      = mTower (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) (entry R 0 (R.length - 1))
        (entry R 1 (R.length - 1) - v) n := by
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hXl1 : (((0, v, z) : ℕ × ℕ × ℕ) :: R).length - 1 = R.length := by
    simp only [List.length_cons]; omega
  have hsrow : srow (((0, v, z) : ℕ × ℕ × ℕ) :: R)
      ((((0, v, z) : ℕ × ℕ × ℕ) :: R).length - 1) = 2 := by
    rw [hXl1, srow_cons_last hRne, hi2]
  have hp : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R)
      (srow (((0, v, z) : ℕ × ℕ × ℕ) :: R)
        ((((0, v, z) : ℕ × ℕ × ℕ) :: R).length - 1))
      ((((0, v, z) : ℕ × ℕ × ℕ) :: R).length - 1) := by
    rw [hXl1, srow_cons_last hRne]
    exact hpM
  have hj0 : parent (((0, v, z) : ℕ × ℕ × ℕ) :: R)
      (srow (((0, v, z) : ℕ × ℕ × ℕ) :: R)
        ((((0, v, z) : ℕ × ℕ × ℕ) :: R).length - 1))
      ((((0, v, z) : ℕ × ℕ × ℕ) :: R).length - 1) = 0 := by
    rw [hXl1, srow_cons_last hRne]
    exact parent_cons_eq_zero hRne hd hpM
  have hzz : ¬ (entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0
        ((((0, v, z) : ℕ × ℕ × ℕ) :: R).length - 1) = 0 ∧
      entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1
        ((((0, v, z) : ℕ × ℕ × ℕ) :: R).length - 1) = 0 ∧
      entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 2
        ((((0, v, z) : ℕ × ℕ × ℕ) :: R).length - 1) = 0) := by
    rintro ⟨-, -, h⟩
    rw [hXl1, entry_cons_last hRne] at h
    have := L53.srow_two_row2_pos hi2
    omega
  have hmt := oper_eq_mTower (M := ((0, v, z) : ℕ × ℕ × ℕ) :: R) n
    (by omega) hzz hp hj0
  rw [hsrow] at hmt
  rw [if_pos (show (0 : ℕ) < 2 from by omega), if_pos (show (1 : ℕ) < 2 from by omega),
    hXl1, entry_cons_last hRne, entry_cons_last hRne, dropLast_cons hRne] at hmt
  have hr0 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 0 0 = 0 := by simp [entry]
  have hr1 : entry (((0, v, z) : ℕ × ℕ × ℕ) :: R) 1 0 = v := by simp [entry]
  rw [hr0, hr1, Nat.sub_zero] at hmt
  rw [← tower2_eq_operTower hR hRne hd hi2 hpM n, hmt]

/-! ### 69.1 ⟹ `LiftFlatMapLocal` は**不要**になった

§62 で「未証明の的」としていた `LiftFlatMapLocal` は、`operTower = mTower` を得るための
**手段**だった。§69 でその結論が**直接**出たので、的そのものは要らない。

    §62 の道筋（廃止）: `LiftFlatMapLocal`（未証明）⟹ `operTower_eq_mTower` ⟹ `operTower_succ`
    §69 の道筋（緑）  : `oper_eq_gexp_gen`（緑）⟹ `oper_eq_mTower`（§68、緑）
                        ＋ `tower2_eq_operTower`（§47、緑）⟹ **`operTower_eq_mTower_tower2`**

⚠ **`LiftFlatMapLocal` が一般の `Q d e n` で真かどうかは、依然として未解決**である
（§69 は**塔の場面の助変数**についてしか言っていない）。だが**塔の場面しか使わない**ので、
**核から落とせる。**

### 69.2 ⟹ `operTower` の succ 形も無条件で出る

`mTower_succ`（§55）が `mTower Q d e (n+1) = mTower Q d e n ++ Lift1 (shiftr01 (d*n) 0 Q) (e*n)`
を無条件で与えるので、`operTower_eq_mTower_tower2` を通せば **`operTower` の succ 形**が
塔の場面で使える。⟹ §62.1 の「的が落ちたあとの道筋」が**そのまま開通**する:

    `oper_shTower`（§48）/ `oper_shTower2`（§56）と同じ技法が使える
    **(2) の帰納が `srow = 1` 側とまったく同じ形になる** -/

open Classical in
/-- **★★★★★ 塔の場面での `operTower` の succ 形**（`LiftFlatMapLocal` 不要）。 -/
theorem operTower_succ_tower2 {v z m : ℕ} {R : TrioSeq} (hR : argOK R)
    (hRne : R ≠ []) (hd : domT R m) (hi2 : srow R (R.length - 1) = 2)
    (hpM : hasParent (((0, v, z) : ℕ × ℕ × ℕ) :: R) (srow R (R.length - 1))
      R.length) (n : ℕ) :
    operTower (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) (entry R 0 (R.length - 1))
        (entry R 1 (R.length - 1) - v) (n + 1)
      = operTower (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) (entry R 0 (R.length - 1))
          (entry R 1 (R.length - 1) - v) n
        ++ Lift1 (shiftr01 (entry R 0 (R.length - 1) * n) 0
              (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast))
            ((entry R 1 (R.length - 1) - v) * n) := by
  rw [operTower_eq_mTower_tower2 hR hRne hd hi2 hpM,
    operTower_eq_mTower_tower2 hR hRne hd hi2 hpM]
  exact mTower_succ _ _ _ _

/-! ## 70. ★★★★★ **`mTower` の展開も「最後のブロックだけ」**（§56 のマスクつき版）

§69 で `operTower = mTower`（塔の場面）が定理になったので、§56 の `oper_shTower2`
（マスク無しの `shTower2` 版）を **`mTower` そのもの**に上げる。道具は同じ:

    `L53.comm_of_hasParentInBlock`（`L53Subst.lean:922`、緑）
    `hasParentInBlock_shiftr01`（§49、緑）＋ 下の `hasParentInBlock_Lift1`

⚠ §56 では行 1 の一様シフト `shiftr01 0 e` に **`lev ≠ 0`** が要った
（`Wset.oper_shiftr1` の前提）。**`Lift1` ではそれが要らない**: `Lift1` は
`srow` も `hasParent` も**無条件で**保つ（`Wset.srow_Lift1` / `hasParent_Lift1`）。
**⟹ マスクつきのほうが素直。** -/

theorem hasParentInBlock_Lift1 {Q : TrioSeq} {e : ℕ} (hQ2 : Q.length - 1 ≠ 0)
    (h : L53.HasParentInBlock Q) : L53.HasParentInBlock (Lift1 Q e) := by
  unfold L53.HasParentInBlock at h ⊢
  rw [Lift1_length, Wset.srow_Lift1 hQ2, hasParent_Lift1]
  exact h

open Classical in
/-- **★★★★★★ `mTower` の展開は最後のブロックだけを展開する。** -/
theorem oper_mTower {Q : TrioSeq} (hQne : Q ≠ []) (hQ2 : Q.length - 1 ≠ 0)
    (hlev : lev Q (Q.length - 1) ≠ 0) (hblk : L53.HasParentInBlock Q)
    (d e n m : ℕ) :
    (mTower Q d e (n + 1))⟦m⟧
      = mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n))⟦m⟧ := by
  have hNlen : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length = Q.length := by
    rw [Lift1_length, shiftr01_length]
  have hNne : Lift1 (shiftr01 (d * n) 0 Q) (e * n) ≠ [] := by
    intro hc
    have hl := congrArg List.length hc
    rw [hNlen] at hl
    exact hQne (List.length_eq_zero_iff.mp hl)
  have hN2 : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length - 1 ≠ 0 := by
    rw [hNlen]; exact hQ2
  have hNblk : L53.HasParentInBlock (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) := by
    refine hasParentInBlock_Lift1 ?_ (hasParentInBlock_shiftr01 hblk)
    rw [shiftr01_length]; exact hQ2
  have hlt : Q.length - 1 < (shiftr01 (d * n) 0 Q).length := by
    have : 0 < Q.length := List.length_pos_iff.mpr hQne
    rw [shiftr01_length]; omega
  have hNz : ¬ (entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 0
        ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length - 1) = 0 ∧
      entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 1
        ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length - 1) = 0 ∧
      entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 2
        ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length - 1) = 0) := by
    rw [hNlen]
    rintro ⟨-, h1, h2⟩
    rw [entry2_Lift1, entry2_shiftr01] at h2
    rw [entry1_Lift1 hlt, entry1_shiftr01] at h1
    unfold lev at hlev
    omega
  rw [mTower_succ, L53.comm_of_hasParentInBlock m hNne hN2 hNz hNblk]

/-! ### 70.1 ⟹ 核 (2) の帰納の 1 段が確定した

    `mTower Q d e (n+1)` の展開 = `mTower Q d e n ++ (最後のブロック)⟦m⟧`

⟹ **`mem_of_oper_mem` で `mTower Q d e (n+1) ∈ W a` を示すには、
右辺が `W a` に入ることだけ言えばよい。** 左半分は帰納法の仮定
（`mTower Q d e n`）、右半分は 1 ブロックの展開である。

⚠ **残るのは連結**（`mTower Q d e n ++ (…)⟦m⟧` が `W a`）。**そこが `WCat` の壁**で、
本線では `graft`（節 3）で回避している。**次の一手はそこ。**

### 70.2 ⟹ §56 との差

    §56 `oper_shTower2` … 行 1 も**一様**シフト。`Wset.oper_shiftr1` の
                          **`lev Q (|Q|-1) ≠ 0`** が要る（`srow` が `0→1` に変わるため）
    §70 `oper_mTower`   … 行 1 は**マスクつき**（`Lift1`）。`srow` は無条件で保たれるので
                          `lev ≠ 0` は **`hNz`（末尾列が全零でない）にしか使わない**

⟹ **マスクつきのほうが仮定が軽い。** §57 で「5 つの塔」を並べたとき
`operTower`（＝ `mTower`）を核に選んだのは、この意味でも正しかった。 -/

/-! ## 71. ★★★★★★ 核 (2) は **帰納なしの 1 文**に落ちる

§70 の `oper_mTower` は `mTower Q d e (n+1)` の**展開すべて**を書き下している。
`Wchar.mem_of_oper_mem` は「展開が全部 `W a` なら本体も `W a`」なので、
**帰納法すら要らない**: 各 `n` について展開を書き換えるだけでよい。 -/

/-- **★★★★★★ 塔の `W` 所属は「1 段の連結」1 文に落ちる**（帰納なし）。 -/
theorem mTower_mem_of_step {a : ℕ} {Q : TrioSeq} {d e : ℕ} (hQne : Q ≠ [])
    (hQ2 : Q.length - 1 ≠ 0) (hlev : lev Q (Q.length - 1) ≠ 0)
    (hblk : L53.HasParentInBlock Q)
    (hstep : ∀ n m : ℕ, 1 ≤ m →
      mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n))⟦m⟧ ∈ W a) :
    ∀ n, mTower Q d e n ∈ W a := by
  intro n
  cases n with
  | zero => simpa [mTower] using W_nil a
  | succ n =>
      refine mem_of_oper_mem (fun m hm => ?_)
      rw [oper_mTower hQne hQ2 hlev hblk d e n m]
      exact hstep n m hm

/-- 尾は「行 0 の一様シフト ∘ 展開 ∘ 行 1 マスクリフト」に書き直せる
（`Wset.oper_shiftr01` は無条件）。 -/
theorem mTower_step_shift (Q : TrioSeq) (d e n m : ℕ) :
    (Lift1 (shiftr01 (d * n) 0 Q) (e * n))⟦m⟧
      = shiftr01 (d * n) 0 ((Lift1 Q (e * n))⟦m⟧) := by
  rw [Lift1_shiftr01, oper_shiftr01]

/-- **★★★★★★ 核 (2) の最終形**: 塔 ＋ 「持ち上げた `Q` の展開を行 0 でずらしたもの」。 -/
def MTowerStep (a : ℕ) (Q : TrioSeq) (d e : ℕ) : Prop :=
  ∀ n m : ℕ, 1 ≤ m →
    mTower Q d e n ++ shiftr01 (d * n) 0 ((Lift1 Q (e * n))⟦m⟧) ∈ W a

theorem mTower_mem_of_mTowerStep {a : ℕ} {Q : TrioSeq} {d e : ℕ} (hQne : Q ≠ [])
    (hQ2 : Q.length - 1 ≠ 0) (hlev : lev Q (Q.length - 1) ≠ 0)
    (hblk : L53.HasParentInBlock Q) (h : MTowerStep a Q d e) :
    ∀ n, mTower Q d e n ∈ W a := by
  refine mTower_mem_of_step hQne hQ2 hlev hblk (fun n m hm => ?_)
  rw [mTower_step_shift]
  exact h n m hm

/-! ### 71.1 ⟹ 残るのは連結ひとつ

    **`mTower Q d e n`** … 塔の**前半**（`n` ブロック）。§69 で `oper` そのものと判明
    **`shiftr01 (d*n) 0 ((Lift1 Q (e*n))⟦m⟧)`** … **1 ブロックの展開**を行 0 でずらしたもの

⟹ **核 (2) は「この 2 つの連結が `W a` に入る」1 文**である。`n` の帰納も
`Wself` の段の帳尻も、もう出てこない。

⚠ **これは `WCat`（連結の閉包）ではない。** 左は塔、右は 1 ブロックの展開で、
**どちらも `Q` から作られる**。本線が `graft`（節 3）で連結を回避しているのと同じく、
ここでも「左が右の**接頭辞**である」ことを使う余地がある:

    `mTower Q d e (n+1) = mTower Q d e n ++ Lift1 (shiftr01 (d*n) 0 Q) (e*n)`（`mTower_succ`）

**⟹ 目標は `mTower Q d e (n+1)` の「最後のブロックだけを展開したもの」**であり、
**`graft` の形（`M.dropLast ++ 置換`）をブロック単位にしたもの**である。
`Aop` の節 3 は 1 列の置換しか許さないので、そのままでは当たらない。**そこが次の壁。**

### 71.2 ⟹ 今日の核の一覧（更新）

    **(1) 悪根 ＝ 根の 1 歩**（§67）… `LiftTower1`（`srow=1`）/ `LiftTowerExp2`（`srow=2`）
        `LiftTieCore` はここに合流した。`liftInner_holds` が `j0 ≥ 1` を全部処理する
    **(2) `MTowerStep`**（上）… 塔 ＋ 1 ブロックの展開の連結。**帰納なし・段なし**
    **(3) `GraftAll` ＝ `CoreCap`**（§25）

**(2) は (1) の `srow = 2` を回すための道具**なので、独立ではない。 -/

/-! ## 72. ⛔ **§71.2 の自己訂正: `LiftTower1` / `LiftTowerExp2` は開いた核ではない**

§71.2 で「今日の核の一覧」に `LiftTower1`（`srow=1`）と `LiftTowerExp2`（`srow=2`）を
**開いた核として**並べたが、**誤り**である。**両方とも `GraftAll` から出る定理**で、
**すでに緑**である:

    **`Wset.liftTower1_of_graftAll`（`Wset.lean:4151`、緑）**
    **`Wset.liftTowerExp2_of_graftAll`（`Wset.lean:4211`、緑）**
    `Lcone.Wstar2s_closed_of_graftAll`（`Lcone.lean:687`、緑）
      ＝ `Wset.Wstar2s_closed liftInner_holds (liftTower1_of_graftAll hga)
                                             (liftTowerExp2_of_graftAll hga)`
    `Lcone.W_le_Wstar2s`（`:694`、緑）… `GraftAll ⟹ ∀ u, W u ⊆ Wstar2s`

> **⟹ 本線は `GraftAll` **1 本**に乗っている。塔の枝はとっくに片づいている。**
> **⟹ 私の §70-71（`oper_mTower` / `MTowerStep`）は「開いた核」ではなく、
>   すでに閉じている枝の別証明である。**

**また grep を怠った。**（§67 の `srow_cons_last`、§69 の `entry_cons_last` に続いて
この節で 3 度目、通算 6 回目。**「核だ」と書く前に `grep _of_graftAll` を打つべきだった。**）

### 72.1 ⟹ 私の §67-71 のうち何が残るか

    **§67（(WL) の 1 歩の残差 ＝ 悪根 ＝ 根）** … 残る。`liftInner_holds` の**使い道**の話で、
        `LiftTieCore`（L53 の核、経路 C）がどこに落ちるかを決める
    **§68（`M⟦n⟧ = mTower M.dropLast d0 d1 n`）** … 残る。**新しい恒等式**
    **§69（`operTower = mTower`）** … 残る。R2 の H73 を定理にした
    §70-71（`oper_mTower` / `MTowerStep`）… **本線では不要**。`GraftAll` 経由で済む

### 72.2 ⚠ ただし `LiftTieCore` は `GraftAll` の下流とは**まだ言えない**

`GraftAll ⟹ W u ⊆ Wstar2s` は使えるが、`LiftTieCore` の場面では

    仮定は **`(0,v,z) :: R ∈ W (2v+z)`**（`X` についての `W` 所属）
    要るのは **`R ∈ Wstar2`**（`R` についての装備）

で、**`X ∈ W u` から `R ∈ W u'` は出ない**（`argOK X` は根の行 0 が `0` なので偽 ⟹
`W_le_Wstar2s` を `X` に当てても空虚）。**`R` 自身の導出が要る。**

⟹ **経路 C（`LiftTieCore` / `TowerOK`）は本線とは別の入口**であり、
**本線が `GraftAll` 1 本で閉じている以上、経路 C を追う理由は薄い。**

> **⟹ 唯一の開いた核は `GraftAll`（＝ 私の §25 の `CoreCap`）。そこに集中すべき。** -/

/-! ## 73. ★★★★★★ **C-2 の前半: `LiftTower1` は `(TOW)` から出る**（`GraftAll` 不要）

`STATUS.md` の **C-2**（`LiftTower1` ＋ `LiftTowerExp2` を無条件に）に対する第一歩。
`srow = 1` では `oper` の `d1 = if 1 < i1 then … else 0` が **`0`** になるので、
展開は**純粋な行 0 ずらしコピー塔**である —— これは既に
**`Wtower2.oper_of_srow1_par0`（`:1732`、緑）** が与えている
（**私の §68 `oper_eq_mTower` の `srow = 1` 特殊化にあたる。書く前に grep した**）。

⟹ `LiftTower1` は

    `M := Lift1 ((0,v,z) :: R) t`  の展開が `shTower (M.dropLast) d0 n`
    `M.dropLast = Lift1 ((0,v,z) :: R.dropLast) t` は**接頭辞装備**から `W a`
    その根は `argOK R` より**狭義に最浅**

の 3 点で、**`Wtower2.ShiftTowerClosedS`（`(TOW)`）にそのまま落ちる。** -/

open Classical in
/-- **★★★★★★ `LiftTower1 ⟸ ShiftTowerClosedS`**（`GraftAll` を使わない）。 -/
theorem liftTower1_of_shiftTowerClosedS (htow : ShiftTowerClosedS) : LiftTower1 := by
  rintro v z u0 a t R hR hRne hz1 hva - hpre ⟨m, hd⟩ hi1 hpM
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hne0 : R.length ≠ 0 := by omega
  have hMlen : (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length = R.length + 1 := by
    rw [Lift1_length, List.length_cons]
  have hMl1 : (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length - 1 = R.length := by
    rw [hMlen]; omega
  have hsrL : srow (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t)
      ((Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length - 1) = 1 := by
    rw [hMl1, Wset.srow_Lift1 hne0, srow_cons_last hRne, hi1]
  have hpL : hasParent (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t)
      (srow (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t)
        ((Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length - 1))
      ((Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length - 1) := by
    rw [hMl1, Wset.srow_Lift1 hne0, srow_cons_last hRne, hasParent_Lift1]
    exact hpM
  have hbpL : parent (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t)
      (srow (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t)
        ((Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length - 1))
      ((Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length - 1) = 0 := by
    rw [hMl1, Wset.srow_Lift1 hne0, srow_cons_last hRne, parent_Lift1]
    exact parent_cons_eq_zero hRne hd hpM
  have hQmem : Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t ∈ W a := by
    have hk : R.length - 1 < R.length := by omega
    have hres := hpre (R.length - 1) hk (argOK_take' hR (R.length - 1)) v z a t hz1 hva
    rwa [← List.dropLast_eq_take] at hres
  have hQshallow : ∀ j, 1 ≤ j →
      j < (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t).length →
      entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t) 0 0
        < entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t) 0 j := by
    intro j hj1 hjl
    rw [Lift1_length, List.length_cons, List.length_dropLast] at hjl
    rw [entry0_Lift1, entry0_Lift1,
      show entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 0 0 = 0 from by simp [entry]]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hj'lt : j' < R.length - 1 := by omega
    have hj'R : j' < R.length := by omega
    rw [entry_cons_succ, List.dropLast_eq_take, entry_take hj'lt]
    exact hR _ (entry_pair_mem (B := R) hj'R)
  refine mem_of_oper_mem (fun n _ => ?_)
  rw [oper_of_srow1_par0 (by rw [hMlen]; omega) hpL hbpL hsrL n, Lift1_dropLast,
    dropLast_cons hRne]
  exact htow a _ n _ hQmem hQshallow

/-! ### 73.1 ⟹ C-2 の残りは `srow = 2` 側だけ

    **`LiftTower1`** … **`ShiftTowerClosedS`（`(TOW)`）から出る**（上、緑）
    **`LiftTowerExp2`** … `srow = 2` なので `d1 > 0`（`L53.tower2_vw`）⟹ 塔は
        **`mTower`（マスクつき）**。`(TOW)` ではなく **§55 `OperTowerSelf` / §71
        `MTowerStep`** が要る

⟹ **C-2 ＝ 「`(TOW)`」＋「マスクつき塔の閉包」の 2 本。** どちらも
**リフトを含まない／段を上げない**塔の閉包で、`GraftAll` より素直な形である。

⚠ `(TOW)`（`Wtower2.ShiftTowerClosed`、`:1763`）は既知の核で、
**実測は `tools/probe_core1.py` (C) の 6244 例・違反 0、しかも `minstage` は等号**
（docstring より）。**塔は段を一切上げない。**

### 73.2 ⚠ 私の §68 との関係（再発明ではない）

`oper_of_srow1_par0`（`Wtower2:1732`）は **`srow = 1` 専用**、私の
`oper_eq_mTower`（§68）は **`srow` の仮定が無い**（`d0`/`d1` の `if` で 0/1/2 を一様に扱う）。
⟹ **§68 は `oper_of_srow1_par0` の一般化**であり、`srow = 2` 側でも使える。
`srow = 1` 側は既存のものをそのまま使うのが正しい（上でそうした）。 -/

/-! ## 74. ★★★★★★ **C-2 の後半: `LiftTowerExp2` はマスクつき塔の閉包から出る**

§73 とまったく同じ骨で、`oper_of_srow1_par0`（`srow = 1` 専用）を
**私の §68 `oper_eq_mTower`（`srow` の仮定なし）**に差し替えるだけである。 -/

/-- **(TOW2)**: マスクつき（行 1 も段ごとに上がる）塔の閉包。
`Wtower2.ShiftTowerClosedS`（`(TOW)`）の `Lift1` 版で、**`e = 0` なら `(TOW)` そのもの**
（`Lift1 X 0 = X`）。根の `lev` は塔で変わらないので、段は `u` のままでよい。 -/
def MTowerClosedS : Prop :=
  ∀ (u d e n : ℕ) (Q : TrioSeq), Q ∈ W u →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
    mTower Q d e n ∈ W u

/-- `(TOW2)` は `(TOW)` を含む（`e = 0` で `mTower = shTower`）。 -/
theorem shiftTowerClosedS_of_mTowerClosedS (h : MTowerClosedS) : ShiftTowerClosedS := by
  intro u e n Q hQ hs
  have hres := h u e 0 n Q hQ hs
  have heq : mTower Q e 0 n = shTower Q e n := by
    unfold mTower shTower
    refine List.flatMap_congr ?_
    intro k _
    rw [Nat.zero_mul, Lift1_zero, Nat.mul_comm]
  rwa [heq] at hres

open Classical in
/-- **★★★★★★ `LiftTowerExp2 ⟸ MTowerClosedS`**（`GraftAll` を使わない）。 -/
theorem liftTowerExp2_of_mTowerClosedS (htow : MTowerClosedS) : LiftTowerExp2 := by
  rintro v z a t R hR hRne hz1 hva - hpre ⟨m, hd⟩ hi2 hpM
  have hRlen : 0 < R.length := List.length_pos_iff.mpr hRne
  have hne0 : R.length ≠ 0 := by omega
  have hMlen : (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length = R.length + 1 := by
    rw [Lift1_length, List.length_cons]
  have hMl1 : (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length - 1 = R.length := by
    rw [hMlen]; omega
  have hpL : hasParent (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t)
      (srow (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t)
        ((Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length - 1))
      ((Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length - 1) := by
    rw [hMl1, Wset.srow_Lift1 hne0, srow_cons_last hRne, hasParent_Lift1]
    exact hpM
  have hbpL : parent (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t)
      (srow (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t)
        ((Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length - 1))
      ((Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length - 1) = 0 := by
    rw [hMl1, Wset.srow_Lift1 hne0, srow_cons_last hRne, parent_Lift1]
    exact parent_cons_eq_zero hRne hd hpM
  have hzz : ¬ (entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t) 0
        ((Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length - 1) = 0 ∧
      entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t) 1
        ((Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length - 1) = 0 ∧
      entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t) 2
        ((Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R) t).length - 1) = 0) := by
    rintro ⟨-, -, h⟩
    rw [hMl1, entry2_Lift1, entry_cons_last hRne] at h
    have := L53.srow_two_row2_pos hi2
    omega
  have hQmem : Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t ∈ W a := by
    have hk : R.length - 1 < R.length := by omega
    have hres := hpre (R.length - 1) hk (argOK_take' hR (R.length - 1)) v z a t hz1 hva
    rwa [← List.dropLast_eq_take] at hres
  have hQshallow : ∀ j, 1 ≤ j →
      j < (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t).length →
      entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t) 0 0
        < entry (Lift1 (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) t) 0 j := by
    intro j hj1 hjl
    rw [Lift1_length, List.length_cons, List.length_dropLast] at hjl
    rw [entry0_Lift1, entry0_Lift1,
      show entry (((0, v, z) : ℕ × ℕ × ℕ) :: R.dropLast) 0 0 = 0 from by simp [entry]]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hj'lt : j' < R.length - 1 := by omega
    have hj'R : j' < R.length := by omega
    rw [entry_cons_succ, List.dropLast_eq_take, entry_take hj'lt]
    exact hR _ (entry_pair_mem (B := R) hj'R)
  refine mem_of_oper_mem (fun n _ => ?_)
  rw [oper_eq_mTower n (by rw [hMl1]; omega) hzz hpL hbpL, Lift1_dropLast,
    dropLast_cons hRne]
  exact htow a _ _ n _ hQmem hQshallow

/-! ## 75. ★★★★★★ **C-2 は塔の閉包 1 本に落ちた**

§73 ＋ §74 ＋ 既存の `Lcone.liftInner_holds`（無条件・緑）を `Wset.Wstar2s_closed` に
入れると、**`GraftAll` が消える**。 -/

/-- **★★★★★★ `MTowerClosedS` だけで `Wstar2s` が閉じる**（`GraftAll` 不要）。 -/
theorem wstar2s_closed_of_mTowerClosedS (htow : MTowerClosedS) :
    ∀ (u0 : ℕ) (R : TrioSeq), Aop W u0 Wstar2s R → R ∈ Wstar2s :=
  Wstar2s_closed liftInner_holds
    (liftTower1_of_shiftTowerClosedS (shiftTowerClosedS_of_mTowerClosedS htow))
    (liftTowerExp2_of_mTowerClosedS htow)

/-- **★★★★★★ ⟹ `W` のすべての元が装備つき package になる。** -/
theorem w_le_wstar2s_of_mTowerClosedS (htow : MTowerClosedS) (u : ℕ) :
    W u ⊆ Wstar2s :=
  A2' (fun R hR => wstar2s_closed_of_mTowerClosedS htow u R hR)

/-! ### 75.1 ⟹ 何が起きたか

    **`GraftAll`（半年の残核、7 量化 / 5 前提、`y ∈ W u` を全部相手にする）**
      ↓ 置き換え
    **`MTowerClosedS`（5 量化 / 2 前提、`Q ∈ W u` と「根が狭義最浅」だけ）**

    `MTowerClosedS a d e n Q : Q ∈ W u → (根が狭義最浅) → mTower Q d e n ∈ W u`

**⟹ `graft`（1 列を `W` の元で置換）も `y ∈ W u` の全称も出てこない。
出てくるのは「`Q` のコピーを行 0 で沈め、行 1 を錐の上だけ持ち上げて `n` 個並べる」だけ。**

⚠ **`(TOW)` は `MTowerClosedS` の `e = 0` の場合**（`shiftTowerClosedS_of_mTowerClosedS`、緑）
なので、**C-2 の「両方」は 1 本にまとまる。** `STATUS.md` の
「`LiftTowerExp2` だけ証明しても 0 点」は、**`MTowerClosedS` 1 本なら回避できる**。

### 75.2 ⚠ 正直な但し書き

**`MTowerClosedS` はまだ未証明**である。私はそれを `GraftAll` の**代わり**に立てただけで、
偽である可能性も残る。ただし:

    `(TOW)`（`e = 0` の場合）… `tools/probe_core1.py` (C) 6244 例・違反 0、
      しかも **`minstage` は等号**（塔は段を一切上げない）—— `Wtower2:1763` docstring
    `e > 0` の場合 … R2 が `mTower` を 276,876 塔・1,245,942 ブロックで扱っている

**⟹ 実測の裏づけは `GraftAll` より厚い。** そして形が小さい（2 前提）。

### 75.3 ⟹ 次の一手

`MTowerClosedS` は §70-71 の道具がそのまま当たる:

    `oper_mTower`（§70、緑）… `(mTower Q d e (n+1))⟦m⟧ = mTower Q d e n ++ (最後のブロック)⟦m⟧`
    `mTower_mem_of_step`（§71、緑）… ⟹ **帰納なしで** `MTowerStep` 1 文に落ちる

⚠ **ただし直結ではない。** `mTower_mem_of_step` は `Q ≠ []` / `|Q|-1 ≠ 0` /
`lev Q (|Q|-1) ≠ 0` / `HasParentInBlock Q` の **4 つの場面仮定**を要求するが、
`MTowerClosedS` の仮定は `Q ∈ W u` と「根が狭義最浅」の **2 つだけ**である。
⟹ **`Q` の末尾列が孤児（`¬ HasParentInBlock`）の場合を別に片づける必要がある**
（そこは `oper` が `Pred` になるので易しいはず。**未確認**）。

**⟹ §70-71 は「本線では不要」ではなくなった。**
（§72 の「§70-71 は不要」は **C-1 を選ぶ場合の話**で、**C-2 を選ぶなら本線の道具**である。） -/

/-! ## 76. ★★★★★ `MTowerClosedS` の**無料の枝**: 行 2 ≡ 0

§32 の `liftStage_of_zeroRow2` と同じ理屈。`mTower` は `Lift1` と `shiftr01 · 0` しか
使わないので**行 2 を動かさない**。⟹ `Q` の行 2 が恒等的に `0` なら `mTower` もそうで、
`Wtower2.zeroRow2_mem_Wself` がそのまま `Wself` に入れる。根の `lev` は `Q` のものと同じ。 -/

@[simp] theorem mTower_nil (d e n : ℕ) : mTower ([] : TrioSeq) d e n = [] := by
  unfold mTower
  simp

theorem zeroRow2_shiftr01 {Q : TrioSeq} {d0 d1 : ℕ} (h : ∀ p ∈ Q, p.2.2 = 0) :
    ∀ p ∈ shiftr01 d0 d1 Q, p.2.2 = 0 := by
  intro p hp
  unfold shiftr01 at hp
  rw [List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact h q hq

theorem zeroRow2_mTower {Q : TrioSeq} (h : ∀ p ∈ Q, p.2.2 = 0) (d e n : ℕ) :
    ∀ p ∈ mTower Q d e n, p.2.2 = 0 := by
  intro p hp
  unfold mTower at hp
  rw [List.mem_flatMap] at hp
  obtain ⟨k, -, hk⟩ := hp
  exact zeroRow2_Lift1 (zeroRow2_shiftr01 h) p hk

theorem lev_mTower_root {Q : TrioSeq} (hQne : Q ≠ []) (d e n : ℕ) :
    lev (mTower Q d e (n + 1)) 0 = lev Q 0 := by
  have hQlen : 0 < Q.length := List.length_pos_iff.mpr hQne
  rw [mTower_cons]
  unfold lev
  rw [entry_append_left _ _ hQlen, entry_append_left _ _ hQlen]

/-- **★★★★★ `MTowerClosedS` の行 2 ≡ 0 の枝は仮定ゼロ。** -/
theorem mTower_mem_of_zeroRow2 {u : ℕ} {Q : TrioSeq} (hz : ∀ p ∈ Q, p.2.2 = 0)
    (hQ : Q ∈ W u) (d e n : ℕ) : mTower Q d e n ∈ W u := by
  cases n with
  | zero => simpa using W_nil u
  | succ n =>
      by_cases hQne : Q = []
      · subst hQne; simpa using W_nil u
      · rw [mem_Wself_iff]
        refine ⟨zeroRow2_mem_Wself (zeroRow2_mTower hz d e (n + 1)), ?_⟩
        rw [lev_mTower_root hQne]
        exact lev_root_le_of_mem_W hQ hQne

/-- ⟹ **`MTowerClosedS` は「`Q` の行 2 に非零がある」場合だけ**（§32.1 と同じ形）。 -/
def MTowerClosedRow2 : Prop :=
  ∀ (u d e n : ℕ) (Q : TrioSeq), Q ∈ W u →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
    (∃ p ∈ Q, 0 < p.2.2) →
    mTower Q d e n ∈ W u

open Classical in
theorem mTowerClosedS_of_row2 (h : MTowerClosedRow2) : MTowerClosedS := by
  intro u d e n Q hQ hs
  by_cases hz2 : ∃ p ∈ Q, 0 < p.2.2
  · exact h u d e n Q hQ hs hz2
  · refine mTower_mem_of_zeroRow2 ?_ hQ d e n
    intro p hp
    by_contra hc
    exact hz2 ⟨p, hp, by omega⟩

/-! ### 76.1 ⟹ `MTowerClosedS` の残差

    `|Q| ≤ 1` かつ `lev Q 0 = 0` … `Q = [(c,0,0)]` ⟹ **行 2 ≡ 0 ⟹ 無料**
    行 2 ≡ 0                       … **無料**（上）
    **行 2 に非零がある**          … **残差**（`MTowerClosedRow2`）

⟹ **`GraftAll` の置き換えとして残るのは `MTowerClosedRow2` 1 本**:

    `Q ∈ W u` ＋ 根が狭義最浅 ＋ **`Q` の行 2 に非零がある**
      ⟹ `mTower Q d e n ∈ W u`

**6 量化 / 3 前提。`graft` も `y ∈ W u` の全称も無い。** -/

/-! ## 77. `MTowerClosedS` の自明な枝と、残差の形

`n ≤ 1` は無料（`mTower_one`（§55、既存）が `mTower Q d e 1 = Q` を与える。
**ここでも書きかけて既存を踏んだ —— grep 7 回目**）。⟹ 残差は `n ≥ 2`。 -/

theorem mTower_mem_of_le_one {u : ℕ} {Q : TrioSeq} (hQ : Q ∈ W u) {d e n : ℕ}
    (hn : n ≤ 1) : mTower Q d e n ∈ W u := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simpa [mTower] using W_nil u
  · have h1 : n = 1 := by omega
    subst h1
    simpa [mTower_one] using hQ

/-! ### 77.1 ⟹ 残差の表

    `n ≤ 1`                    … **無料**（上）
    `Q` の行 2 ≡ 0             … **無料**（§76、`|Q| ≤ 1` の枝もここ）
    `Q` の末尾列が段内に親を持つ … §70-71 で **1 文**（`MTowerStep`）に落ちる
    **`Q` の末尾列が段内で孤児** … **残差**（塔の悪根がブロックをまたぐ）

⚠ 最後の枝が本当の残差である。`L53.comm_of_hasParentInBlock` は
「最後のブロックの中に親がある」ときだけ展開を塔の前半から切り離すので、
**孤児のときは悪根が前のブロックに逃げうる**。

### 77.2 ⚠ その先は `WCat` の匂いがする（team-lead の判断待ち）

素直な攻め方は「塔 `A` に、ブロックの**派生の途中** `B` を継ぐ」形で `B ∈ W u` に
`A2'` を回すことである:

    `CatBlock u c A := ∀ B ∈ W u, A ++ shiftr01 c 0 B ∈ W u`

    節 1（`B` 短い）… `A ++ []` は `A`、`A ++ [(b+c,0,0)]` は **snoc**
      （`Wtower2.snoc_orphan`（`:3053`）／`snoc_flat_root`（`:2208`）で
        **親なし**と**親＝根**は無料。**親が内部**なら `PrefixCopies`）
    節 2 で **`HasParentInBlock B`** … `comm_of_hasParentInBlock` で
      `(A ++ shift B)⟦m⟧ = A ++ shift (B⟦m⟧)` ⟹ 帰納法の仮定
    節 3 … `Wchar.aop_clause3_to_clause2` で節 2 に吸収される（`|B| ≥ 2`）
    節 2 で **`¬ HasParentInBlock B`** … **残差**（同上）

⚠ **`CatBlock` は `WCat` の制限版**である。team-lead の規律「`WCat` を避ける」に
触れるので、**進める前に判断を仰ぐ。** -/

/-! ## 78. ★★★★★ 塔に 1 ブロックを継ぐ: **残差は「悪根が前半に逃げる」1 枝**

§77.2 の骨組みを実際に組んだ。**`WCat` の制限版**（`A` は塔、`B` は同じ素材の派生）だが、
**4 枝のうち 3 枝が既存の緑で落ちる**ことが確認できた。 -/

/-- 段内に親があるなら末尾列は全零でない（全零なら `srow = 0` で行 0 の親が要り、
`entry 0 j0 < 0` は不可能）。 -/
theorem hz_of_hasParentInBlock {N : TrioSeq} (h : L53.HasParentInBlock N) :
    ¬ (entry N 0 (N.length - 1) = 0 ∧ entry N 1 (N.length - 1) = 0 ∧
      entry N 2 (N.length - 1) = 0) := by
  rintro ⟨h0, h1, h2⟩
  unfold L53.HasParentInBlock at h
  have hsr : srow N (N.length - 1) = 0 := by
    unfold srow
    rw [if_neg (by omega), if_neg (by omega)]
  rw [hsr] at h
  obtain ⟨j0, hj0, -⟩ := h
  unfold nextR at hj0
  rw [if_pos rfl] at hj0
  have := hj0.2.2.2.1
  omega

/-- 1 列の塊は段内に親を持たない。 -/
theorem not_hasParentInBlock_of_short {N : TrioSeq} (h1 : N.length - 1 = 0) :
    ¬ L53.HasParentInBlock N := by
  unfold L53.HasParentInBlock
  rintro ⟨j0, hj0, -⟩
  have := nextR_index_lt hj0
  omega

/-- **★★★★★ 段内に親があるブロックは、前半 `A` を素通しする。** -/
theorem catBlock_step {u c : ℕ} {A B : TrioSeq} (hB2 : 2 ≤ B.length)
    (hblk : L53.HasParentInBlock (shiftr01 c 0 B))
    (hop : ∀ m, 1 ≤ m → A ++ shiftr01 c 0 (B⟦m⟧) ∈ W u) :
    A ++ shiftr01 c 0 B ∈ W u := by
  refine mem_of_oper_mem (fun m hm => ?_)
  have hNne : shiftr01 c 0 B ≠ [] := by
    intro hc
    have hl : (shiftr01 c 0 B).length = 0 := by rw [hc]; rfl
    rw [shiftr01_length] at hl
    omega
  have hN2 : (shiftr01 c 0 B).length - 1 ≠ 0 := by
    rw [shiftr01_length]; omega
  rw [L53.comm_of_hasParentInBlock m hNne hN2 (hz_of_hasParentInBlock hblk) hblk,
    oper_shiftr01]
  exact hop m hm

open Classical in
/-- **★★★★★★ 塔に 1 ブロックを継ぐ問題は「悪根が前半に逃げる」1 枝に落ちる。**

`hesc` は「継いだブロックの末尾列が**そのブロックの中では孤児**」の場合だけを引き受ける。
それ以外（節 1 の空・節 2 の段内親あり・節 3）は**全部この証明の中で落ちる**。 -/
theorem catBlock_of_escape {u c : ℕ} {A : TrioSeq} (hA : A ∈ W u)
    (hesc : ∀ B : TrioSeq, 1 ≤ B.length →
      ¬ L53.HasParentInBlock (shiftr01 c 0 B) →
      A ++ shiftr01 c 0 B ∈ W u) :
    ∀ B : TrioSeq, B ∈ W u → A ++ shiftr01 c 0 B ∈ W u := by
  have hsub : W u ⊆ {B : TrioSeq | A ++ shiftr01 c 0 B ∈ W u} := by
    refine A2' ?_
    rintro B (⟨hl, -⟩ | hop | ⟨m', hm', hd, hgr⟩)
    · rcases Nat.eq_zero_or_pos B.length with h0 | hpos
      · have hnil : B = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        show A ++ shiftr01 c 0 ([] : TrioSeq) ∈ W u
        simpa using hA
      · refine hesc B (by omega) ?_
        refine not_hasParentInBlock_of_short ?_
        rw [shiftr01_length]; omega
    · show A ++ shiftr01 c 0 B ∈ W u
      rcases Nat.lt_or_ge B.length 2 with hsm | hbig
      · have hres := hop 1 le_rfl
        rwa [oper_eq_self_of_short 1 (by omega)] at hres
      · by_cases hblk : L53.HasParentInBlock (shiftr01 c 0 B)
        · exact catBlock_step hbig hblk (fun m hm => hop m hm)
        · exact hesc B (by omega) hblk
    · show A ++ shiftr01 c 0 B ∈ W u
      rcases Nat.lt_or_ge B.length 2 with hsm | hbig
      · have hBne : B ≠ [] := by
          intro hc
          rw [hc] at hd
          exact not_domT_nil m' hd
        have h1 : 0 < B.length := List.length_pos_iff.mpr hBne
        refine hesc B (by omega) ?_
        refine not_hasParentInBlock_of_short ?_
        rw [shiftr01_length]; omega
      · have hop := aop_clause3_to_clause2 hbig hd hgr
        by_cases hblk : L53.HasParentInBlock (shiftr01 c 0 B)
        · exact catBlock_step hbig hblk (fun m hm => hop m hm)
        · exact hesc B (by omega) hblk
  exact fun B hB => hsub hB

/-! ### 78.1 ⟹ 落ちた枝と残った枝

    節 1 `B = []`         … `A ++ [] = A ∈ W u`                        **無料**
    節 1 `|B| = 1`        … 1 列は段内に親を持たない ⟹ `hesc`          （残差に合流）
    節 2 `|B| ≤ 1`        … `oper_eq_self_of_short` で `hop 1`          **無料**
    節 2 段内に親あり     … **`L53.comm_of_hasParentInBlock` ＋ `oper_shiftr01`** **無料**
    節 2 段内で孤児       … `hesc`                                      **残差**
    節 3 `|B| ≤ 1`        … 同上                                        （残差に合流）
    節 3 `|B| ≥ 2`        … **`Wchar.aop_clause3_to_clause2`** で節 2 に吸収 **無料**

⟹ **残差は `hesc` 1 本**:

    `A ∈ W u` ＋ **継ぐブロックの末尾列がそのブロックの中で孤児**
      ⟹ `A ++ shiftr01 c 0 B ∈ W u`

**これは §67 の「悪根 ＝ 根」と同じ現象**（悪根が自分のブロックを出て前半に逃げる）である。
⟹ **`MTowerClosedRow2` と `hesc` は同じ 1 枝を見ている。**

### 78.2 ⚠ `hesc` は `WSnoc` を含む

`|B| = 1` のとき `A ++ shiftr01 c 0 [p] = A ++ [p']` は**任意の列の snoc** なので、
`hesc` は **`WSnoc` を含んでしまう**。⟹ **このままでは核として弱くない。**

    `Wtower2.snoc_orphan`（`:3053`）  … `A ++ [p']` で `p'` が**孤児のまま**なら無料
    `Wtower2.snoc_flat_root`（`:2208`）… `srow = 0` かつ**親が根**なら無料
    残るのは **`p'` が `A` の中に親を見つける**場合 ＝ 上と同じ現象

⟹ **`hesc` をこのまま核にするのは筋が悪い。** §77.2 で挙げた懸念どおり
**`WCat` / `WSnoc` に触れる。** ⟹ **`MTowerClosedRow2` 側から攻めるべき**で、
そちらは `A` が**塔**であることを使える（`hesc` は `A` が何でもよい形になっている）。

**⟹ この節は「素直な分解では `WSnoc` に落ちる」ことの記録である。次は使わない。** -/

/-! ## 79. ★★★★★ **孤児の枝はほとんど起きない**（根が狭義最浅なら）

§77-78 の残差は「継ぐブロックの末尾列が**そのブロックの中で孤児**」だった。
ところが **`MTowerClosedS` は「根が狭義に最浅」を仮定している**ので、
その枝はかなり狭い。道具は既存（`Wset.hasParent_zero_iff` `:1784` /
`hasParent_one_of` `:1823` / `hasParent_two_of` `:1858` / `Lcone.rtg0_zero` `:27`）。 -/

theorem le0_zero_of_shallow {Q : TrioSeq}
    (hs : ∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j)
    {b : ℕ} (hb : b < Q.length) : le0 Q 0 b :=
  ⟨by omega, hb, rtg0_zero (fun l hl0 hl1 => hs l hl0 hl1) hb⟩

/-- **`srow = 0` の末尾列は必ず段内に親を持つ**（根が狭義に最浅なので）。 -/
theorem hasParentInBlock_of_srow_zero {Q : TrioSeq} (h2 : 2 ≤ Q.length)
    (hs : ∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j)
    (hsr : srow Q (Q.length - 1) = 0) : L53.HasParentInBlock Q := by
  unfold L53.HasParentInBlock
  rw [hsr, hasParent_zero_iff (by omega)]
  exact ⟨0, by omega, hs (Q.length - 1) (by omega) (by omega)⟩

/-- **`srow = 1`**: 根の行 1 が末尾列より狭義に小さければ段内に親を持つ。 -/
theorem hasParentInBlock_of_srow_one {Q : TrioSeq} (h2 : 2 ≤ Q.length)
    (hs : ∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j)
    (hsr : srow Q (Q.length - 1) = 1)
    (hlt : entry Q 1 0 < entry Q 1 (Q.length - 1)) : L53.HasParentInBlock Q := by
  unfold L53.HasParentInBlock
  rw [hsr]
  exact hasParent_one_of (by omega) (by omega)
    (le0_zero_of_shallow hs (by omega)) hlt

/-- **`srow = 2`**: 末尾列が根の行 1 錐に入っていて、根の行 2 が狭義に小さければ
段内に親を持つ。 -/
theorem hasParentInBlock_of_srow_two {Q : TrioSeq} (h2 : 2 ≤ Q.length)
    (hsr : srow Q (Q.length - 1) = 2)
    (hcone : le1 Q 0 (Q.length - 1))
    (hlt : entry Q 2 0 < entry Q 2 (Q.length - 1)) : L53.HasParentInBlock Q := by
  unfold L53.HasParentInBlock
  rw [hsr]
  exact hasParent_two_of (by omega) (by omega) hcone hlt

/-! ### 79.1 ⟹ 孤児の枝が残る条件（`|Q| ≥ 2`・根が狭義最浅）

    `srow = 0` … **起きない**（`hasParentInBlock_of_srow_zero`）
    `srow = 1` … **`entry Q 1 (|Q|-1) ≤ entry Q 1 0`** のときだけ
    `srow = 2` … **`¬ le1 Q 0 (|Q|-1)`（末尾列が根の錐の外）** または
                 **`entry Q 2 (|Q|-1) ≤ entry Q 2 0`** のときだけ

⟹ **孤児は「末尾列が根より上に行けない」場合に限る。** `srow = 2` の側は
**「末尾列がブロッカーの向こう側にある」**という §59.1 と同じ現象である。

### 79.2 ⟹ `MTowerClosedRow2` の残差の最終形

    `n ≥ 2` ／ `Q` の行 2 に非零 ／ **`|Q| ≥ 2` かつ末尾列が段内で孤児**
      ＝ `srow Q (|Q|-1) = 1` かつ `entry Q 1 (|Q|-1) ≤ entry Q 1 0`、または
        `srow Q (|Q|-1) = 2` かつ（錐の外 または 行 2 が根以下）

⚠ **`srow = 2` かつ `entry Q 2 (|Q|-1) ≤ entry Q 2 0` は `z ≤ 1` の断片では
`entry Q 2 0 = 1` を強いる**（`srow = 2` は `entry Q 2 (|Q|-1) ≥ 1`）。
⟹ **`z = 1` に限る。** `z = 0` の塔では **錐の外**の場合しか残らない。

**⟹ 次に測るなら「塔のブロックの末尾列が段内で孤児になる割合」**（R2 向け）。
私の予想は**低い**（`srow = 0` は 0%、`srow = 1` は根の行 1 が末尾以上のときだけ）。 -/

/-! ## 80. ★★★★★★ `MTowerClosedS` の**残差 3 本**（無料枝を全部落とした形）

§76（行 2 ≡ 0）・§77（`n ≤ 1`）・§79（`srow = 0` は孤児にならない）を踏まえて、
`MTowerClosedS` を**証明の骨まで**分解する。まず §70 の `oper_mTower` の仮定
`lev Q (|Q|-1) ≠ 0` を「**根が狭義に最浅**」に置き換える（`MTowerClosedS` の仮定に揃う）。 -/

open Classical in
/-- **§70 の改良版**: `lev ≠ 0` の代わりに「根が狭義に最浅」を使う。
（末尾列の**行 0** が根より大きいので、末尾列は全零になりようがない。） -/
theorem oper_mTower' {Q : TrioSeq} (h2 : 2 ≤ Q.length)
    (hs : ∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j)
    (hblk : L53.HasParentInBlock Q) (d e n m : ℕ) :
    (mTower Q d e (n + 1))⟦m⟧
      = mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n))⟦m⟧ := by
  have hQ2 : Q.length - 1 ≠ 0 := by omega
  have hNlen : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length = Q.length := by
    rw [Lift1_length, shiftr01_length]
  have hNne : Lift1 (shiftr01 (d * n) 0 Q) (e * n) ≠ [] := by
    intro hc
    have hl : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length = 0 := by rw [hc]; rfl
    rw [hNlen] at hl; omega
  have hN2 : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length - 1 ≠ 0 := by
    rw [hNlen]; exact hQ2
  have hNblk : L53.HasParentInBlock (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) := by
    refine hasParentInBlock_Lift1 ?_ (hasParentInBlock_shiftr01 hblk)
    rw [shiftr01_length]; exact hQ2
  have hlt : Q.length - 1 < Q.length := by omega
  have hNz : ¬ (entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 0
        ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length - 1) = 0 ∧
      entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 1
        ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length - 1) = 0 ∧
      entry (Lift1 (shiftr01 (d * n) 0 Q) (e * n)) 2
        ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length - 1) = 0) := by
    rw [hNlen]
    rintro ⟨h0, -, -⟩
    rw [entry0_Lift1, entry0_shiftr01 hlt] at h0
    have := hs (Q.length - 1) (by omega) hlt
    omega
  rw [mTower_succ, L53.comm_of_hasParentInBlock m hNne hN2 hNz hNblk]

theorem mTower_mem_of_step' {a : ℕ} {Q : TrioSeq} {d e : ℕ} (h2 : 2 ≤ Q.length)
    (hs : ∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j)
    (hblk : L53.HasParentInBlock Q) (h : MTowerStep a Q d e) :
    ∀ n, mTower Q d e n ∈ W a := by
  intro n
  cases n with
  | zero => simpa using W_nil a
  | succ n =>
      refine mem_of_oper_mem (fun m hm => ?_)
      rw [oper_mTower' h2 hs hblk d e n m, mTower_step_shift]
      exact h n m hm

/-- **残差 A**: 末尾列が段内に親を持つ場合の「塔 ＋ 1 ブロックの展開」。 -/
def MTowerStepAll : Prop :=
  ∀ (u d e : ℕ) (Q : TrioSeq), Q ∈ W u → 2 ≤ Q.length →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
    L53.HasParentInBlock Q → MTowerStep u Q d e

/-- **残差 B**: 末尾列が段内で**孤児**の場合（§79 で `srow ∈ {1,2}` に限る）。 -/
def MTowerOrphan : Prop :=
  ∀ (u d e n : ℕ) (Q : TrioSeq), Q ∈ W u → 2 ≤ Q.length →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
    ¬ L53.HasParentInBlock Q → mTower Q d e n ∈ W u

/-- **残差 C**: ブロックが 1 列（塔は等差の 1 列列になる）。 -/
def MTowerSingle : Prop :=
  ∀ (u d e n : ℕ) (Q : TrioSeq), Q ∈ W u → Q.length = 1 →
    mTower Q d e n ∈ W u

/-- **★★★★★★ `MTowerClosedS` は残差 3 本から出る。** -/
theorem mTowerClosedS_of_residues (hA : MTowerStepAll) (hB : MTowerOrphan)
    (hC : MTowerSingle) : MTowerClosedS := by
  intro u d e n Q hQ hs
  rcases Nat.lt_or_ge Q.length 2 with hsm | hbig
  · rcases Nat.eq_zero_or_pos Q.length with h0 | hpos
    · have hnil : Q = [] := List.length_eq_zero_iff.mp h0
      subst hnil
      simpa using W_nil u
    · exact hC u d e n Q hQ (by omega)
  · by_cases hblk : L53.HasParentInBlock Q
    · exact mTower_mem_of_step' hbig hs hblk (hA u d e Q hQ hbig hs hblk) n
    · exact hB u d e n Q hQ hbig hs hblk

/-! ### 80.1 ⟹ 3 本の内訳と難度の見立て

    **A `MTowerStepAll`** … 本丸。`mTower Q d e n ++ shiftr01 (d*n) 0 ((Lift1 Q (e*n))⟦m⟧)`
        **`n` の帰納も段の帳尻も無い 1 文**（§71）。連結が壁
    **B `MTowerOrphan`** … §79 で `srow = 1` かつ根の行 1 が末尾以上、または
        `srow = 2` かつ（錐の外 または 行 2 が根以下）に限る。**狭い**
    **C `MTowerSingle`** … `Q = [(c,b,z)]` なら `mTower = [(c,b,z),(c+d,b+e,z),…]`
        ＝ **等差の 1 列列**。`z = 0` なら §76 で無料。**残るのは `z ≥ 1` だけ**

⟹ **C は `z ≥ 1` の等差列 1 本**なので、いちばん易しいはず。
`Wchar.mem_iff_lev_le` と `Wset.singleton_mem_W` の周りで閉じる可能性がある。

### 80.2 ⚠ まだ `MTowerClosedS` の証明ではない

3 本とも未証明である。**やったのは「無料の枝を全部落として、残差を 3 つに名前をつけた」だけ。**
`GraftAll` の代わりに置いた `MTowerClosedS`（§74）は、いま

    **A（連結 1 文）＋ B（狭い孤児枝）＋ C（等差 1 列列、`z ≥ 1`）**

に分かれている。 -/

/-! ## 81. ★★★★★★ **残差 C（`MTowerSingle`）は定理**

`|Q| = 1` なら塔は **1 列ずつの等差列**である。行 2 は塔全体で**一定**なので:

    `z = 0` … §76（行 2 ≡ 0）で無料
    `z ≥ 1` … 末尾列の `srow = 2` だが **`nextrel2` は行 2 の狭義増加を要求する**
              ⟹ **行 2 が一定なら親は存在しない ⟹ `oper` は `Pred`（末尾を剥がすだけ）**
              ⟹ `n` の帰納で閉じる

**⟹ 残差 3 本のうち C は落ちた。** -/

theorem row2_const_shiftr01 {Q : TrioSeq} {z d0 d1 : ℕ} (h : ∀ p ∈ Q, p.2.2 = z) :
    ∀ p ∈ shiftr01 d0 d1 Q, p.2.2 = z := by
  intro p hp
  unfold shiftr01 at hp
  rw [List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact h q hq

theorem row2_const_Lift1 {X : TrioSeq} {z d : ℕ} (h : ∀ p ∈ X, p.2.2 = z) :
    ∀ p ∈ Lift1 X d, p.2.2 = z := by
  intro p hp
  unfold Lift1 at hp
  rw [List.mem_map] at hp
  obtain ⟨j, hj, hjp⟩ := hp
  rw [List.mem_range] at hj
  rw [← hjp]
  show entry X 2 j = z
  exact h _ (entry_pair_mem (B := X) hj)

theorem row2_const_mTower {Q : TrioSeq} {z : ℕ} (h : ∀ p ∈ Q, p.2.2 = z) (d e n : ℕ) :
    ∀ p ∈ mTower Q d e n, p.2.2 = z := by
  intro p hp
  unfold mTower at hp
  rw [List.mem_flatMap] at hp
  obtain ⟨k, -, hk⟩ := hp
  exact row2_const_Lift1 (row2_const_shiftr01 h) p hk

theorem entry2_of_const {M : TrioSeq} {z j : ℕ} (h : ∀ p ∈ M, p.2.2 = z)
    (hj : j < M.length) : entry M 2 j = z :=
  h _ (entry_pair_mem (B := M) hj)

theorem mTower_length (Q : TrioSeq) (d e : ℕ) :
    ∀ n, (mTower Q d e n).length = n * Q.length := by
  intro n
  induction n with
  | zero => simp [mTower]
  | succ n ih =>
      rw [mTower_succ, List.length_append, ih, Lift1_length, shiftr01_length]
      exact (Nat.succ_mul n Q.length).symm

theorem mTower_dropLast_of_single {Q : TrioSeq} (h1 : Q.length = 1) (d e n : ℕ) :
    (mTower Q d e (n + 1)).dropLast = mTower Q d e n := by
  have hlen : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length = 1 := by
    rw [Lift1_length, shiftr01_length, h1]
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
  rw [mTower_succ, hx, List.dropLast_concat]

open Classical in
/-- **行 2 が一定なら末尾列は行 2 の親を持たない**（`nextrel2` は狭義増加を要求）。 -/
theorem not_hasParent_two_of_row2_const {M : TrioSeq} {z : ℕ}
    (h : ∀ p ∈ M, p.2.2 = z) (hlen : 0 < M.length) :
    ¬ hasParent M 2 (M.length - 1) := by
  rintro ⟨j0, hj0, -⟩
  unfold nextR at hj0
  rw [if_neg (by omega), if_neg (by omega)] at hj0
  have hj0lt : j0 < M.length := hj0.1
  have hlt := hj0.2.2.2.1
  rw [entry2_of_const h hj0lt, entry2_of_const h (by omega)] at hlt
  omega

open Classical in
/-- **★★★★★★ 残差 C は定理。** -/
theorem mTowerSingle_holds : MTowerSingle := by
  intro u d e n Q hQ h1
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
  rcases Nat.eq_zero_or_pos z with hz0 | hzpos
  · refine mTower_mem_of_zeroRow2 ?_ hQ d e n
    intro p hp
    rw [hconstQ p hp, hz0]
  · induction n with
    | zero => simpa using W_nil u
    | succ n ih =>
        rcases Nat.eq_zero_or_pos n with hn0 | hnpos
        · subst hn0
          rwa [mTower_one]
        · have hconst := row2_const_mTower hconstQ d e (n + 1)
          have hML : (mTower Q d e (n + 1)).length = n + 1 := by
            rw [mTower_length, h1, Nat.mul_one]
          have hMpos : 0 < (mTower Q d e (n + 1)).length := by omega
          have hML1 : (mTower Q d e (n + 1)).length - 1 ≠ 0 := by omega
          have hsr : srow (mTower Q d e (n + 1))
              ((mTower Q d e (n + 1)).length - 1) = 2 := by
            unfold srow
            rw [if_pos (by rw [entry2_of_const hconst (by omega)]; omega)]
          have hnp : ¬ hasParent (mTower Q d e (n + 1))
              (srow (mTower Q d e (n + 1)) ((mTower Q d e (n + 1)).length - 1))
              ((mTower Q d e (n + 1)).length - 1) := by
            rw [hsr]
            exact not_hasParent_two_of_row2_const hconst hMpos
          have hzz : ¬ (entry (mTower Q d e (n + 1)) 0
                ((mTower Q d e (n + 1)).length - 1) = 0 ∧
              entry (mTower Q d e (n + 1)) 1
                ((mTower Q d e (n + 1)).length - 1) = 0 ∧
              entry (mTower Q d e (n + 1)) 2
                ((mTower Q d e (n + 1)).length - 1) = 0) := by
            rintro ⟨-, -, h2⟩
            rw [entry2_of_const hconst (by omega)] at h2
            omega
          refine mem_of_oper_mem (fun m hm => ?_)
          rw [oper_eq_pred_of_noParent m hML1 hzz hnp]
          unfold Pred
          rw [if_neg (by omega), mTower_dropLast_of_single h1]
          exact ih

/-! ### 81.1 ⟹ 残るのは A と B の 2 本

    ⛔ **C `MTowerSingle`** … **落ちた**（上）
    **A `MTowerStepAll`** … 本丸。「塔 ＋ 1 ブロックの展開」の連結 1 文
    **B `MTowerOrphan`** … §79 で狭い条件（`srow ∈ {1,2}` かつ末尾列が根より上に行けない）

⟹ **`GraftAll` の代わりは A ＋ B の 2 本。** -/

/-! ## 82. ★★★★★★ 残差 A を「塔に限った `GraftAll`」まで落とす

### 82.1 ⚠ まず構造の自覚: **`catBlock` は `graft` そのもの**

    `graft S y = S.dropLast ++ shiftr01 (entry S 0 (|S|-1)) 0 y`   （`Wset.lean:67`）
    `catBlock`  … `A ++ shiftr01 c 0 B`

**同じ形である。** ⟹ §78 の分解は **`Gamma.lean` の `GraftAll` 機械の再演**にあたる。

> **⟹ C-1 と C-2 の差は「`y` の範囲」だけ。**
> `GraftAll` … **すべての `y ∈ W u`** について要求する
> `MTowerStep` … **`Lift1 Q (e*n)` の導出に出てくる `y`** だけでよい
> **⟹ C-2 は `GraftAll` の真の制限版である。**（§74 で `GraftAll` 抜きの経路が
> 緑になっているので、これは循環ではない。）

### 82.2 ★ 段は 2 つに分かれる

§78 の `A2'` は `B` の段と結論の段を**別々に取れる**（`aop_clause3_to_clause2` も
`not_domT_nil` も `B` 側の段しか見ない）。⟹ **リフトで段が上がっても構わない。** -/

open Classical in
/-- **§78 の 2 段版**: 継ぐ側 `B` の段 `u'` と、全体の段 `u` は独立でよい。 -/
theorem catBlock_of_escape' {u u' c : ℕ} {A : TrioSeq} (hA : A ∈ W u)
    (hesc : ∀ B : TrioSeq, 1 ≤ B.length →
      ¬ L53.HasParentInBlock (shiftr01 c 0 B) →
      A ++ shiftr01 c 0 B ∈ W u) :
    ∀ B : TrioSeq, B ∈ W u' → A ++ shiftr01 c 0 B ∈ W u := by
  have hsub : W u' ⊆ {B : TrioSeq | A ++ shiftr01 c 0 B ∈ W u} := by
    refine A2' ?_
    rintro B (⟨hl, -⟩ | hop | ⟨m', hm', hd, hgr⟩)
    · rcases Nat.eq_zero_or_pos B.length with h0 | hpos
      · have hnil : B = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        show A ++ shiftr01 c 0 ([] : TrioSeq) ∈ W u
        simpa using hA
      · refine hesc B (by omega) ?_
        refine not_hasParentInBlock_of_short ?_
        rw [shiftr01_length]; omega
    · show A ++ shiftr01 c 0 B ∈ W u
      rcases Nat.lt_or_ge B.length 2 with hsm | hbig
      · have hres := hop 1 le_rfl
        rwa [oper_eq_self_of_short 1 (by omega)] at hres
      · by_cases hblk : L53.HasParentInBlock (shiftr01 c 0 B)
        · exact catBlock_step hbig hblk (fun m hm => hop m hm)
        · exact hesc B (by omega) hblk
    · show A ++ shiftr01 c 0 B ∈ W u
      rcases Nat.lt_or_ge B.length 2 with hsm | hbig
      · have hBne : B ≠ [] := by
          intro hc
          rw [hc] at hd
          exact not_domT_nil m' hd
        have h1 : 0 < B.length := List.length_pos_iff.mpr hBne
        refine hesc B (by omega) ?_
        refine not_hasParentInBlock_of_short ?_
        rw [shiftr01_length]; omega
      · have hop := aop_clause3_to_clause2 hbig hd hgr
        by_cases hblk : L53.HasParentInBlock (shiftr01 c 0 B)
        · exact catBlock_step hbig hblk (fun m hm => hop m hm)
        · exact hesc B (by omega) hblk
  exact fun B hB => hsub hB

/-! ### 82.3 ★★★★★★ ⟹ 残差 A は「塔に 1 列を継ぐ」だけになる

`Q` に**リフト装備**（`∀ s, ∃ u', Lift1 Q s ∈ W u'`）があれば、
`n` の帰納の各段で `catBlock_of_escape'` が使える。**装備は応用側で無料**である:
`Q = Lift1 ((0,v,z) :: R.dropLast) t` なので
`Lift1 Q s = Lift1 ((0,v,z) :: R.dropLast) (t+s)` は**接頭辞装備そのもの**。 -/

open Classical in
/-- **★★★★★★ 塔の閉包は「塔に 1 列を継ぐ」1 文に落ちる**（リフト装備つき）。 -/
theorem mTowerClosed_of_escape {u : ℕ} {Q : TrioSeq} {d e : ℕ} (h2 : 2 ≤ Q.length)
    (hs : ∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j)
    (hblk : L53.HasParentInBlock Q)
    (hlift : ∀ s : ℕ, ∃ u' : ℕ, Lift1 Q s ∈ W u')
    (hesc : ∀ (n : ℕ) (B : TrioSeq), 1 ≤ B.length →
      ¬ L53.HasParentInBlock (shiftr01 (d * n) 0 B) →
      mTower Q d e n ∈ W u → mTower Q d e n ++ shiftr01 (d * n) 0 B ∈ W u) :
    ∀ n, mTower Q d e n ∈ W u := by
  intro n
  induction n with
  | zero => simpa using W_nil u
  | succ n ih =>
      refine mem_of_oper_mem (fun m hm => ?_)
      rw [oper_mTower' h2 hs hblk d e n m, mTower_step_shift]
      obtain ⟨u', hu'⟩ := hlift (e * n)
      have hQ2 : 2 ≤ (Lift1 Q (e * n)).length := by rw [Lift1_length]; exact h2
      exact catBlock_of_escape' ih (fun B h1 hnb => hesc n B h1 hnb ih)
        ((Lift1 Q (e * n))⟦m⟧) (oper_mem_of_mem hQ2 hu' m hm)

/-! ### 82.4 ⟹ 残差の最終形（`GraftAll` との比較）

    **`GraftAll`** … 装備つき文脈 `S` ＋ **任意の `y ∈ W u`** ⟹ `Lift1 ((0,v,z) :: graft S y) t ∈ W a`
    **`hesc`**     … **塔 `mTower Q d e n`** ＋ **1 列（または段内で孤児の塊）** ⟹ 連結が `W u`

    左が `W` の元**すべて**を相手にするのに対し、右は
    **「塔」＋「継ぐ側が段内で孤児」**という 2 重の制限がついている。

⚠ **`hesc` は `|B| = 1` のとき任意の列の snoc になる**（§78.2）ので、
**`WSnoc` を含む**のは変わらない。ただし土台 `A` が**塔**に固定されたので、
`Wtower2.snoc_orphan`（孤児なら無料）／`snoc_flat_root`（`srow=0` かつ親が根なら無料）
の適用範囲が**塔の構造から決まる**。**そこが次に調べるところ。** -/

/-! ## 83. `hesc` の無料の枝と、今日の到達点

`hesc`（§82）の `|B| = 1` の枝は、**継いだ列が孤児のままなら無料**である
（`snoc_orphan_W`、§4、既存）。⟹ 残るのは「**継いだ塊が土台 `A` の中に親を見つける**」場合。 -/

theorem hesc_single_orphan {u c : ℕ} {A : TrioSeq} (hA : A ∈ W u) (hAne : A ≠ [])
    {B : TrioSeq} (h1 : B.length = 1)
    (hnp : ¬ hasParent (A ++ shiftr01 c 0 B)
      (srow (A ++ shiftr01 c 0 B) A.length) A.length) :
    A ++ shiftr01 c 0 B ∈ W u := by
  obtain ⟨q, hq⟩ := List.length_eq_one_iff.mp h1
  subst hq
  have hsh : shiftr01 c 0 [q] = [((q.1 + c, q.2.1, q.2.2) : ℕ × ℕ × ℕ)] := by
    unfold shiftr01
    simp
  rw [hsh] at hnp ⊢
  exact snoc_orphan_W _ hA hAne hnp

/-! ### 83.1 ⟹ 今日の到達点（`GraftAll` の置き換え）

    **`Final.TRIO_terminates_of_mTowerClosedS`**（緑）
      ⟸ `L105.wstar2s_closed_of_mTowerClosedS`（§75、緑）
        ⟸ `liftTower1_of_shiftTowerClosedS`（§73、緑）
          ＋ `liftTowerExp2_of_mTowerClosedS`（§74、緑）
          ＋ `Lcone.liftInner_holds`（無条件・緑）
      ⟸ **`MTowerClosedS`**（§74、**未証明**、5 量化 / 2 前提）
        無料の枝: 行 2 ≡ 0（§76）／`n ≤ 1`（§77）／`srow = 0` の孤児は起きない（§79）
        **残差 C `MTowerSingle` … ⛔ 証明ずみ（§81）**
        **残差 B `MTowerOrphan` … 未証明**（§79 で狭い条件に限る）
        **残差 A `MTowerStepAll` … `hesc`（§82）1 文に落ちた**
          さらに `hesc` の孤児 snoc の枝は無料（上）

⟹ **未証明は 2 本**:

    **(A') `hesc`** … 塔 `mTower Q d e n` に、段内で孤児の塊を継ぐ
    **(B) `MTowerOrphan`** … `Q` の末尾列が段内で孤児のときの塔

**どちらも「悪根／親が自分のブロックを出て前へ逃げる」という同じ現象**である
（§67 の「悪根 ＝ 根」、R2 の (D)、H12 の §231 と同じ場所）。

### 83.2 ⚠ 今日いちばん効いた道具（次の人へ）

    **`Lcone.oper_eq_gexp_gen`（`:487`、任意の悪根、緑）**
      —— `j0 = 0` で読むと `take` が空になり **`M⟦n⟧ = mTower M.dropLast d0 d1 n`**（§68）
    **`Lcone.liftInner_holds`（`:507`、無条件、緑）**
      —— `j0 ≥ 1` の可換性を**全部**片づける。残差が `j0 = 0` に絞れる（§67）
    **`Wchar.mem_of_oper_mem` / `aop_clause3_to_clause2`**
      —— 段と節 3 を消す。**帰納法が要らなくなる場面が多い**（§71、§82）
    **`L53.comm_of_hasParentInBlock`（`L53Subst:922`、緑）**
      —— 「段内に親があれば展開は前半を触らない」。塔の帰納の心臓

### 83.3 ⚠ 今日の規律の失敗（記録）

**既存補題の再発明が 7 回**（`shTower` 系 ×2、`srow_cons_last`、`entry_cons_last`、
`mTower_one`、`srow_shiftr01`、`oper_of_srow1_par0` は寸前で回避）。
**「新しい補題を書く前に `grep`」を毎回やること。** 2 回は `leanman check` の
`already been declared` が救ってくれたが、名前が違うと通ってしまう。 -/

/-! ## 84. ★★★★★★ 課題 (E): **`j0 = 0` の錐輸送**（R2 の (D) そのもの）

`Lcone.gexp_cone_mir`（`:106`、緑）は **`hj0 : 0 < j0`**（悪根がブロックの内側）を要求する。
塔は **`j0 = 0`** なので当たらない —— それが R2 の (D)／H12 の §231 の正体である。

**ところが `hj0` の使い所は 3 つしかない**（証明を読んだ）:

    1 `gexp_root_shallow`（展開でも根が最浅）… **`0 < d0` が代わりになる**
    2 `gexp_entry_low hlen hj0`（位置 0 は take 部）… **`gexp_entry_root` が代わりになる**
    3 `y < j0` の枝 … **`j0 = 0` では空虚**

そして `j0 = 0` で新たに要るのは **`0 < d1`** だけである
（ブロック `k` の根が根の錐に入るために。`d1 = 0` だと**実際に偽**: ブロックの根の行 1 が
上がらないので `nextrel1` の狭義増加が破れる）。⟹ **`srow = 2` の塔ではちょうど `d1 > 0`**
（`L53.tower2_vw`）。 -/

/-- **`j0 = 0` 版の「展開でも根が狭義に最浅」**: `0 < j0` の代わりに **`0 < d0`**。 -/
theorem gexp_root_shallow_zero {M : TrioSeq} {Lb d0 d1 n : ℕ}
    (hlen : 0 + Lb + 1 = M.length) (hn : 0 < n) (hLb : 0 < Lb) (hd0pos : 0 < d0)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l) :
    ∀ l, 0 < l → l < (gexp M 0 Lb d0 d1 n).length →
      entry (gexp M 0 Lb d0 d1 n) 0 0 < entry (gexp M 0 Lb d0 d1 n) 0 l := by
  intro l hl0 hl1
  rw [gexp_length hlen] at hl1
  rw [gexp_entry_root hlen hn hLb]
  obtain ⟨k, q, hk, hq, rfl⟩ := gexp_pos_decomp hLb (Nat.zero_le l) hl1
  rw [gexp_entry0_mir hlen hk hq, Nat.zero_add]
  rcases Nat.eq_zero_or_pos q with rfl | hqpos
  · have hk1 : 0 < k := by
      by_contra hc
      have hk0 : k = 0 := by omega
      subst hk0
      omega
    have hkd : 0 < k * d0 := Nat.mul_pos hk1 hd0pos
    omega
  · have := hr0 q (by omega) (by omega)
    omega

open Classical in
/-- **★★★★★★ 課題 (E) の答え: `j0 = 0` でも根の錐は位置対応どおりに移る。**
`Lcone.gexp_cone_mir` の `0 < j0` を **`0 < d0` ＋ `0 < d1`** に置き換えたもの。 -/
theorem gexp_cone_mir_zero {M : TrioSeq} {Lb d0 d1 n k q : ℕ}
    (hlen : 0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hk : k < n) (hq : q < Lb)
    (hd1pos : 0 < d1)
    (hd0e : entry M 0 (0 + Lb) = entry M 0 0 + d0)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + Lb)) :
    le1 (gexp M 0 Lb d0 d1 n) 0 (0 + (k * Lb + q)) ↔ le1 M 0 (0 + q) := by
  classical
  -- ★ R2 の (v): `hup` と `hd0pos` は `hr0` ＋ `hd0e` から出る（前提 2 本を削除）
  have hup : ∀ l, 0 < l → l ≤ 0 + Lb → entry M 0 0 < entry M 0 l :=
    fun l hl0 hl1 => hr0 l hl0 (by omega)
  have hd0pos : 0 < d0 := by
    have h := hr0 (0 + Lb) (by omega) (by omega)
    rw [hd0e] at h
    omega
  have hn : 0 < n := by omega
  have hXlen : (gexp M 0 Lb d0 d1 n).length = 0 + n * Lb := gexp_length hlen
  have hbnd : k * Lb + q < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hplt : 0 + (k * Lb + q) < (gexp M 0 Lb d0 d1 n).length := by
    rw [hXlen]; omega
  have hqlt : 0 + q < M.length := by omega
  have hrX := gexp_root_shallow_zero (d1 := d1) hlen hn hLb hd0pos hr0
  have h10 : entry (gexp M 0 Lb d0 d1 n) 1 0 = entry M 1 0 :=
    gexp_entry_root hlen hn hLb
  have hMj0q : Relation.ReflTransGen (nextrel0 M) 0 (0 + q) :=
    rtg0_of_window (by omega) (by omega) (fun l hl0 hl1 => hup l hl0 (by omega))
  have hXj0p : Relation.ReflTransGen (nextrel0 (gexp M 0 Lb d0 d1 n)) 0
      (0 + (k * Lb + q)) :=
    gexp_rtg0_root hlen hn hLb hup hd0pos _ (by omega) (by omega)
  rw [le1_zero_iff hrX hplt, le1_zero_iff hr0 hqlt, h10]
  constructor
  · intro hXw y hyq hy0
    have hyle : y ≤ 0 + q := nextrel0_rtrancl_index_le hyq
    obtain ⟨q', hq'e⟩ : ∃ q', y = 0 + q' := ⟨y, by omega⟩
    subst hq'e
    have hq'lt : q' < Lb := by omega
    have hmir : Relation.ReflTransGen (nextrel0 (gexp M 0 Lb d0 d1 n))
        (0 + (k * Lb + q')) (0 + (k * Lb + q)) :=
      gexp_rtg0_mir hlen hk hyq q rfl hq
    have h := hXw (0 + (k * Lb + q')) hmir (by omega)
    rw [gexp_entry1_mir hlen hk hq'lt] at h
    by_cases hg : le1 M 0 (0 + q')
    · have := le1_entry1_lt hg (by omega)
      omega
    · rw [if_neg hg] at h
      omega
  · intro hMw y hyp hy0
    obtain ⟨k', q', hk', hq', hye, hcase⟩ :=
      gexp_chain_inversion hlen hk hq hup hd0e y hyp (Nat.zero_le y)
    subst hye
    rw [gexp_entry1_mir hlen (by omega) hq']
    rcases Nat.eq_zero_or_pos q' with rfl | hq'pos
    · have hk'pos : 0 < k' := by
        by_contra hc
        have hk'0 : k' = 0 := by omega
        subst hk'0
        omega
      rw [if_pos (le1_refl (show 0 + 0 < M.length by omega))]
      have hkd : 0 < k' * d1 := Nat.mul_pos hk'pos hd1pos
      have he : entry M 1 (0 + 0) = entry M 1 0 := rfl
      omega
    · have hbase : entry M 1 0 < entry M 1 (0 + q') := by
        rcases hcase with ⟨-, hM⟩ | ⟨-, hM⟩
        · exact hMw (0 + q') hM (by omega)
        · have hchain : Relation.ReflTransGen (nextrel0 M) 0 (0 + q') :=
            rtg0_of_window (by omega) (by omega)
              (fun l hl0 hl1 => hup l hl0 (by omega))
          exact le1_chain_window hlp.2.2 (0 + q') hchain hM (by omega)
      split_ifs <;> omega

/-! ### 84.1 ⟹ これが (D) である

`gexp_cone_mir_zero` は「**塔の第 `k` ブロックの位置 `q` が根の錐に入る ⟺
`M` の位置 `q` が根の錐に入る**」で、まさに R2 の (A)+(B)、H12 の §231 である。

⚠ **`0 < d1` が本質的**である。`d1 = 0` だとブロック `k` の根の行 1 が上がらないので
`nextrel1` の狭義増加が破れ、**文は実際に偽**になる（`k ≥ 1`, `q = 0`）。
⟹ **`srow = 1` の塔（`d1 = 0`）ではこの形は使えない。** そちらは
`mTower Q d 0 n = shTower Q d n`（`Lift1` が消える）なので**そもそも錐が要らない**。 -/

/-! ## 85. ★★★★★★ (D) を `mTower` の言葉に: **塔の錐はブロック局所**

§68 の `gexp_zero_eq_mTower` で §84 を `mTower` に移す。 -/

open Classical in
/-- **★★★★★★ 塔の第 `k` ブロックの位置 `q` が根の錐に入る ⟺ `Q` の位置 `q` が入る。**
＝ R2 の (A)+(B)、H12 の §231。 -/
theorem le1_mTower_block {M : TrioSeq} {d e n k q : ℕ} (hM2 : 2 ≤ M.length)
    (hd1pos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hk : k < n) (hq : q < M.dropLast.length) :
    le1 (mTower M.dropLast d e n) 0 (k * M.dropLast.length + q)
      ↔ le1 M.dropLast 0 q := by
  have hdl : M.dropLast.length = M.length - 1 := List.length_dropLast
  have hlen : 0 + M.dropLast.length + 1 = M.length := by rw [hdl]; omega
  have hLb : 0 < M.dropLast.length := by rw [hdl]; omega
  have hgexp : gexp M 0 M.dropLast.length d e n = mTower M.dropLast d e n := by
    rw [gexp_zero_eq_mTower (by omega), hdl, ← List.dropLast_eq_take]
  have hres := gexp_cone_mir_zero hlen hLb hk hq hd1pos hd0e hr0 hlp
  rw [hgexp, Nat.zero_add, Nat.zero_add] at hres
  rw [hres, List.dropLast_eq_take, le1_take (by omega) (by rw [hdl] at hq; omega)]

/-! ### 85.1 ⟹ これで (B)/(D) の障害が消えた

§283 で私は「`Q` の中で孤児でも、塔の中では前のブロックに親が見つかりうる。
それが無いことを言うには `le1` のブロック局所性が要る」と報告した。
**その `le1` のブロック局所性が上で定理になった。**

⚠ ただし上は**根からの錐 `le1 T 0 ·`** の局所性である。
`nextrel2` が要求するのは **一般の `le1 T y ·`** なので、そのままでは (B) に直結しない。
**次はそこ**（`le1 T y ·` の局所性、または `nextrel2` の候補が同ブロックに限ることの直接証明）。 -/

/-! ## 86. ★★★★★ **ブロックの根は壁**（行 0 の鎖はブロックを飛び越せない）

`le1 T y ·` の一般の局所性（§85.1 の次の一手）に向けた基本補題。
**ブロック `k` の根は、そのブロックのどの列よりも狭義に浅い**ので、
`nextrel0` の「途中に窪みなし」条項が、ブロック外からの 1 歩を禁じる。 -/

theorem nextrel0_gexp_no_skip {M : TrioSeq} {Lb d0 d1 n k q y : ℕ}
    (hlen : 0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hk : k < n) (hq : q < Lb)
    (hq1 : 0 < q)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (h : nextrel0 (gexp M 0 Lb d0 d1 n) y (0 + (k * Lb + q))) :
    k * Lb ≤ y := by
  by_contra hc
  have hmin := h.2.2.2.2 (0 + k * Lb) ⟨by omega, by omega⟩
  rw [show (0 : ℕ) + k * Lb = 0 + (k * Lb + 0) from by omega] at hmin
  rw [gexp_entry0_mir hlen hk hq, gexp_entry0_mir hlen hk hLb] at hmin
  have hlt := hr0 (0 + q) (by omega) (by omega)
  simp only [Nat.add_zero] at hmin
  omega

/-! ### 86.1 ⟹ 何が言えたか

    **ブロック `k` の**根以外**の列 `p` の行 0 の親は、必ず同じブロック `k` の中にある。**

⟹ ブロック `k` の列の行 0 の祖先鎖は、**ブロック `k` の根に着くまでブロックを出ない**。
（根に着いた後は前のブロックへ出られる。それが `Gtrans.gexp_chain_inversion` の
`k' < k` の枝。）

### 86.2 ⟹ 次の一手（`le1 T y ·` の局所性）

`nextrel1 T a b` は `le0 T a b` を要求し、極小性条項

    `∀ j, a < j ∧ le0 T j b → entry T 1 b ≤ entry T 1 j`

を持つ。`b` がブロック `k` の列なら、上より **ブロック `k` の根 `r_k` は `le0 T r_k b`**
を満たすので、`a` がブロック外なら `a < r_k` で `j := r_k` が取れて

    **`entry T 1 b ≤ entry T 1 r_k`**

が必要になる。`r_k` の行 1 は `entry M 1 0 + k*d1`（根は必ず錐の中）。
⟹ **`b` が `Q` の錐の中なら `entry M 1 (b の元) + k*d1 ≤ entry M 1 0 + k*d1`、
つまり `entry M 1 (b の元) ≤ entry M 1 0` が必要**だが、
錐の中なら `Lcone.le1_entry1_lt` で **`entry M 1 0 < entry M 1 (b の元)`** ⟹ **矛盾**。

> **⟹ 「`b` が `Q` の錐の中」なら、`nextrel1` はブロック外から入れない。**
> ⟹ そのとき `le1 T y b` は `y` を同じブロックに閉じ込める。**(B) の道具になる。**

⚠ **錐の外の `b` については別**（`+k*d1` が付かないので上の矛盾が出ない）。**そこが残る。** -/

/-! ## 87. ★★★★★★ **錐の中の列には、ブロック外から行 1 の親は来ない**

§86.2 の設計図の実装。`nextrel1` の極小性条項に**ブロック `k` の根**を代入する。
根は必ず錐の中なので行 1 が `+k*d1` され、目標の列も錐の中なら同じだけ上がる
⟹ 比較が `Q` の中の比較に戻り、`Lcone.le1_entry1_lt` で矛盾する。 -/

open Classical in
theorem nextrel1_gexp_no_enter {M : TrioSeq} {Lb d0 d1 n k q a : ℕ}
    (hlen : 0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hk : k < n) (hq : q < Lb)
    (hq1 : 0 < q) (hcone : le1 M 0 (0 + q))
    (hup : ∀ l, 0 < l → l ≤ 0 + Lb → entry M 0 0 < entry M 0 l)
    (h : nextrel1 (gexp M 0 Lb d0 d1 n) a (0 + (k * Lb + q))) :
    k * Lb ≤ a := by
  by_contra hc
  have hXlen : (gexp M 0 Lb d0 d1 n).length = 0 + n * Lb := gexp_length hlen
  have hbnd : k * Lb + q < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hMq : Relation.ReflTransGen (nextrel0 M) (0 + 0) (0 + q) :=
    rtg0_of_window (by omega) (by omega) (fun l hl0 hl1 => hup l hl0 (by omega))
  have hrtg : Relation.ReflTransGen (nextrel0 (gexp M 0 Lb d0 d1 n))
      (0 + (k * Lb + 0)) (0 + (k * Lb + q)) :=
    gexp_rtg0_mir hlen hk hMq q rfl hq
  have hle0 : le0 (gexp M 0 Lb d0 d1 n) (0 + (k * Lb + 0)) (0 + (k * Lb + q)) :=
    ⟨by rw [hXlen]; omega, by rw [hXlen]; omega, hrtg⟩
  have hmin := h.2.2.2.2.2 (0 + (k * Lb + 0)) ⟨by omega, hle0⟩
  rw [gexp_entry1_mir hlen hk hq, gexp_entry1_mir hlen hk hLb] at hmin
  rw [if_pos hcone, if_pos (le1_refl (show (0 : ℕ) < M.length from by omega))] at hmin
  have hlt := le1_entry1_lt hcone (show (0 : ℕ) ≠ 0 + q from by omega)
  have he : entry M 1 (0 + 0) = entry M 1 0 := rfl
  omega

/-! ### 87.1 ⟹ 系: 錐の中の列への `le1` はブロックに閉じる

`le1 T y b` は `nextrel1 T` の反射推移閉包なので、**最後の 1 歩**が
`nextrel1 T a b` である。`b` が錐の中のブロック `k` の列（根以外）なら、上より
`a` も同じブロックにある。⟹ **鎖はブロック `k` から出られない**（帰納で繰り返せる）。

⚠ **`b` が錐の外なら別**（`+k*d1` が付かないので上の矛盾が出ない）。
そこは `Q` 側で `le1 Q 0 b` が偽の場合で、**ブロッカーの向こう側**にあたる。
**(B) の残りはそこだけ。** -/

/-! ## 88. ⚠ 課題 2（`oper_mTower` から `hblk` を落とす）への回答: **箱を疑うべき**

### 88.1 私が持っている「復活しない」の道具と、その射程

    **`srow = 0`** … **§86（行 0 の壁）で無料**。ブロック外から行 0 の親は来ない。
        ⟹ `N` の中で孤児なら `A ++ N` でも孤児 ⟹ **復活しない**（`hblk` 不要）
    **`srow = 1` かつ末尾列が `Q` の錐の中** … **§87 で無料**
    **`srow = 2` かつ末尾列が `Q` の錐の中かつ `entry Q 2 (last) > entry Q 2 0`**
        … 極小性条項にブロックの根を入れて矛盾（§87 と同じ骨）

⚠ ところが **§79** により、後ろの 2 つは**そもそも `hblk` が成り立つ場合**である
（`hasParentInBlock_of_srow_{one,two}`）。⟹ **`hblk` が破れる側では、私の道具は届かない。**

### 88.2 ⚠ **R2 の §R131 の「破れ 0」は箱の産物の疑いがある**（教訓 21 / 27）

R2 の箱は **`n, m ∈ {1,2}`**（`R2-NOTES.md` §R131 (x1)）。しかし復活が起きるとしたら
その形は **`n*d1` が大きいとき**である:

    `nextrel1 T a (block n の末尾列)` の極小性は `j := block n の根` で
      **`entry T 1 last ≤ entry T 1 (root n) = entry Q 1 0 + n*d1`**
    を要求する。末尾列が **`Q` の錐の外**なら `entry T 1 last = entry Q 1 (last)`（リフト無し）
    ⟹ 条件は **`entry Q 1 (last) ≤ entry Q 1 0 + n*d1`**
    ⟹ **`n` が小さいと満たせない。`n` を大きくすると満たせる。**

> **⟹ 「反例が起きるとしたらどういう形か」（教訓 45）: `srow ∈ {1,2}` かつ
> 末尾列が `Q` の錐の外で、`n*d1 ≥ entry Q 1 (last) - entry Q 1 0`。**
> **R2 の `n ≤ 2` の箱では、この形が母集団にほとんど入っていない可能性が高い。**

⟹ **`hblk` を落とす前に、`n` を 3〜5 まで伸ばして測り直すこと。**
**`n` は塔の高さなので、伸ばす軸としていちばん自然である。**

### 88.3 ⟹ 私の判断

**`oper_mTower` の `hblk` は残す。** 代わりに §80 の残差分割
（`hblk` あり ＝ A、`hblk` なし ＝ B）をそのまま使う。
**§79 が B を狭めているので、B は「末尾列が錐の外」または「行 2 が根以下」だけ**であり、
**それは §88.2 の反例の形と同じ**である。⟹ **同じ 1 点を 2 方向から見ている。** -/

/-! ## 89. 錐の列の行 1 の親も錐の中

§87 を鎖に沿って繰り返すための 1 本。`nextrel1` の親は一意（`Wset.nextrel1_uniq_src`）なので、
根からの鎖は必ずその親を通る。 -/

theorem le1_zero_of_nextrel1 {T : TrioSeq} {a b : ℕ} (hb : le1 T 0 b) (hne : b ≠ 0)
    (h : nextrel1 T a b) : le1 T 0 a := by
  obtain ⟨h0, hblt, hchain⟩ := hb
  rcases hchain.cases_tail with heq | ⟨c, hc1, hc2⟩
  · exact absurd heq hne
  · have hca : c = a := nextrel1_uniq_src hc2 h
    subst hca
    exact ⟨h0, h.1, hc1⟩

/-! ### 89.1 ⟹ 鎖に沿って §87 を繰り返す形

`le1 T 0 b`（塔全体の錐）＋ `b` がブロック `k` の**根以外**の列
⟹ §87 で行 1 の親 `a` は同じブロック `k`、⟹ 上で `le1 T 0 a`
⟹ `a` が根以外ならまた §87 …

**⟹ 鎖はブロック `k` の根に着くまでブロックを出ない。**
根に着いた後は前のブロックへ出るが、そこは `le1_mTower_block`（§85）と
`tower_anc0_not_blocker`（§63）が押さえている領域である。

⚠ **残るのは「`b` が錐の外」の場合だけ**（§87 の但し書き）。
team-lead が R2 に「錐の外の `b` がどれだけ出るか」を測らせている。 -/

/-! ## 90. ★★★★★★ §78.2 の壁を外す: **`hesc` の底は「決まった 1 列」**

§78.2 で「`|B| = 1` のとき残差は任意の列の snoc ＝ `WSnoc` を含む」と判定した。
**それは `B` を `W u'` 全体で回したからである。**

**`oper` も `graft` も先頭列を変えない**（`Wset.oper_headD`（`:1509`、緑）／
`graft M z = M.dropLast ++ …` で `|M| ≥ 2` なら先頭は残る）ので、
**派生の途中の `B` はすべて出発点と同じ先頭列を持つ。**

⟹ **`|B| = 1` に落ちたときの `B` は「出発点の先頭列 1 本」に確定する。**
**⟹ 任意の snoc ではない。`WSnoc` は含まれない。** -/

open Classical in
/-- **★★★★★★ 先頭列を固定した `catBlock`**: 底が 1 つの決まった snoc になる。 -/
theorem catBlock_of_escape_head {u u' c : ℕ} {A : TrioSeq} {p : ℕ × ℕ × ℕ}
    (hA : A ∈ W u)
    (hsnoc : A ++ [((p.1 + c, p.2.1, p.2.2) : ℕ × ℕ × ℕ)] ∈ W u)
    (hesc : ∀ B : TrioSeq, 2 ≤ B.length →
      ¬ L53.HasParentInBlock (shiftr01 c 0 B) →
      A ++ shiftr01 c 0 B ∈ W u) :
    ∀ B : TrioSeq, B ∈ W u' → (B ≠ [] → B.headD (0, 0, 0) = p) →
      A ++ shiftr01 c 0 B ∈ W u := by
  have hone : ∀ B : TrioSeq, B.length = 1 → (B ≠ [] → B.headD (0, 0, 0) = p) →
      A ++ shiftr01 c 0 B ∈ W u := by
    intro B h1 hd
    obtain ⟨q, hq⟩ := List.length_eq_one_iff.mp h1
    subst hq
    have hqp : q = p := by
      have := hd (by simp)
      simpa using this
    subst hqp
    have hsh : shiftr01 c 0 [q] = [((q.1 + c, q.2.1, q.2.2) : ℕ × ℕ × ℕ)] := by
      unfold shiftr01
      simp
    rw [hsh]
    exact hsnoc
  have hsub : W u' ⊆ {B : TrioSeq |
      (B ≠ [] → B.headD (0, 0, 0) = p) → A ++ shiftr01 c 0 B ∈ W u} := by
    refine A2' ?_
    rintro B (⟨hl, -⟩ | hop | ⟨m', hm', hd, hgr⟩) hdd
    · rcases Nat.eq_zero_or_pos B.length with h0 | hpos
      · have hnil : B = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        show A ++ shiftr01 c 0 ([] : TrioSeq) ∈ W u
        simpa using hA
      · exact hone B (by omega) hdd
    · show A ++ shiftr01 c 0 B ∈ W u
      rcases Nat.lt_or_ge B.length 2 with hsm | hbig
      · rcases Nat.eq_zero_or_pos B.length with h0 | hpos
        · have hnil : B = [] := List.length_eq_zero_iff.mp h0
          subst hnil
          simpa using hA
        · exact hone B (by omega) hdd
      · have hhead : ∀ m, 1 ≤ m → A ++ shiftr01 c 0 (B⟦m⟧) ∈ W u := by
          intro m hm
          refine hop m hm ?_
          intro _
          rw [oper_headD B (by omega) hm]
          exact hdd (by intro hc; rw [hc] at hbig; simp at hbig)
        by_cases hblk : L53.HasParentInBlock (shiftr01 c 0 B)
        · exact catBlock_step hbig hblk hhead
        · exact hesc B hbig hblk
    · show A ++ shiftr01 c 0 B ∈ W u
      rcases Nat.lt_or_ge B.length 2 with hsm | hbig
      · have hBne : B ≠ [] := by
          intro hc
          rw [hc] at hd
          exact not_domT_nil m' hd
        have h1 : 0 < B.length := List.length_pos_iff.mpr hBne
        exact hone B (by omega) hdd
      · have hop := aop_clause3_to_clause2 hbig hd hgr
        have hhead : ∀ m, 1 ≤ m → A ++ shiftr01 c 0 (B⟦m⟧) ∈ W u := by
          intro m hm
          refine hop m hm ?_
          intro _
          rw [oper_headD B (by omega) hm]
          exact hdd (by intro hc; rw [hc] at hbig; simp at hbig)
        by_cases hblk : L53.HasParentInBlock (shiftr01 c 0 B)
        · exact catBlock_step hbig hblk hhead
        · exact hesc B hbig hblk
  exact fun B hB hdd => hsub hB hdd

/-! ### 90.1 ⚠ §78.2 の自己訂正

> 「`hesc` は `|B| = 1` のとき任意の列の snoc になるので **`WSnoc` を含む**」

**これは `B` を `W u'` 全体で回したときの話だった。**
**派生の途中では先頭列が保たれる**（`oper_headD`）ので、**底は 1 つの決まった列**である。
⟹ **`WSnoc` は含まれない。§78.2 の判定は撤回する。** -/

/-! ## 91. ★★★★★★ 塔に当てる: **底は「ブロック `n` の根を 1 本足す」だけ** -/

theorem headD_eq_getD (l : TrioSeq) : l.headD (0, 0, 0) = l.getD 0 (0, 0, 0) := by
  cases l <;> rfl

open Classical in
theorem headD_Lift1 {X : TrioSeq} {c : ℕ} (hne : X ≠ []) :
    (Lift1 X c).headD (0, 0, 0)
      = ((entry X 0 0, entry X 1 0 + c, entry X 2 0) : ℕ × ℕ × ℕ) := by
  have h0 : 0 < X.length := List.length_pos_iff.mpr hne
  rw [headD_eq_getD, Lift1_getD h0, if_pos (le1_refl h0)]

open Classical in
/-- **★★★★★★ 塔の閉包は「塔にブロックの根を 1 本足す」＋「段内で孤児の塊を継ぐ」の 2 本。** -/
theorem mTowerClosed_of_escape_head {u : ℕ} {Q : TrioSeq} {d e : ℕ} (h2 : 2 ≤ Q.length)
    (hs : ∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j)
    (hblk : L53.HasParentInBlock Q)
    (hlift : ∀ s : ℕ, ∃ u' : ℕ, Lift1 Q s ∈ W u')
    (hbase : ∀ n : ℕ, mTower Q d e n ∈ W u →
      mTower Q d e n
        ++ [((entry Q 0 0 + d * n, entry Q 1 0 + e * n, entry Q 2 0) : ℕ × ℕ × ℕ)]
        ∈ W u)
    (hesc : ∀ (n : ℕ) (B : TrioSeq), 2 ≤ B.length →
      ¬ L53.HasParentInBlock (shiftr01 (d * n) 0 B) →
      mTower Q d e n ∈ W u → mTower Q d e n ++ shiftr01 (d * n) 0 B ∈ W u) :
    ∀ n, mTower Q d e n ∈ W u := by
  have hQne : Q ≠ [] := by intro hc; rw [hc] at h2; simp at h2
  intro n
  induction n with
  | zero => simpa using W_nil u
  | succ n ih =>
      refine mem_of_oper_mem (fun m hm => ?_)
      rw [oper_mTower' h2 hs hblk d e n m, mTower_step_shift]
      obtain ⟨u', hu'⟩ := hlift (e * n)
      have hQ2 : 2 ≤ (Lift1 Q (e * n)).length := by rw [Lift1_length]; exact h2
      have hLne : Lift1 Q (e * n) ≠ [] := by
        intro hc
        have hl : (Lift1 Q (e * n)).length = 0 := by rw [hc]; rfl
        rw [Lift1_length] at hl
        omega
      refine catBlock_of_escape_head
        (p := ((entry Q 0 0, entry Q 1 0 + e * n, entry Q 2 0) : ℕ × ℕ × ℕ))
        ih ?_ (fun B hB2 hnb => hesc n B hB2 hnb ih)
        ((Lift1 Q (e * n))⟦m⟧) (oper_mem_of_mem hQ2 hu' m hm) ?_
      · exact hbase n ih
      · intro _
        rw [oper_headD _ (by rw [Lift1_length]; omega) hm, headD_Lift1 hQne]

/-! ### 91.1 ⟹ 残差の最終形（A の側）

    **(A1) 底**: `mTower Q d e n ++ [ブロック `n` の根] ∈ W u`
        ＝ **`mTower Q d e (n+1)` の接頭辞**（`(n*|Q| + 1)` 列目まで）
    **(A2) 継ぎ**: 段内で孤児の塊 `B`（`|B| ≥ 2`）を継ぐ

**⟹ (A1) は「塔 ＋ 次のブロックの根 1 列」**という、いちばん小さい snoc である。
任意の列ではない ⟹ **`WSnoc` を経由しない。**

⚠ (A1) はそれでも自明ではない: `mTower Q d e (n+1) ∈ W u` から `Wset.W_take` で取れれば
無料だが、それはいま証明しようとしているもの（同じ `n` で循環）。**別の議論が要る。**

### 91.2 ⟹ B（`MTowerOrphan`）との関係

(A2) は「段内で孤児の塊を継ぐ」で、**B は「`Q` の末尾列が段内で孤児のときの塔」**。
**どちらも「孤児が土台の中で親を見つけるか」**という同じ問いである（§88.1）。
**⟹ A と B は (A1) を除いて同じ 1 点に集まった。** -/

/-! ## 92. ⛔ 自己訂正（grep 8-9 回目）: §86 / §87 は **`Wset.nextR_src_ge` の特殊化**

`Wset.nextR_src_ge`（`Wset.lean:2573`、**緑**）:

    `nextR T i q j1` ＋ `nextR (A ++ T) i y (A.length + j1)` ⟹ **`A.length ≤ y`**
    docstring:「**A prefix cannot supply a `nextR`-predecessor once the block itself has one**:
    the minimality clause of the inner predecessor rules it out.
    Unlike `nextR_src_in_T` this needs **no** anchoring hypothesis on `T`.」

**行 0・行 1・行 2 を一度に扱い、`T` に錨も要らない。私の §86（行 0）と §87（行 1・錐の中）は
どちらもこれの特殊化である。** 私は「ブロックの根の浅さ」「ブロックの根の行 1」という
**具体的な witness** を使って `T` 側の親の存在を作ったが、
**`nextR_src_ge` はその witness を引数に取る形で既に一般化されていた。**

    §86 … `T` ＝ ブロック `k` 以降、`j1` ＝ ブロック内の位置、
          `T` 側の親 ＝ **ブロック `k` の根**（`hasParent_zero_iff` で存在）
    §87 … 同じで行 1。`T` 側の親 ＝ 錐の中なら `Q` の `nextrel1` の親の像

⟹ **§86 / §87 は新しい内容を持たない。残す理由は「塔の言葉での具体形」だけ。**

### 92.1 ⟹ それでも残る本質

**`nextR_src_ge` は「`T` が自分の親を持つ」ことを要求する。**
⟹ **`T` の末尾列が `T` の中で孤児のときは何も言わない。**
**⟹ 残差（(A2) と B）はまさにそこ**であり、一般補題でも埋まらない。

**⟹ 私が §86-87 で「錐の外は別」と書いた但し書きは、
一般補題の射程の限界とちょうど一致していた。** 結論は変わらない。

### 92.2 ⚠ 規律（通算 8-9 回目）

**`nextrel` / `nextR` の「前置は親を供給できない」という形の補題を書く前に
`grep "nextR_src\|src_ge\|src_in_T"` を打つこと。**
今回は `W_flatMap_copies` を探していて**偶然** 3 行下に見つけた。
**探して見つけたのではない。** -/

/-! ## 93. ★★★★★★ 課題「行 2 の壁は作れるか」への 30 分の答え: **作れる。ただし ¬F2b だけ**

§87（行 1 の壁）と同じ骨で行 2 版が書ける。**極小性条項にブロック `k` の根を代入する。**
道具は `Lcone.gexp_entry2_mir`（`:436`、**緑・一般**、行 2 は鏡像で変わらない）。 -/

open Classical in
/-- **★★★★★ 行 2 の壁**: ブロック `k` の根の行 2（＝ `M` の根の行 2）が目標より
**狭義に小さい**なら、`nextrel2` はブロック外から入れない。 -/
theorem nextrel2_gexp_no_enter {M : TrioSeq} {Lb d0 d1 n k q a : ℕ}
    (hlen : 0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hk : k < n) (hq : q < Lb)
    (hrow2 : entry M 2 0 < entry M 2 (0 + q))
    (hbc : le1 (gexp M 0 Lb d0 d1 n) (0 + (k * Lb + 0)) (0 + (k * Lb + q)))
    (h : nextrel2 (gexp M 0 Lb d0 d1 n) a (0 + (k * Lb + q))) :
    k * Lb ≤ a := by
  by_contra hc
  have hmin := h.2.2.2.2.2 (0 + (k * Lb + 0)) ⟨by omega, hbc⟩
  rw [gexp_entry2_mir hlen hk hq d0 d1, gexp_entry2_mir hlen hk hLb d0 d1] at hmin
  have he : entry M 2 (0 + 0) = entry M 2 0 := rfl
  omega

/-! ### 93.1 ⛔ **前提 `hrow2` はちょうど ¬F2b。F2b には原理的に届きません**

    `hrow2 : entry M 2 0 < entry M 2 (0 + q)`   （根の行 2 が目標より狭義に小さい）
    **F2b   : `entry Q 2 (|Q|-1) ≤ entry Q 2 0`**（目標の行 2 が根以下）
    **⟹ 互いに否定。壁の射程と残差はちょうど排他。**

**なぜ強められないか（§76 が理由を持っている）:**

> **`mTower` は `Lift1` と `shiftr01 · 0` しか使わないので行 2 を動かさない。**

§87（行 1）は**ブロック `k` の根の行 1 が `+k*d1` される**ことで矛盾を出した。
**行 2 には `+k*d2` が付かない**（付ける操作が塔の定義に無い）
⟹ **`k` に依存する項が一切現れない ⟹ 比較は `M` の中の `entry M 2 0` vs `entry M 2 q` だけ**
⟹ **`hrow2` を落とすことはできない。**

### 93.2 ⚠ そして「道具が無い」のではなく **文が偽**です

R2 の (z5)（§R132）: **F2b のみの枝で 破れ 1,812 / 365,796（0.50%）。**
最小反例 `Q = (0,0,1)(1,1,0)(2,1,1)`, `d=2, e=2, n=2`（`Q ∈ W 1`）:

    `T = (0,0,1)(1,1,0)(2,1,1) | (2,2,1)(3,3,0)(4,3,1)`
    **末尾列 `(4,3,1)` の行 2 の親は index 1（第 0 ブロックの中）へ逃げる**

> **⟹ 「ブロック内で孤児 ⟹ 塔でも孤児」は F2b では実際に偽。**
> **⟹ 壁が作れないのは私の道具の限界ではなく、命題が成り立たないからです。**

### 93.3 ★ `z = 0` の断片では F2b は空（証明）

`srow Q (|Q|-1) = 2` ⟹ `1 ≤ entry Q 2 (|Q|-1)`（`L53.srow_two_row2_pos`、緑）。
F2b は `entry Q 2 (|Q|-1) ≤ entry Q 2 0` なので **`1 ≤ entry Q 2 0`**。
塔の場面では `Q = Lift1 ((0,v,z) :: R.dropLast) t` ⟹ `entry Q 2 0 = z` ⟹ **`z = 1`**。 -/

theorem f2b_forces_row2_root {Q : TrioSeq} (hsr : srow Q (Q.length - 1) = 2)
    (hf2b : entry Q 2 (Q.length - 1) ≤ entry Q 2 0) : 1 ≤ entry Q 2 0 := by
  have := L53.srow_two_row2_pos hsr
  omega

/-! ### 93.4 ⟹ 30 分の結論

    **行 1 の壁（§87）** … 作れる。`+k*d1` が矛盾を作る
    **行 0 の壁（§86）** … 作れる。ブロックの根の浅さが矛盾を作る
    **行 2 の壁（上）** … **`¬F2b` のときだけ作れる。F2b では命題が偽**

> **⟹ B の本丸（`z = 1` かつ F2b）は「孤児が塔で復活する」ことを認めた上で、
> それでも `mTower Q d e n ∈ W u` を示すしかありません。**
> **「復活しない」路線はこの枝では閉じています。**

⚠ **§86 / §87 / 上の 3 本はいずれも `Wset.nextR_src_ge`（`:2573`、緑）の特殊化**である（§92）。
**一般補題も「ブロックが自分の親を持つ」ことを要求するので、F2b（孤児）には同じく届かない。** -/

/-! ## 94. ★★★★★★ 塔の閉包を **「1 列ずつ足す」2 重帰納**に落とす（team-lead の案）

`catBlock` / `hesc` / リフト装備を全部使わない形。**外側は `n`、内側は「ブロック `n` の
何列目まで足したか」`j`。** 段は 1 列の snoc で、**列は完全に決まっている。** -/

/-- **★★★★★★ 塔の閉包 ＝ 1 列ずつの snoc（2 重帰納）。** -/
theorem mTowerClosed_of_snocStep {u : ℕ} {Q : TrioSeq} {d e : ℕ}
    (hstep : ∀ (n j : ℕ), j < Q.length →
      mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j ∈ W u →
      mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1) ∈ W u) :
    ∀ n, mTower Q d e n ∈ W u := by
  intro n
  induction n with
  | zero => simpa using W_nil u
  | succ n ih =>
      have key : ∀ j, j ≤ Q.length →
          mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j ∈ W u := by
        intro j
        induction j with
        | zero => intro _; simpa using ih
        | succ j ihj =>
            intro hj
            exact hstep n j (by omega) (ihj (by omega))
      have hfull := key Q.length le_rfl
      rw [List.take_of_length_le (by rw [Lift1_length, shiftr01_length])] at hfull
      rw [mTower_succ]
      exact hfull

open Classical in
/-- 足す列は完全に決まっている。 -/
theorem block_getD {Q : TrioSeq} {d e n j : ℕ} (hj : j < Q.length) :
    (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).getD j (0, 0, 0)
      = ((entry Q 0 j + d * n,
          entry Q 1 j + (if le1 Q 0 j then e * n else 0), entry Q 2 j) : ℕ × ℕ × ℕ) := by
  have hlt : j < (shiftr01 (d * n) 0 Q).length := by rw [shiftr01_length]; exact hj
  rw [Lift1_getD hlt, entry0_shiftr01 hj, entry1_shiftr01, entry2_shiftr01, le1_shiftr01]

/-! ### 94.1 ⟹ 何が良くなったか

    **`catBlock_of_escape'`（§82）** … `B ∈ W u'` に `A2'` を回す。リフト装備が要る
    **`catBlock_of_escape_head`（§90）** … 底が 1 列に確定。だが `A2'` は残る
    **`mTowerClosed_of_snocStep`（上）** … **`A2'` も装備も無い。素の 2 重帰納**

**段は「決まった 1 列の snoc」で、列は `block_getD` が明示する:**

    **`(entry Q 0 j + d*n, entry Q 1 j + [錐なら e*n], entry Q 2 j)`**

⟹ **`j = 0` が (A1)（ブロックの根）**、`j ≥ 1` がその続き。

### 94.2 ⚠ 段が易しくなったわけではない

**1 列の snoc は `WSnoc` の形である。** 無料なのは 2 つだけ:

    **`snoc_orphan_W`（§4、緑）** … 足した列が**孤児のまま**なら段によらず無料
    **`Wtower2.snoc_flat_root`（`:2208`）** … `srow = 0` かつ**親が根**なら無料

**⟹ 残るのは「足した列が土台の中に親を見つける（根以外）」場合**で、
**それは §88.1 / §91.2 と同じ 1 点である。**

**⟹ 形は最小になった（`A2'` も装備も消えた）が、難所は動いていない。**
**次に測るべきは「`j` ごとに、足した列が孤児か／親が根か／親が内部か」の 3 分割。** -/

/-! ## 95. ⚠ `j = 0`（ブロックの根を足す）は**無料の 2 枝のどちらにも入りません**

§94 の段を `j = 0` で見る。足す列は **ブロック `n` の根**

    `r = (entry Q 0 0 + d*n,  entry Q 1 0 + e*n,  entry Q 2 0)`

土台は `A = mTower Q d e n`。塔の場面では `Q = Lift1 ((0,v,z) :: R.dropLast) t` なので
`entry Q 0 0 = 0`、`entry Q 1 0 = v + t`、`entry Q 2 0 = z`。

### 95.1 `r` は**孤児になりません**（`snoc_orphan_W` が当たらない）

    ブロック `k` の根の行 0 は `entry Q 0 0 + d*k`（`k < n`）⟹ **`r` より狭義に浅い**
    ⟹ **行 0 の親は必ず存在する**（`Wset.hasParent_zero_iff`）

`z = 0` のとき `srow r = 1`（行 1 ＝ `v+t+e*n ≥ 1`、行 2 ＝ 0）で、
**ブロック `n-1` の根は行 1 が `v+t+e*(n-1) < v+t+e*n`** かつ `r` の行 0 祖先
⟹ **`Wset.hasParent_one_of` の前提が揃う ⟹ 行 1 の親も存在する。**

### 95.2 親は**根ではありません**（`snoc_flat_root` も当たらない）

`nextrel1` の極小性は「行 1 が `r` より小さい `le0` 祖先のうち**添字最大**のもの」を選ぶ。
**ブロック `n-1` の根（添字 `(n-1)*|Q|`）がその候補**なので、
**`n ≥ 2` では親の添字は `≥ (n-1)*|Q| ≥ |Q| > 0`** ⟹ **根ではない。**
（`snoc_flat_root` は `srow = 0` かつ親 = 根の両方を要求する。ここでは両方とも成り立たない。）

> **⟹ `j = 0` は無料の 2 枝のどちらにも入らない。残差 (iii) の中にある。**
> **⟹ 残差は「ブロック境界」に実在する。**（R2 の「`n` に依存しない ＝ ブロック境界 1 つの現象」
> という観察とも整合する。）

### 95.3 ⟹ 次に要る道具

`A ++ [r]` の展開は、**悪根がブロック `n-1` の根（またはその近く）**なので、
**`oper` は「ブロック `n-1` の根から `r` の直前まで」を複製する** ——
つまり **ブロック `n-1` の中身をもう 1 本作る**。

⟹ **`A ++ [r]` の展開は `mTower Q d e n` の最後のブロックを増やした形**になるはずで、
**`mTower Q d e (n+1)` の接頭辞と同じ族に留まる**可能性がある。
**そこが閉じれば `mem_of_oper_mem` で `j = 0` の段が落ちる。**

⚠ **これは設計の見立てであって証明ではない。** 悪根の位置（ブロック `n-1` の根か、
それとも `Q` の中のより浅い列か）は **`R` の末尾列が `R` の中で最浅かどうか**に依存し、
R2 の (n4) はそれが **27.5〜30.3% で偽**だと測っている。⟹ **2 通りある。** -/

/-! ## 96. R2 の (v) と (a2) を取り込む

### 96.1 ✅ (v): `gexp_cone_mir_zero` / `le1_mTower_block` の前提を **2 本削除**（実施ずみ）

R2 の導出をそのまま入れた（`hup` と `hd0pos` は `hr0` ＋ `hd0e` から出る）:

    `hup l hl0 hl1` … `l ≤ 0 + Lb` かつ `|M| = Lb + 1` ⟹ `l < |M|` ⟹ **`hr0 l`**
    `hd0pos`       … `hr0 (0+Lb)` ＋ `hd0e` ⟹ `entry M 0 0 < entry M 0 0 + d0` ⟹ **`0 < d0`**

⟹ **`gexp_cone_mir_zero` は 8 前提 → 6 前提、`le1_mTower_block` も同じ。**

### 96.2 ★ (a2): 「錐の外」の閉じた形は **`Lcone.le1_zero_iff` の否定そのもの**

R2 の閉じた形（「錐の外 ⟺ 行 1 の親鎖上に『行 1 が根以下』の列がある」）は、
**既存の `le1_zero_iff`（`Lcone:36`、緑）をそのまま否定した形**である。 -/

open Classical in
/-- **「錐の外」の閉じた形**（`Lcone.le1_zero_iff` の否定）。 -/
theorem not_le1_zero_iff {Q : TrioSeq}
    (hr : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    {q : ℕ} (hq : q < Q.length) :
    ¬ le1 Q 0 q ↔ ∃ y, Relation.ReflTransGen (nextrel0 Q) y q ∧ y ≠ 0 ∧
      entry Q 1 y ≤ entry Q 1 0 := by
  rw [le1_zero_iff hr hq]
  constructor
  · intro h
    by_contra hc
    refine h (fun y hy hy0 => ?_)
    by_contra hlt
    exact hc ⟨y, hy, hy0, by omega⟩
  · rintro ⟨y, hy, hy0, hle⟩ hall
    have := hall y hy hy0
    omega

/-! ### 96.3 ⟹ R2 の (G1)/(G2) は**証人の位置**で分けているだけ

    **(G1)** 証人が **`q` 自身**（`ReflTransGen` は反射的なので常に候補）
             ＝ `entry Q 1 q ≤ entry Q 1 0`
    **(G2)** 証人が **`q` より真に手前**（＝ 途中のブロッカー）

**⟹ `not_le1_zero_iff` の `∃ y` が両方を 1 本にまとめている。**
**R2 の「G1 と G2 を分けずに 1 本の帰納で扱える形がある」はこれのことである。**

⚠ R2 の実測「G2 が `|M|` とともに増える（0.0 / 5.0 / 9.2%）」は
**証人が `q` 自身でない場合が増える**ということで、**`∃ y` の形なら場合分けが要らない。**

### 96.4 ⚠ ただし B（F2b）には効きません

F2b は **`srow = 2` ∧ 錐の**中** ∧ 行 2 が根以下**である。
**「錐の外」の閉じた形は F2a 側の道具**であり、
**R2 の (z5) では F2a は破れ 0（933,768 件）＝ すでに無料の側**である。
⟹ **本丸（F2b）には別の道具が要る**（§93 のとおり）。 -/

/-! ## 97. F1 / F2a（「ブロック内で孤児 ⟹ 塔でも孤児」）の**足りない 1 文**

R2 の (z5) は F1 と F2a で破れ 0（合計 130 万件超）。**機構を定義から詰めた。**

### 97.1 F1（`srow = 1` ∧ `entry Q 1 (L-1) ≤ entry Q 1 0`、`L = |Q|`）

**まず `F1 ⟹ 末尾列は `Q` の錐の外`**（`Lcone.le1_entry1_lt`、緑）:
`le1 Q 0 (L-1)` と `L-1 ≠ 0` なら `entry Q 1 0 < entry Q 1 (L-1)` で F1 と矛盾。
⟹ **塔の末尾列の行 1 はリフトされない**: `entry T 1 last = entry Q 1 (L-1)`。

`nextrel1 T a last` を仮定して `a` を追う:

    `a` がブロック `k` の**根**            … `entry T 1 a = entry Q 1 0 + e*k ≥ entry Q 1 0`
                                          ≥ `entry Q 1 (L-1)` ⟹ **`<` にならない ⟹ 不可**
    `a` が**錐の中**（`q_a ≥ 1`）          … `entry T 1 a = entry Q 1 q_a + e*k > entry Q 1 0`
                                          ⟹ 同じく**不可**
    `a` が**錐の外**（`q_a ≥ 1`）          … `entry T 1 a = entry Q 1 q_a`（リフト無し）
                                          ⟹ **`entry Q 1 q_a < entry Q 1 (L-1)` なら可能**

**ブロック `n-1` の中では起きない**: `Q` の末尾列が行 1 で孤児 ⟹
`Wset.hasParent_one_of` の対偶より **`Q` の `le0` 祖先はすべて `entry Q 1 y ≥ entry Q 1 (L-1)`**。
像も `+ (錐なら e*(n-1))` で減らない ⟹ **同ブロック内は塞がっている。**

> **⟹ 足りないのは 1 文だけ:**
> **「ブロック `n-1` の根の（塔の中での）行 0 祖先は、すべて `entry T 1 ≥ entry Q 1 (L-1)`」**

⚠ 極小性条項は塞ぎません: `j :=` ブロック `n-1` の根 を入れると
`entry T 1 last ≤ entry Q 1 0 + e*(n-1)` が要りますが、**F1 のもとでこれは自動的に真**
（`entry Q 1 (L-1) ≤ entry Q 1 0`）。**⟹ §87 の骨はここでは使えない。**

### 97.2 F2a（`srow = 2` ∧ 錐の外）

同じ形。`nextrel2 T y last` は `le1 T y last` を要求し、`le1` の最後の 1 歩は `nextrel1` なので、
**97.1 の解析がそのまま前段になる。**

### 97.3 ⟹ R2 に測ってほしい形（教訓 45: 反例の形を先に書く）

> **「ブロック `k` の根の行 0 祖先（塔の中、根 `0` を除く）で、
> `entry T 1 < entry Q 1 (|Q|-1)` のものがあるか。」**

    **あるなら** … F1 の破れの候補。R2 の 376,164 件で 0 だったのだから**無いはず**
    **無いなら** … その理由が F1 / F2a の機構。**それを証明すればよい**

⚠ **私の予想**: 祖先は「ブロックの根」か「錐の外の列」で、
**前者は `entry Q 1 0 + e*k ≥ entry Q 1 0 ≥ entry Q 1 (L-1)`（F1 より）で塞がる**。
**後者（錐の外の列が前のブロックから行 0 祖先になる）が起きるかどうかが鍵。**
**⚠ これは見立てであって証明ではない。** -/

/-! ## 98. ★★★★★★ §97 の「足りない 1 文」は **§85 ＋ `le1_zero_iff` から出ます**

§97 で必要だと特定したのは

> **「ブロック `k` の根の（塔の中での）行 0 祖先（根 `0` を除く）は、すべて 行 1 が `entry M 1 0` より上」**

**これは既存の 2 本の合成である:**

    **(1) `le1 T 0 (ブロック `k` の根)` は真**（§84 の `q = 0` の場合 ＋ `le1_refl`）
    **(2) `Lcone.le1_zero_iff`**（緑）… `le1 T 0 j` ⟺ `j` の非根の行 0 祖先が全部 行 1 > 根

**⟹ (1) を (2) に入れるだけ。** -/

open Classical in
/-- **ブロック `k` の根は必ず塔の根の錐に入る。** -/
theorem gexp_blockRoot_cone {M : TrioSeq} {Lb d0 d1 n k : ℕ}
    (hlen : 0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hk : k < n) (hd1pos : 0 < d1)
    (hd0e : entry M 0 (0 + Lb) = entry M 0 0 + d0)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + Lb)) :
    le1 (gexp M 0 Lb d0 d1 n) 0 (0 + (k * Lb + 0)) := by
  rw [gexp_cone_mir_zero hlen hLb hk hLb hd1pos hd0e hr0 hlp]
  exact le1_refl (by omega)

open Classical in
/-- **★★★★★★ §97 の足りない 1 文**: ブロックの根の行 0 祖先は全部、塔の根より行 1 が上。 -/
theorem gexp_blockRoot_anc {M : TrioSeq} {Lb d0 d1 n k : ℕ}
    (hlen : 0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hk : k < n) (hd1pos : 0 < d1)
    (hd0e : entry M 0 (0 + Lb) = entry M 0 0 + d0)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + Lb)) :
    ∀ y, Relation.ReflTransGen (nextrel0 (gexp M 0 Lb d0 d1 n)) y (0 + (k * Lb + 0)) →
      y ≠ 0 → entry M 1 0 < entry (gexp M 0 Lb d0 d1 n) 1 y := by
  have hn : 0 < n := by omega
  have hd0pos : 0 < d0 := by
    have h := hr0 (0 + Lb) (by omega) (by omega)
    rw [hd0e] at h
    omega
  have hrX := gexp_root_shallow_zero (d1 := d1) hlen hn hLb hd0pos hr0
  have hbnd : k * Lb + 0 < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hplt : 0 + (k * Lb + 0) < (gexp M 0 Lb d0 d1 n).length := by
    rw [gexp_length hlen]; omega
  have h10 : entry (gexp M 0 Lb d0 d1 n) 1 0 = entry M 1 0 :=
    gexp_entry_root hlen hn hLb
  have hall := (le1_zero_iff hrX hplt).mp
    (gexp_blockRoot_cone hlen hLb hk hd1pos hd0e hr0 hlp)
  intro y hy hy0
  have hres := hall y hy hy0
  rwa [h10] at hres

/-! ### 98.1 ⟹ F1 の証明の骨（残るは行 0 の鎖のブロック分解だけ）

F1（`srow Q (L-1) = 1` ∧ `entry Q 1 (L-1) ≤ entry Q 1 0`、`Q = M.dropLast`, `L = Lb`）で
`nextrel1 T a last`（`last` ＝ ブロック `n-1` の最終列）を仮定する。§97 より
**`entry T 1 last = entry M 1 (Lb-1)`**（錐の外なのでリフト無し）。

    **`a` がブロック `n-1` の外** … §86（行 0 の壁）を繰り返すと `a` は
        **ブロック `n-1` の根の行 0 祖先** ⟹ **上の `gexp_blockRoot_anc`** で
        **`entry T 1 a > entry M 1 0 ≥ entry M 1 (Lb-1)`（F1）** ⟹ `entry T 1 a < entry T 1 last` と**矛盾**
    **`a` がブロック `n-1` の中** … `Gtrans.gexp_chain_inversion`（緑）で `a` は像
        ⟹ `le0 M q_a (Lb-1)` かつ `entry T 1 a ≥ entry M 1 q_a`
        ⟹ `Q` の末尾列が行 1 で孤児（`Wset.hasParent_one_of` の対偶）より
           **`entry M 1 q_a ≥ entry M 1 (Lb-1)`** ⟹ 同じく**矛盾**

> **⟹ 残るのは「ブロック外の行 0 祖先は、ブロックの根の行 0 祖先である」1 本だけ。**
> **それは §86（`nextrel0_gexp_no_skip`）を鎖に沿って繰り返した形である。**

**⟹ F1 は道具がすべて揃った。F2a も `nextrel2` が `le1` を要求し、
`le1` の最後の 1 歩が `nextrel1` なので同じ骨で通るはず。**

⚠ **まだ証明ではない。** 上の「繰り返し」を Lean で書くのが次の作業である。 -/

/-! ## 99. ★★★★★★ §86 を鎖に沿って繰り返す: **ブロック外の祖先は必ずブロックの根を通る** -/

theorem gexp_anc_through_root {M : TrioSeq} {Lb d0 d1 n k : ℕ}
    (hlen : 0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hk : k < n)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l) :
    ∀ q, q < Lb → ∀ y,
      Relation.ReflTransGen (nextrel0 (gexp M 0 Lb d0 d1 n)) y (0 + (k * Lb + q)) →
      y < k * Lb →
      Relation.ReflTransGen (nextrel0 (gexp M 0 Lb d0 d1 n)) y (0 + (k * Lb + 0)) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq y hy hylt
    rcases Nat.eq_zero_or_pos q with rfl | hqpos
    · exact hy
    · rcases hy.cases_tail with heq | ⟨c, hc1, hc2⟩
      · omega
      · have hcge : k * Lb ≤ c :=
          nextrel0_gexp_no_skip hlen hLb hk hq hqpos hr0 hc2
        have hclt : c < 0 + (k * Lb + q) := nextrel0_index_less hc2
        obtain ⟨q', hq'⟩ : ∃ q', c = 0 + (k * Lb + q') := ⟨c - k * Lb, by omega⟩
        subst hq'
        exact ih q' (by omega) (by omega) y hc1 hylt

/-! ### 99.1 ⟹ §98.1 の骨の「ブロック外」の枝が閉じました

    §86 `nextrel0_gexp_no_skip`  … 1 歩
    **§99 `gexp_anc_through_root` … 鎖全体**（`q` の強帰納）
    **§98 `gexp_blockRoot_anc`   … ブロックの根の祖先は行 1 が塔の根より上**

**⟹ 合成すると: ブロック `k` の位置 `q ≥ 1` の行 0 祖先 `y` がブロック外なら
`entry T 1 y > entry M 1 0`。** -/

open Classical in
/-- **★★★★★★ ブロック外の行 0 祖先は、行 1 が塔の根より上。** -/
theorem gexp_outer_anc_row1 {M : TrioSeq} {Lb d0 d1 n k q : ℕ}
    (hlen : 0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hk : k < n) (hq : q < Lb)
    (hd1pos : 0 < d1)
    (hd0e : entry M 0 (0 + Lb) = entry M 0 0 + d0)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + Lb)) :
    ∀ y, Relation.ReflTransGen (nextrel0 (gexp M 0 Lb d0 d1 n)) y (0 + (k * Lb + q)) →
      y < k * Lb → y ≠ 0 →
      entry M 1 0 < entry (gexp M 0 Lb d0 d1 n) 1 y := by
  intro y hy hylt hy0
  exact gexp_blockRoot_anc hlen hLb hk hd1pos hd0e hr0 hlp y
    (gexp_anc_through_root hlen hLb hk hr0 q hq y hy hylt) hy0

/-! ### 99.2 ⟹ 残るのは「ブロック内」の枝だけ

§98.1 の骨のうち **「`a` がブロック `n-1` の外」の枝が上で閉じました。**
残るのは **「`a` がブロック `n-1` の中」** で、そこは

    `Gtrans.gexp_chain_inversion`（緑）で `a` は像 ⟹ `le0 M q_a (Lb-1)`
    `Wset.hasParent_one_of` の対偶 ⟹ `entry M 1 q_a ≥ entry M 1 (Lb-1)`
    `entry T 1 a ≥ entry M 1 q_a`（`Lift1` は行 1 を減らさない）

の 3 本で、**全部既存の緑**です。**⟹ F1 は道具が完全に揃いました。** -/

/-! ## 100. ★★★★★★★ **F1 は定理**: ブロック内で行 1 の孤児なら、塔でも行 1 の孤児

R2 の (z5) の F1（376,164 件・破れ 0）を Lean にする。§98-99 で「ブロック外」、
`Gtrans.gexp_chain_inversion` ＋ `Wset.hasParent_one_of` の対偶で「ブロック内」。 -/

open Classical in
theorem gexp_last_orphan_row1 {M : TrioSeq} {Lb d0 d1 n : ℕ}
    (hlen : 0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hn : 0 < n) (hLb1 : 1 < Lb)
    (hd1pos : 0 < d1)
    (hd0e : entry M 0 (0 + Lb) = entry M 0 0 + d0)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + Lb))
    (hf1 : entry M 1 (0 + (Lb - 1)) ≤ entry M 1 0)
    (horph : ¬ hasParent M 1 (0 + (Lb - 1))) :
    ¬ hasParent (gexp M 0 Lb d0 d1 n) 1
      (0 + ((n - 1) * Lb + (Lb - 1))) := by
  have hup : ∀ l, 0 < l → l ≤ 0 + Lb → entry M 0 0 < entry M 0 l :=
    fun l hl0 hl1 => hr0 l hl0 (by omega)
  have hkn : n - 1 < n := by omega
  have hqL : Lb - 1 < Lb := by omega
  -- 末尾列は `M` の錐の外（F1 ＋ `le1_entry1_lt`）
  have hout : ¬ le1 M 0 (0 + (Lb - 1)) := by
    intro hc
    have := le1_entry1_lt hc (show (0 : ℕ) ≠ 0 + (Lb - 1) from by omega)
    omega
  have hlast1 : entry (gexp M 0 Lb d0 d1 n) 1 (0 + ((n - 1) * Lb + (Lb - 1)))
      = entry M 1 (0 + (Lb - 1)) := by
    rw [gexp_entry1_mir hlen hkn hqL, if_neg hout]
    omega
  rintro ⟨a, ha, -⟩
  have hnr : nextrel1 (gexp M 0 Lb d0 d1 n) a (0 + ((n - 1) * Lb + (Lb - 1))) := by
    unfold nextR at ha
    rw [if_neg (by omega), if_pos rfl] at ha
    exact ha
  have hlt := hnr.2.2.2.1
  rw [hlast1] at hlt
  have hle0 := hnr.2.2.2.2.1
  by_cases ha0 : a = 0
  · subst ha0
    have h10 : entry (gexp M 0 Lb d0 d1 n) 1 0 = entry M 1 0 :=
      gexp_entry_root hlen hn hLb
    rw [h10] at hlt
    omega
  · by_cases hain : (n - 1) * Lb ≤ a
    · -- ブロック `n-1` の中
      obtain ⟨qa, hqa⟩ : ∃ qa, a = 0 + ((n - 1) * Lb + qa) :=
        ⟨a - (n - 1) * Lb, by omega⟩
      have haltp : a < 0 + ((n - 1) * Lb + (Lb - 1)) := hnr.2.2.1
      have hqalt : qa < Lb - 1 := by omega
      subst hqa
      have hent : entry M 1 (0 + qa) ≤
          entry (gexp M 0 Lb d0 d1 n) 1 (0 + ((n - 1) * Lb + qa)) := by
        rw [gexp_entry1_mir hlen hkn (by omega)]
        split_ifs <;> omega
      obtain ⟨k', q', hk', hq', hxe, hcase⟩ :=
        gexp_chain_inversion hlen hkn hqL hup hd0e _ hle0.2.2 (Nat.zero_le _)
      have hk'e : k' = n - 1 := by
        rcases Nat.lt_or_ge k' (n - 1) with h | h
        · exfalso
          have : k' * Lb + Lb ≤ (n - 1) * Lb := by
            have h1 : (k' + 1) * Lb ≤ (n - 1) * Lb := Nat.mul_le_mul_right _ (by omega)
            have h2 : (k' + 1) * Lb = k' * Lb + Lb := Nat.succ_mul k' Lb
            omega
          omega
        · omega
      subst hk'e
      have hq'e : q' = qa := by omega
      have hM : Relation.ReflTransGen (nextrel0 M) (0 + qa) (0 + (Lb - 1)) := by
        rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
        · rw [hq'e] at h; exact h
        · omega
      exact horph (hasParent_one_of (b := 0 + (Lb - 1)) (k := 0 + qa)
        (by omega) (by omega) ⟨by omega, by omega, hM⟩ (by omega))
    · -- ブロック `n-1` の外
      have := gexp_outer_anc_row1 hlen hLb hkn hqL hd1pos hd0e hr0 hlp a
        hle0.2.2 (by omega) ha0
      omega

/-! ### 100.1 ⟹ R2 の (z5) の F1 が定理になりました

    R2 の実測 **376,164 件・破れ 0** ⟹ **`gexp_last_orphan_row1`（上、緑）**

**⟹ `oper_eq_pred_of_noParent`（`Decrease:37`）と合わせると、
F1 の場面では `T⟦m⟧ = T.dropLast` ＝ 長さの帰納だけで B が閉じます。**

⚠ **F2a（`srow = 2` ∧ 錐の外）は `nextrel2` 版が要ります。**
`nextrel2` は `le1` を要求し、`le1` の最後の 1 歩が `nextrel1` なので**同じ骨**ですが、
**`le1` の鎖をたどる分だけ余分な作業があります。** -/

/-! ## 101. ⚠ `j = 0` の段の悪根の位置: **`≥ (n-1)*|Q|` は出る。`= (n-1)*|Q|` は 7 割**

### 101.1 ⛔ team-lead の `j0 = (n-1)*|Q|` は**私の §95 の読み過ぎ**です

§95 で私が示したのは **`j0 ≥ (n-1)*|Q|`（＝ 根ではない）**であって、
**等号ではありません。** 等号が成り立つのは「ブロック `n-1` の中に `r` より浅い列が
根以外に無い」ときだけです。

`r` の行 0 は `entry Q 0 0 + d*n`、ブロック `n-1` の列は `entry Q 0 q + d*(n-1)` なので

    **ブロック `n-1` の中の `q` が `r` の行 0 の親の候補 ⟺ `entry Q 0 q < entry Q 0 0 + d`**

塔の場面では `entry Q 0 0 = 0`、`d = entry R 0 (|R|-1)`、`entry Q 0 q = entry R 0 (q-1)` なので

    **⟺ `entry R 0 (q-1) < entry R 0 (|R|-1)` ＝「`R` の末尾列が `R` の中で最浅でない」**

**⟹ R2 の (n4)「`d` が最小でない 27.5〜30.3%」が、まさにその割合です。**
**⟹ `j0 = (n-1)*|Q|`（＝ `Lb = |Q|`）は 7 割。3 割では `j0` はブロック `n-1` の内部で、
`Lb < |Q|`（写されるのはブロック `n-1` の**接尾辞**）になります。**

### 101.2 ★ ただし `j0 ≥ (n-1)*|Q|` は既存の緑で出ます（`Wset.nextR_src_ge`）

**§95 の手計算は要りません。** `M = A ++ T`（`A` ＝ ブロック 0..n-2、`T` ＝ ブロック `n-1` ＋ `[r]`）
と分けて、**`T` が自分の中に親を持てば**、`nextR_src_ge` が**前置は親を供給できない**と言う。 -/

theorem parent_ge_of_inner {A T : TrioSeq} {i y : ℕ} (hTne : T ≠ [])
    (hq : hasParent T i (T.length - 1))
    (hy : nextR (A ++ T) i y ((A ++ T).length - 1)) : A.length ≤ y := by
  have hTlen : 0 < T.length := List.length_pos_iff.mpr hTne
  obtain ⟨q, hqn, -⟩ := hq
  have hidx : (A ++ T).length - 1 = A.length + (T.length - 1) := by
    rw [List.length_append]; omega
  rw [hidx] at hy
  exact nextR_src_ge hqn hy

/-! ### 101.3 ⟹ 適用の形（`z = 0`）

`T = ブロック `n-1` ++ [r]` は **`T` の根（ブロック `n-1` の根）が狭義に最浅**である
（他の列は `entry Q 0 q + d*(n-1)` で根より深く、`r` は `+d*n` で `d ≥ 1` より深い）
⟹ **`le0_zero_of_shallow`（§79、緑）で `le0 T 0 (|T|-1)` が無条件**。

そして `z = 0` なら `srow r = 1`（行 1 ＝ `entry Q 1 0 + e*n ≥ 1`、行 2 ＝ 0）で

    `entry T 1 0 = entry Q 1 0 + e*(n-1)` < `entry Q 1 0 + e*n = entry T 1 (|T|-1)`（`e ≥ 1`）

⟹ **`Wset.hasParent_one_of` の前提が揃う ⟹ `hasParent T 1 (|T|-1)`**
⟹ **`parent_ge_of_inner` で悪根は `≥ |A| = (n-1)*|Q|`。**

### 101.4 ⟹ ⟹ 展開の形（`oper_eq_gexp_gen` を `j0 ≥ (n-1)*|Q|` で読む）

    `hlen : j0 + Lb + 1 = |M| = n*|Q| + 1` ⟹ **`Lb = n*|Q| − j0 ≤ |Q|`**
    **`M.take j0` ⊇ `mTower Q d e (n-1)`**（`j0 ≥ (n-1)*|Q|` より）

⟹ **写されるのはブロック `n-1` の（接尾辞を含む）中だけ。前半 `n-1` ブロックは触られません。**

⚠ **`d1` について**: `z = 0` なら `srow r = 1` ⟹ `1 < 1` は偽 ⟹ **`d1 = 0`**
⟹ **写しは行 0 だけずらす形** ⟹ team-lead の読みどおり **`shTower` の領域**。
⚠ **`z = 1` では `srow r = 2` になりうる**（`entry Q 2 0 = z = 1 > 0`）⟹ **`d1 = e` の側**。

⚠ **これは設計であって証明ではありません。** `Lb` と `M.take j0` の具体形は
`j0` が「ブロック `n-1` のどこか」に依存するので、**`Lb = |Q|` を仮定して書くと
3 割で偽の文になります**（§101.1）。**team-lead の計算の 1 か所だけが読み過ぎでした。** -/

/-! ## 102. ★★★★★★ **F1 は最終列に限りません**（任意の `(k, q)` へ一般化）

§100 は `k = n-1`, `q = Lb-1` に特殊化していたが、**証明はどこもそれを使っていない。**
一般化すると **§94 の `j ≥ 1` の段にそのまま当たる。** -/

open Classical in
theorem gexp_orphan_row1 {M : TrioSeq} {Lb d0 d1 n k q : ℕ}
    (hlen : 0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hn : 0 < n)
    (hk : k < n) (hq : q < Lb) (hq1 : 0 < q)
    (hd1pos : 0 < d1)
    (hd0e : entry M 0 (0 + Lb) = entry M 0 0 + d0)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + Lb))
    (hf1 : entry M 1 (0 + q) ≤ entry M 1 0)
    (horph : ¬ hasParent M 1 (0 + q)) :
    ¬ hasParent (gexp M 0 Lb d0 d1 n) 1 (0 + (k * Lb + q)) := by
  have hup : ∀ l, 0 < l → l ≤ 0 + Lb → entry M 0 0 < entry M 0 l :=
    fun l hl0 hl1 => hr0 l hl0 (by omega)
  have hout : ¬ le1 M 0 (0 + q) := by
    intro hc
    have := le1_entry1_lt hc (show (0 : ℕ) ≠ 0 + q from by omega)
    omega
  have hlast1 : entry (gexp M 0 Lb d0 d1 n) 1 (0 + (k * Lb + q))
      = entry M 1 (0 + q) := by
    rw [gexp_entry1_mir hlen hk hq, if_neg hout]
    omega
  rintro ⟨a, ha, -⟩
  have hnr : nextrel1 (gexp M 0 Lb d0 d1 n) a (0 + (k * Lb + q)) := by
    unfold nextR at ha
    rw [if_neg (by omega), if_pos rfl] at ha
    exact ha
  have hlt := hnr.2.2.2.1
  rw [hlast1] at hlt
  have hle0 := hnr.2.2.2.2.1
  by_cases ha0 : a = 0
  · subst ha0
    have h10 : entry (gexp M 0 Lb d0 d1 n) 1 0 = entry M 1 0 :=
      gexp_entry_root hlen hn hLb
    rw [h10] at hlt
    omega
  · by_cases hain : k * Lb ≤ a
    · obtain ⟨qa, hqa⟩ : ∃ qa, a = 0 + (k * Lb + qa) := ⟨a - k * Lb, by omega⟩
      have haltp : a < 0 + (k * Lb + q) := hnr.2.2.1
      have hqalt : qa < q := by omega
      subst hqa
      have hent : entry M 1 (0 + qa) ≤
          entry (gexp M 0 Lb d0 d1 n) 1 (0 + (k * Lb + qa)) := by
        rw [gexp_entry1_mir hlen hk (by omega)]
        split_ifs <;> omega
      obtain ⟨k', q', hk', hq', hxe, hcase⟩ :=
        gexp_chain_inversion hlen hk hq hup hd0e _ hle0.2.2 (Nat.zero_le _)
      have hk'e : k' = k := by
        rcases Nat.lt_or_ge k' k with h | h
        · exfalso
          have : k' * Lb + Lb ≤ k * Lb := by
            have h1 : (k' + 1) * Lb ≤ k * Lb := Nat.mul_le_mul_right _ (by omega)
            have h2 : (k' + 1) * Lb = k' * Lb + Lb := Nat.succ_mul k' Lb
            omega
          omega
        · omega
      subst hk'e
      have hq'e : q' = qa := by omega
      have hM : Relation.ReflTransGen (nextrel0 M) (0 + qa) (0 + q) := by
        rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
        · rw [hq'e] at h; exact h
        · omega
      exact horph (hasParent_one_of (b := 0 + q) (k := 0 + qa)
        (by omega) (by omega) ⟨by omega, by omega, hM⟩ (by omega))
    · have := gexp_outer_anc_row1 hlen hLb hk hq hd1pos hd0e hr0 hlp a
        hle0.2.2 (by omega) ha0
      omega

/-! ### 102.1 ⟹ §94 の `j ≥ 1` の段への含意（team-lead の 30 分課題）

足す列は **`(block n)[j]` ＝ `Q` の第 `j` 列の像**（`block_getD`、§94）。

    **`Q` の第 `j` 列が `Q` の中で親を持つ** ⟹ その親の添字 `p < j`
      ⟹ **像は土台 `mTower Q d e n ++ (block n).take j` の中にある**
      ⟹ **足した列は親を持つ ⟹ 残差 (iii)。無料ではない**
    **`Q` の第 `j` 列が `Q` の中で孤児**（行 1）かつ **行 1 が根以下**
      ⟹ **上の `gexp_orphan_row1` が `k = n`, `q = j` でそのまま当たる**
      ⟹ **塔でも孤児 ⟹ `snoc_orphan_W` で無料**

> **⛔ team-lead の見立て（「`j ≥ 1` は `Q` の親関係を持ち上げるだけ」）は正しいが、
> 「だから易しい」は逆である。持ち上がった親は**土台の中**にあるので、
> **`j ≥ 1` は `Q` の第 `j` 列が親を持つたびに残差 (iii) に入る。**

⚠ **`j = 0` だけが特別なのではありません。`Q` のどの列も、親を持てば残差です。**
**無料なのは「`Q` の中で孤児で、かつ行 1 が根以下」の列だけ。**

### 102.2 ⟹ 残差の正しい姿

    **無料** … `Q` の第 `j` 列が行 1 の孤児 ∧ 行 1 が根以下 ⟹ `gexp_orphan_row1`（上、緑）
    **残差** … それ以外の `j` 全部（`j = 0` を含む）

**⟹ 残差は「ブロック境界」だけではなく、`Q` の親を持つ全部の列です。**
**§95 の「`j = 0` は残差」は正しいが、`j = 0` に**限らない**。 -/

/-! ## 103. F2a: **`a` は必ず錐の外**。そして残る穴は R2 の **G2** です

### 103.1 ★ 錐は `nextrel1` の鎖に沿って**下向きに閉じている** -/

theorem le1_zero_trans {T : TrioSeq} {a b : ℕ} (ha : le1 T 0 a)
    (hab : Relation.ReflTransGen (nextrel1 T) a b) (hb : b < T.length) : le1 T 0 b :=
  ⟨ha.1, hb, ha.2.2.trans hab⟩

/-- **目標が錐の外なら、`le1` の祖先も全部錐の外。** -/
theorem not_le1_zero_src {T : TrioSeq} {a b : ℕ} (hab : le1 T a b)
    (hnb : ¬ le1 T 0 b) : ¬ le1 T 0 a :=
  fun ha => hnb (le1_zero_trans ha hab.2.2 hab.2.1)

/-! ### 103.2 ⟹ F2a の場面での帰結

F2a は **`last` が `M` の錐の外**なので、§85（`le1_mTower_block`）より
**`¬ le1 T 0 last`**。`nextrel2 T a last` は `le1 T a last` を要求するので、上より

> **`a` も、`a` から `last` までの鎖の全ノードも、塔の根の錐の外。**

⟹ §85 でそれぞれの**ブロック内の位置も `M` の錐の外**である。

### 103.3 ⟹ 同じブロックの中なら閉じます

塔を `A ++ (ブロック `n-1`)` と分けると（`mTower_succ`）、
**`Wset.le1_append_right`** が `le1 T (|A|+i) (|A|+j) ↔ le1 (ブロック) i j` を与え、
**`le1_block`（§60、緑）** がそれを `le1 M i j` に直す。
⟹ `a` がブロック `n-1` の中なら **`le1 M q_a q_last`** ⟹
**`M` の末尾列が行 2 の孤児**（F2a の前提）より `entry M 2 q_a ≥ entry M 2 q_last`
⟹ `nextrel2` の `entry T 2 a < entry T 2 last` と**矛盾**。

### 103.4 ⛔ 残る穴: `a` が**前のブロック**にある場合

鎖はどこかでブロック境界を越える: `nextrel1 T c b`（`c` が前、`b` が後ろのブロック）。

    §87 は **`b` が錐の中**のときだけ止める。**103.2 より鎖は全部錐の外** ⟹ **§87 は効かない**
    極小性（`j :=` `b` のブロックの根）… `entry T 1 b ≤ entry M 1 0 + e*k_b`
      `b` は錐の外 ⟹ `entry T 1 b = entry M 1 q_b` ⟹ **`entry M 1 q_b ≤ entry M 1 0 + e*k_b`**
    `nextrel1` の `entry T 1 c < entry T 1 b` ＋ **§98/§99**（`c` はブロック外 ⟹ `entry T 1 c > entry M 1 0`）
      ⟹ **`entry M 1 0 < entry M 1 q_b`**

> **⟹ 越えるには `b` が「錐の外なのに行 1 が根より上」＝ R2 の **G2** でなければならない。**

### 103.5 ⚠⚠ ⟹ **R2 の F2a「破れ 0 / 933,768」は箱の産物の疑いがあります**

R2 の (a2) の実測（§R133）:

    **G2（行 1 は根より上なのに錐の外）… `|M|` = 3 / 4 / 5 で 0.0% / 5.0% / 9.2%（増加中）**
    R2 自身が「**9.2% を上限として引用しないこと。伸ばすと増えています**」と書いている

**⟹ F2a の反例は G2 の列を通らなければ作れない。`|M|` が小さい箱には G2 がほとんど無い。**
**⟹ `|M|` を 6, 7 まで伸ばして測り直す必要があります**（教訓 21 / 27 / 45）。

> **⚠ 反例の形（先に書きます）: 「`srow=2` ∧ `last` が錐の外 ∧ `M` の末尾列が行 2 の孤児」の場面で、
> **`le1` の鎖がブロック境界を G2 の列で越え、その先に `entry M 2 < entry M 2 q_last` の列がある」。**
> **その形が母集団に何件入っているかを先に数えてください。0 件なら「破れ 0」は空虚です。**

⚠ **これは `hblk`（§88.2）と同じ形の指摘です。今日 2 回目。**
**どちらも「反例が成立するには箱の端でしか出ない特徴が要る」という形です。** -/

/-! ## 104. ★★★★★ 「土台に親を持つ列を足す」: **`j = 0` は特別。`j ≥ 1` は前半に触らない**

team-lead の問い「`parent_ge_of_inner` の前提（`T` が自分の中に親を持つ）が
`j ≥ 1` でも成り立つか」に答える。**答えは「`j ≥ 1` では成り立つ。`j = 0` では成り立たない」。**

### 104.1 ⟹ 分け方が違います

§94 の段で足す列は `(block n)[j]`。**土台と足す列を `A ++ T` に分けるとき:**

    **`j = 0`** … `T = [(block n)[0]]` は **1 列**。1 列は自分の中に親を持てない
                 （`not_hasParentInBlock_of_short`、§78）
                 ⟹ **`T` を「ブロック `n-1` ＋ その列」に取り直すしかない**（§101 でそうした）
                 ⟹ **`j = 0` は本当に特別。ブロック境界をまたぐ**
    **`j ≥ 1`** … **`T = (block n).take (j+1)`** が取れる。**`|T| = j+1 ≥ 2`**
                 ⟹ `Q[j]` が `Q` の中に親を持てば、その像が `T` の中にある
                 ⟹ **`L53.HasParentInBlock T` が成り立つ**

> **⟹ `j ≥ 1` では `A = mTower Q d e n`（ブロック `n` より前**全部**）が土台に取れて、
> `L53.comm_of_hasParentInBlock` が「前半は触られない」を与える。**
> **⟹ `oper_eq_gexp_gen` を持ち出す必要はありません。** -/

open Classical in
/-- **★★★★★ `j ≥ 1`: 展開はブロック `n` の接頭辞の中だけで起きる。** -/
theorem oper_tower_blockPrefix {Q : TrioSeq} {d e n j m : ℕ} (hj : 1 ≤ j)
    (hlen : j + 1 ≤ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).length)
    (hblk : L53.HasParentInBlock
      ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))) :
    (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))⟦m⟧
      = mTower Q d e n
        ++ ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))⟦m⟧ := by
  have hTlen : ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length = j + 1 := by
    rw [List.length_take]; omega
  have hTne : (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1) ≠ [] := by
    intro hc
    have hl : ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length = 0 := by
      rw [hc]; rfl
    omega
  have hT2 : ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1 ≠ 0 := by
    rw [hTlen]; omega
  exact L53.comm_of_hasParentInBlock m hTne hT2 (hz_of_hasParentInBlock hblk) hblk

/-! ### 104.2 ⟹ 3 分割（`j` と `Q[j]` の性質で決まる）

    **`j = 0`**                       … 悪根は**前のブロック**（§101。`≥ (n-1)*|Q|`）
    **`j ≥ 1` ∧ `Q[j]` が `Q` の中に親を持つ** … **悪根はブロック `n` の接頭辞の中**（上）
                                       ⟹ **前半 `n` ブロックは触られない**
    **`j ≥ 1` ∧ `Q[j]` が `Q` の中で孤児**   … `T` に親が無い ⟹ 悪根は前のブロックへ
                                       ⟹ **§102 `gexp_orphan_row1` の場面**
                                         （行 1 が根以下なら**塔でも孤児 ⟹ 無料**）

> **⟹ team-lead の「`j = 0` は特別ではない」は誤りでした。`j = 0` だけが
> 「土台の中に自分のブロックの仲間が 1 つも無い」状態で、そこだけ境界をまたぎます。**

### 104.3 ⟹ そして `j ≥ 1` の枝は既存の機械にそのまま乗ります

`comm_of_hasParentInBlock` で前半が切り離せるので、`mem_of_oper_mem` で

    `A ++ (block n).take (j+1) ∈ W u` ⟸ `∀ m ≥ 1, A ++ ((block n).take (j+1))⟦m⟧ ∈ W u`

となり、右辺は**ブロック `n` の接頭辞の導出に沿って降りる**。
⟹ **§90 `catBlock_of_escape_head`（`c = d*n`）がそのまま当たる**形である。
**⟹ 底は「決まった 1 列」、残りは孤児の枝。**

⚠ **これは形の整理であって、残差が減ったわけではありません。**
**`j = 0`（境界）と、`j ≥ 1` の孤児でない枝の底が、依然として残差です。** -/

/-! ## 105. ⛔ 自己訂正 2 件 ＋ ★ 2 ブロックへの還元（R2 の §R134-136）

### 105.1 ⛔ §95.1 の見出しは **`z ≥ 1` では誤り**です

私は §95.1 に「**`r` は孤児になりません**」と書き、根拠に**行 0 の親の存在**を挙げた。
**しかし要るのは行 `srow r` の親である。**

    `z = 0` … `srow r = 1` ⟹ 行 1 の親が要る。§95.1 の議論はそこは正しい
    **`z ≥ 1` … `srow r = 2` ⟹ 行 2 の親が要る。行 0 の親があっても関係ない**

**R2 の実測: 足す列が孤児なのは `srow`(足す列)別に 0 → 25.0% ／ 1 → 32.0% ／ **2 → 74.2%**、
`z=0` → 31.1% ／ **`z=1` → 74.2%**。**
**⟹ 私の「孤児にならない」は 25〜36% しか当たっていない。見出しを撤回する。**

⟹ **正しくは: `z = 0` では孤児にならない（§95.1 の議論）。`z ≥ 1` では 74〜82% が孤児**
（そこは `snoc_orphan_W`（§4、緑）で**無料**）。

### 105.2 ⛔ §88.2 の「箱を疑え」は **軸を間違えていました**

私は「反例の形は `n*d1 ≥ entry Q 1 last − entry Q 1 0` なので `n ≤ 2` の箱では出ない」
と書いたが、R2 が `n = 1..5` で測って**全段で破れ 0**、しかも**私の形は箱に 78.8〜100% 入っていた**
（`n=1` で既に 8 割）。**陽性対照（`hj0` を落とすと 1.03〜1.59% 破れる）も通っている。**

**R2 の理由:「行 1 の値域が狭いと右辺が小さく、`n=1` で既に満たされる。
伸ばすべき軸は `n` ではなく行 1 だった」**（行 1 を 4 まで広げても `n=1` で 78.8〜98.8%）。

⟹ **私の「反例の形」は正しかったが、「その形が箱に入らない」という判断が誤り。**
**教訓 45 は「形を書く」だけでなく「その形の充足率を自分で見積もる」まで含むべきだった。**

### 105.3 ★ `snoc_flat_root` について（記録のため）

**私の §94.2 / §95.2 は最初から `srow = 0` を書いています**
（「`srow = 0` かつ**親が根**なら無料」「両方を要求する」）。
R2 が測った実効射程は**親ありの 1.5〜2.3%**。**⟹ 無料の 2 枝のうち、こちらはほぼ効かない。**

### 105.4 ★★★★ R2 の還元: **現象は 2 ブロックで決まる**

R2 の実測: 破れる `(Q,d,e)` の集合は **`n = 2,3,4,5` で完全に一致**し、
復活先は**常に 1 つ前のブロック**。⟹ **`n` は効かない。**

**⟹ 私の指標では `n = 1`（土台 ＝ ブロック 0 ＝ `Q`、作るのはブロック 1）で書けばよい。**
そのとき §94 の段 `j = 0` は **`Q` への 1 列の snoc**そのものになる。 -/

theorem take_one_of_ne_nil {l : TrioSeq} (h : l ≠ []) :
    l.take 1 = [l.getD 0 (0, 0, 0)] := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

open Classical in
/-- **★★★★★ 2 ブロックの `j = 0` の段 ＝ `Q` に「ずらした根」を 1 列足すこと。** -/
theorem tower_step0_two {Q : TrioSeq} {d e : ℕ} (hQne : Q ≠ []) :
    mTower Q d e 1 ++ (Lift1 (shiftr01 (d * 1) 0 Q) (e * 1)).take 1
      = Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)] := by
  have hQlen : 0 < Q.length := List.length_pos_iff.mpr hQne
  have hBne : Lift1 (shiftr01 (d * 1) 0 Q) (e * 1) ≠ [] := by
    intro hc
    have hl : (Lift1 (shiftr01 (d * 1) 0 Q) (e * 1)).length = 0 := by rw [hc]; rfl
    rw [Lift1_length, shiftr01_length] at hl
    omega
  rw [mTower_one, take_one_of_ne_nil hBne, block_getD (d := d) (e := e) (n := 1) hQlen,
    if_pos (le1_refl hQlen), Nat.mul_one, Nat.mul_one]

/-- **★★★★★★ 2 ブロックの残差**: `Q` に「行 0 を `d`、行 1 を `e` ずらした根」を足す。 -/
def TowerSnocRoot : Prop :=
  ∀ (u d e : ℕ) (Q : TrioSeq), Q ∈ W u → 2 ≤ Q.length →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
    Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)] ∈ W u

/-! ### 105.5 ⟹ `TowerSnocRoot` の位置づけ

    **無料**（R2 の実測 49.7〜66.0%）… 足した列が**孤児のまま** ⟹ `snoc_orphan_W`（§4、緑）
        **`z = 1` では 74.2%**（`srow = 2` なので行 2 の親が要るが、行 2 は塔で動かない）
    **残差**（34〜50%）… 足した列が親を見つける ⟹ **`z = 0` 側が主**（31.1% しか孤児でない）

⚠ **`z` の効き方が §93（F2b は `z=1` だけ）と**逆**である:**

    **F2b（B の残差）** … `z = 1` だけ
    **`TowerSnocRoot`（A の残差）** … **`z = 0` 側が重い**

**⟹ A と B は `z` について相補的。どちらか一方だけでは断片は閉じない。** -/

/-! ## 106. ★★★★★★ §103.3 を Lean に: **F2a の同ブロックの枝は 3 行**

索引で `nextrel2` を引いたら、**`le1` を経由する必要がありませんでした**:

    **`L53.nextrel2_append_right`（`:801`、緑）** … `nextrel2 (A ++ N) (|A|+a) (|A|+b) ↔ nextrel2 N a b`
    **`Wset.nextrel2_Lift1`（`:1244`、緑）** ／ **`Wset.nextrel2_shiftr01`（`:347`、緑）**
    **`Invariant.nextrel2_unique`（`:746`、緑）**

⟹ **`nextrel2` はブロックの中で `Q` のものと一致する**（`le1` の転送も `le1_block` も要らない）。 -/

open Classical in
/-- **★★★★★★ 最後のブロックの中に行 2 の親は無い**（`Q` の末尾列が行 2 の孤児なら）。 -/
theorem nextrel2_lastBlock_absurd {Q A : TrioSeq} {d0' d1' qa b : ℕ}
    (horph : ¬ hasParent Q 2 b)
    (h : nextrel2 (A ++ Lift1 (shiftr01 d0' 0 Q) d1') (A.length + qa) (A.length + b)) :
    False := by
  rw [L53.nextrel2_append_right, nextrel2_Lift1, nextrel2_shiftr01] at h
  have hnR : nextR Q 2 qa b := by
    unfold nextR
    rw [if_neg (by omega), if_neg (by omega)]
    exact h
  refine horph ⟨qa, hnR, ?_⟩
  intro y hy
  have hy' : nextR Q 2 y b := hy
  unfold nextR at hy'
  rw [if_neg (by omega), if_neg (by omega)] at hy'
  exact nextrel2_unique hy' h

/-- ⟹ 塔の言葉で。 -/
theorem nextrel2_mTower_sameBlock {Q : TrioSeq} {d e n' qa b : ℕ}
    (horph : ¬ hasParent Q 2 b)
    (h : nextrel2 (mTower Q d e (n' + 1))
      ((mTower Q d e n').length + qa) ((mTower Q d e n').length + b)) : False := by
  rw [mTower_succ] at h
  exact nextrel2_lastBlock_absurd horph h

/-! ### 106.1 ⟹ F2a の残る穴は **`a` が前のブロック**の 1 点だけ

    ✅ **`a` が最後のブロックの中** … 上で閉じた（**`le1` を通らない。`nextrel2` の転送だけ**）
    ⛔ **`a` が前のブロック**       … §103.4 のとおり。越えるには **G2** の列が要る

⚠ **私の §103.3 は `le1_append_right` ＋ `le1_block` ＋ `hasParent_two_of` の 3 段を考えていたが、
`nextrel2_append_right` が最初から `nextrel2` を丸ごと運ぶので 1 段で済んだ。**
**索引で `nextrel2` を全部見てから書いたのが効いた**（`grep nextrel2 LEMMA-INDEX.tsv`）。

### 106.2 ⟹ F2a の全体像

    `nextrel2 T a last` を仮定
    §103.1-2 ⟹ **`a` も鎖の全ノードも塔の根の錐の外**
    **`a` が最後のブロックの中 ⟹ §106（上）で矛盾**
    `a` が前のブロック ⟹ **G2 の列で境界を越える必要がある**（§103.4）
      ⟹ **R2 の (f1a)（`|M|` を 6, 7 まで、分母を先に）待ち** -/

/-! ## 107. ★★★★★★★ **G2 があっても越境できません**: `nextrel1` の壁が完成しました

§103.4 で「越境には G2 が要る」と絞ったが、**G2 でも越えられない。**
**理由は「錐の外にする張本人（ブロッカー）が、同じブロックの中の行 0 祖先だから」。**

    `b` が `M` の錐の外 ⟹ **`not_le1_zero_iff`（§96）** で
      **`b` の行 0 祖先 `y ≠ 0` に `entry M 1 y ≤ entry M 1 0` のものがある**
    その像はブロック `k` の中（`gexp_rtg0_mir`）で、`c` はブロック外 ⟹ **`c < 像`**
    ⟹ **`nextrel1` の極小性が `entry T 1 b ≤ entry T 1 (像)` を要求**
    `y` はブロッカー ⟹ **錐の外 ⟹ リフトされない** ⟹ `entry T 1 (像) = entry M 1 y ≤ entry M 1 0`
    ⟹ **`entry T 1 b ≤ entry M 1 0`**
    一方 `entry T 1 c < entry T 1 b ≤ entry M 1 0` で、`c` はブロック外 ⟹
      **§99 `gexp_outer_anc_row1` が `entry M 1 0 < entry T 1 c`**（`c ≠ 0`）
    ⟹ **矛盾**（`c = 0` なら `entry T 1 0 = entry M 1 0` で同じく矛盾）

**⟹ §87（錐の中）と合わせて、`nextrel1` は根以外のどの列にも外から入れない。** -/

open Classical in
/-- **★★★★★★★ 錐の外の列にも、ブロック外から行 1 の親は来ない。** -/
theorem nextrel1_gexp_no_enter_out {M : TrioSeq} {Lb d0 d1 n k q c : ℕ}
    (hlen : 0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hk : k < n) (hq : q < Lb)
    (hd1pos : 0 < d1)
    (hd0e : entry M 0 (0 + Lb) = entry M 0 0 + d0)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + Lb))
    (hout : ¬ le1 M 0 (0 + q))
    (h : nextrel1 (gexp M 0 Lb d0 d1 n) c (0 + (k * Lb + q))) :
    k * Lb ≤ c := by
  by_contra hc
  have hn : 0 < n := by omega
  -- 目標の行 1（錐の外なのでリフト無し）
  have hb1 : entry (gexp M 0 Lb d0 d1 n) 1 (0 + (k * Lb + q)) = entry M 1 (0 + q) := by
    rw [gexp_entry1_mir hlen hk hq, if_neg hout]
    omega
  -- ブロッカーを取り出す
  obtain ⟨y, hy, hy0, hyle⟩ := (not_le1_zero_iff hr0 (show 0 + q < M.length by omega)).mp hout
  obtain ⟨y', hy'⟩ : ∃ y', y = 0 + y' := ⟨y, (Nat.zero_add y).symm⟩
  subst hy'
  have hyq : 0 + y' ≤ 0 + q := nextrel0_rtrancl_index_le hy
  have hy'lt : y' < Lb := by omega
  -- ブロッカーの像はブロック `k` の中で、`b` の行 0 祖先
  have hmir : Relation.ReflTransGen (nextrel0 (gexp M 0 Lb d0 d1 n))
      (0 + (k * Lb + y')) (0 + (k * Lb + q)) :=
    gexp_rtg0_mir hlen hk hy q rfl hq
  have hXlen : (gexp M 0 Lb d0 d1 n).length = 0 + n * Lb := gexp_length hlen
  have hbnd : k * Lb + q < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hle0 : le0 (gexp M 0 Lb d0 d1 n) (0 + (k * Lb + y')) (0 + (k * Lb + q)) :=
    ⟨by rw [hXlen]; omega, by rw [hXlen]; omega, hmir⟩
  -- ブロッカーは錐の外なのでリフトされない
  have houty : ¬ le1 M 0 (0 + y') := by
    intro hcy
    have := le1_entry1_lt hcy (show (0 : ℕ) ≠ 0 + y' from by omega)
    omega
  have hy1 : entry (gexp M 0 Lb d0 d1 n) 1 (0 + (k * Lb + y')) = entry M 1 (0 + y') := by
    rw [gexp_entry1_mir hlen hk hy'lt, if_neg houty]
    omega
  -- 極小性
  have hmin := h.2.2.2.2.2 (0 + (k * Lb + y')) ⟨by omega, hle0⟩
  rw [hb1, hy1] at hmin
  -- `c` の行 1
  have hlt := h.2.2.2.1
  rw [hb1] at hlt
  by_cases hc0 : c = 0
  · subst hc0
    have h10 : entry (gexp M 0 Lb d0 d1 n) 1 0 = entry M 1 0 :=
      gexp_entry_root hlen hn hLb
    rw [h10] at hlt
    omega
  · have := gexp_outer_anc_row1 hlen hLb hk hq hd1pos hd0e hr0 hlp c
      h.2.2.2.2.1.2.2 (by omega) hc0
    omega

/-! ### 107.1 ★★★★★★★ ⟹ `nextrel1` の壁が完成しました

    **§87 `nextrel1_gexp_no_enter`** … 目標が**錐の中**のとき
    **§107 `nextrel1_gexp_no_enter_out`** … 目標が**錐の外**のとき
    **⟹ 場合分けが尽きた。`nextrel1` は根以外のどの列にも、ブロック外から入れない。**

⟹ **`le1` の鎖もブロックを出られない**（§89 と合わせて帰納で回せる）
⟹ **F2a の残る穴（§103.4）が閉じました。**

⚠ **R2 の実測（`|Q|=6`・分母 117 万・破れ 0、G2 ありでも破れ 0）と一致します。**
**そして機構は「G2 でも越えられない」で、R2 が示唆した方向そのものです。** -/

/-! ## 108. ★★★★★★★ **`le1` の鎖もブロックを出られません**（F2a の組み立ての最後の 1 本）

§87（錐の中）＋ §107（錐の外）で `nextrel1` の 1 歩が塞がった。鎖に沿って繰り返す。

⚠ **1 か所だけ注意**: `nextrel1` はブロックの**根**には外から入れる（§87/§107 は `q ≥ 1` を要求）。
だが **`le1 T 0 (ブロックの根)` は真**（§98 `gexp_blockRoot_cone`）なので、
**根が鎖に乗ると目標も錐の中になってしまう** ⟹ 目標が錐の外なら**根は鎖に乗らない**。 -/

open Classical in
theorem le1_gexp_in_block {M : TrioSeq} {Lb d0 d1 n k : ℕ}
    (hlen : 0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hk : k < n) (hd1pos : 0 < d1)
    (hd0e : entry M 0 (0 + Lb) = entry M 0 0 + d0)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + Lb)) :
    ∀ q, q < Lb → 0 < q → ¬ le1 M 0 (0 + q) → ∀ a,
      Relation.ReflTransGen (nextrel1 (gexp M 0 Lb d0 d1 n)) a (0 + (k * Lb + q)) →
      k * Lb ≤ a := by
  have hup : ∀ l, 0 < l → l ≤ 0 + Lb → entry M 0 0 < entry M 0 l :=
    fun l hl0 hl1 => hr0 l hl0 (by omega)
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq hq1 hout a ha
    rcases ha.cases_tail with heq | ⟨c, hc1, hc2⟩
    · omega
    · have hcge : k * Lb ≤ c := by
        by_cases hcone : le1 M 0 (0 + q)
        · exact absurd hcone hout
        · exact nextrel1_gexp_no_enter_out hlen hLb hk hq hd1pos hd0e hr0 hlp hcone hc2
      have hclt : c < 0 + (k * Lb + q) := hc2.2.2.1
      obtain ⟨q', hq'⟩ : ∃ q', c = 0 + (k * Lb + q') := ⟨c - k * Lb, by omega⟩
      subst hq'
      have hq'lt : q' < Lb := by omega
      -- 目標が錐の外なら `c` も錐の外（`c` が錐の中なら 1 歩で目標も錐の中になる）
      have houtc : ¬ le1 M 0 (0 + q') := by
        intro hcone'
        refine hout ?_
        rw [← gexp_cone_mir_zero hlen hLb hk hq hd1pos hd0e hr0 hlp]
        have hcc : le1 (gexp M 0 Lb d0 d1 n) 0 (0 + (k * Lb + q')) := by
          rw [gexp_cone_mir_zero hlen hLb hk hq'lt hd1pos hd0e hr0 hlp]
          exact hcone'
        exact ⟨hcc.1, hc2.2.1, hcc.2.2.tail hc2⟩
      rcases Nat.eq_zero_or_pos q' with rfl | hq'pos
      · exact absurd (le1_refl (by omega)) houtc
      · exact ih q' (by omega) (by omega) hq'pos houtc a hc1

/-! ### 108.1 ⟹ F2a の道具が全部揃いました

    §103.1-2 `not_le1_zero_src` … `nextrel2 T a last` の `a` は錐の外
    **§108（上）** … **`le1 T a last`（目標が錐の外）は `a` をブロックに閉じ込める**
    §106 `nextrel2_lastBlock_absurd` … 同じブロックの中には行 2 の親は無い
    **⟹ 矛盾。F2a は落ちます。**

⚠ **`q' = 0`（ブロックの根）の枝は「`le1 M 0 (0+0)` は反射で真」なので
`houtc` に矛盾して消えます** —— 根が鎖に乗ると目標が錐の中になってしまうからです。 -/

/-! ## 109. ★★★★★★★ **F2a は定理**（塔の最後のブロック）

§108 を `mTower` の言葉に移し（§85 と同じ手順）、§106 と合わせて組み立てる。 -/

open Classical in
/-- **§108 の `mTower` 版**: 目標が錐の外なら `le1` の祖先は同じブロックの中。 -/
theorem le1_mTower_in_block {M : TrioSeq} {d e n k q : ℕ} (hM2 : 2 ≤ M.length)
    (hd1pos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hk : k < n) (hq : q < M.dropLast.length) (hq1 : 0 < q)
    (hout : ¬ le1 M 0 (0 + q)) :
    ∀ a, Relation.ReflTransGen (nextrel1 (mTower M.dropLast d e n)) a
        (k * M.dropLast.length + q) →
      k * M.dropLast.length ≤ a := by
  have hdl : M.dropLast.length = M.length - 1 := List.length_dropLast
  have hlen : 0 + M.dropLast.length + 1 = M.length := by rw [hdl]; omega
  have hLb : 0 < M.dropLast.length := by rw [hdl]; omega
  have hgexp : gexp M 0 M.dropLast.length d e n = mTower M.dropLast d e n := by
    rw [gexp_zero_eq_mTower (by omega), hdl, ← List.dropLast_eq_take]
  intro a ha
  refine le1_gexp_in_block hlen hLb hk hd1pos hd0e hr0 hlp q hq hq1 hout a ?_
  rw [hgexp, Nat.zero_add]
  exact ha

open Classical in
/-- **★★★★★★★ F2a**: `Q` の末尾列が「錐の外 ∧ 行 2 の孤児」なら、塔でも行 2 の孤児。 -/
theorem mTower_orphan_row2 {M : TrioSeq} {d e n' : ℕ} (hM2 : 2 ≤ M.length)
    (hd1pos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hQ2 : 2 ≤ M.dropLast.length)
    (hout : ¬ le1 M 0 (0 + (M.dropLast.length - 1)))
    (horph : ¬ hasParent M.dropLast 2 (M.dropLast.length - 1)) :
    ¬ hasParent (mTower M.dropLast d e (n' + 1)) 2
      ((mTower M.dropLast d e n').length + (M.dropLast.length - 1)) := by
  have hLb : 0 < M.dropLast.length := by omega
  have hAlen : (mTower M.dropLast d e n').length = n' * M.dropLast.length := by
    rw [mTower_length]
  rintro ⟨a, ha, -⟩
  have hnr : nextrel2 (mTower M.dropLast d e (n' + 1)) a
      ((mTower M.dropLast d e n').length + (M.dropLast.length - 1)) := by
    unfold nextR at ha
    rw [if_neg (by omega), if_neg (by omega)] at ha
    exact ha
  have hge : n' * M.dropLast.length ≤ a := by
    have h := le1_mTower_in_block (n := n' + 1) (k := n') hM2 hd1pos hd0e hr0 hlp
      (by omega) (show M.dropLast.length - 1 < M.dropLast.length by omega)
      (by omega) hout a ?_
    · exact h
    · rw [hAlen] at hnr
      exact hnr.2.2.2.2.1.2.2
  have halt : a < (mTower M.dropLast d e n').length + (M.dropLast.length - 1) :=
    hnr.2.2.1
  obtain ⟨qa, hqa⟩ : ∃ qa, a = (mTower M.dropLast d e n').length + qa :=
    ⟨a - n' * M.dropLast.length, by omega⟩
  subst hqa
  rw [mTower_succ] at hnr
  exact nextrel2_lastBlock_absurd horph hnr

/-! ### 109.1 ⟹ B（`MTowerOrphan`）の 2 枝が両方定理になりました

    **F1** … §102 `gexp_orphan_row1`（任意の `(k,q)`）
    **F2a** … **§109（上）**

**⟹ 残るのは F2b（`z = 1`）だけで、そこは §93 で「命題が偽」と確定しています。**
**⟹ R2 の (z5)（F1 376,164 ＋ F2a 933,768 ＝ 130 万件・破れ 0）が定理になりました。** -/

/-! ## 110. ★★★★★★★ **`TowerSnocRoot` と `MTowerClosedS` は同じ文でした**

`TowerSnocRoot`（§105）は「`Q` に `r = (根の行0+d, 根の行1+e, 根の行2)` を 1 列足す」。
**その `Q ++ [r]` に §68 `oper_eq_mTower` を当てると、右辺が `mTower Q d e m` そのものになる。**

    `M := Q ++ [r]` ⟹ `|M| = |Q| + 1`、`M.dropLast = Q`
    `d0 = entry M 0 (|M|-1) − entry M 0 0 = (entry Q 0 0 + d) − entry Q 0 0 = d`
    `d1 = entry M 1 (|M|-1) − entry M 1 0 = (entry Q 1 0 + e) − entry Q 1 0 = e`

**⟹ `(Q ++ [r])⟦m⟧ = mTower Q d e m`（悪根が根のとき）。**
**⟹ `Wchar.mem_iff_oper_mem` で `Q ++ [r] ∈ W u ⟺ ∀ m ≥ 1, mTower Q d e m ∈ W u`。**
**⟹ 2 つの残差は同じ 1 文。塔を消したのは「別の問題にした」のではなく「同じ問題の最小形」。** -/

/-! ⚠ **再発明 10 回目を `leanman check` が止めました**: `entry_snoc_last` は
**この file の `:62`（§2）に私自身が書いています**。索引を引く前に手が動きました。 -/

open Classical in
/-- **★★★★★★★ `Q` に「ずらした根」を足したものの展開は、塔そのもの。** -/
theorem oper_snocRoot {Q : TrioSeq} {d e m : ℕ} (hQ2 : 2 ≤ Q.length)
    (hz : ¬ (entry (Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)]) 0
        ((Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)]).length - 1) = 0 ∧
      entry (Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)]) 1
        ((Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)]).length - 1) = 0 ∧
      entry (Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)]) 2
        ((Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)]).length - 1) = 0))
    (hp : hasParent (Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)])
        (srow (Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)])
          ((Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)]).length - 1))
        ((Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)]).length - 1))
    (hj0 : parent (Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)])
        (srow (Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)])
          ((Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)]).length - 1))
        ((Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)]).length - 1) = 0)
    (hsr2 : 1 < srow (Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)])
        ((Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)]).length - 1)) :
    (Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)])⟦m⟧
      = mTower Q d e m := by
  have hlen : (Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)]).length
      = Q.length + 1 := by
    rw [List.length_append]; simp
  have hl1 : (Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)]).length - 1
      = Q.length := by rw [hlen]; omega
  have hres := oper_eq_mTower m (by rw [hl1]; omega) hz hp hj0
  rw [hl1] at hres hsr2
  rw [hres, if_pos (show 0 < srow (Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e,
      entry Q 2 0) : ℕ × ℕ × ℕ)]) Q.length from by omega), if_pos hsr2,
    entry_snoc_last, entry_snoc_last,
    List.dropLast_concat]
  have h0 : entry ([((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)]) 0 0
      = entry Q 0 0 + d := rfl
  have h1 : entry ([((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)]) 1 0
      = entry Q 1 0 + e := rfl
  have h0q : entry (Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)]) 0 0
      = entry Q 0 0 := entry_append_left _ _ (by omega)
  have h1q : entry (Q ++ [((entry Q 0 0 + d, entry Q 1 0 + e, entry Q 2 0) : ℕ × ℕ × ℕ)]) 1 0
      = entry Q 1 0 := entry_append_left _ _ (by omega)
  rw [h0, h1, h0q, h1q]
  simp

/-! ### 110.1 ⟹ A と B は同じ 1 文の 2 つの姿

    **`TowerSnocRoot`（§105）** … `Q ++ [r] ∈ W u`
    **`MTowerClosedS`（§74）**   … `∀ m, mTower Q d e m ∈ W u`
    **`Wchar.mem_iff_oper_mem` ＋ 上 ⟹ 同値**（悪根が根で `srow = 2` のとき）

**⟹ §105 で「塔が消えた」のは、別の問題にしたのではなく、同じ問題の最小形に書き直したもの。**
**⟹ そして `mem_of_oper_mem` は片方向なので、証明としては
「`Q ++ [r]` の展開が `W u` にある」を示せばよい ＝ 塔の閉包そのもの。**

⚠ **`srow = 1`（`z = 0` かつ行 2 が 0）では `d1 = 0` になり、
右辺は `mTower Q d 0 m = shTower Q d m`（`Lift1` が消える）**
⟹ **`Wtower2.ShiftTowerClosedS` の領域。`e > 0` より易しいはず**（team-lead の読み）。 -/

/-! ## 111. ★★★★★★ `TowerSnocRoot` の枝分け: **親が内側なら前半は触られない**

`Q ++ [p]` の 3 分割（`p` の親の位置で決まる）:

    **(A) 親なし**       … `snoc_orphan_W`（§4、緑）で**無料**。R2 実測 `z=1` で 74.2%
    **(B) 親 ＝ 根**     … §110 `oper_snocRoot` で **`(Q++[p])⟦m⟧ = mTower Q d e m`**（塔）
    **(C) 親が内側 `j0 ≥ 1`** … **下**（前半 `Q.take j0` は触られない ⟹ 短い `Q` に降りる）

(C) の道具は §106 と同じ `L53.comm_of_hasParentInBlock` で、
**`Q ++ [p] = Q.take j0 ++ (Q.drop j0 ++ [p])`** と分けるだけである。 -/

open Classical in
theorem snocRoot_comm_of_inner {Q : TrioSeq} {p : ℕ × ℕ × ℕ} {j0 m : ℕ}
    (hj0lt : j0 < Q.length)
    (hp : hasParent (Q ++ [p]) (srow (Q ++ [p]) Q.length) Q.length)
    (hpar : parent (Q ++ [p]) (srow (Q ++ [p]) Q.length) Q.length = j0) :
    (Q ++ [p])⟦m⟧ = Q.take j0 ++ (Q.drop j0 ++ [p])⟦m⟧ := by
  set i : ℕ := srow (Q ++ [p]) Q.length with hi
  set A : TrioSeq := Q.take j0 with hA
  set T : TrioSeq := Q.drop j0 ++ [p] with hT
  have hAlen : A.length = j0 := by rw [hA, List.length_take]; omega
  have hTlen : T.length = Q.length - j0 + 1 := by
    rw [hT, List.length_append, List.length_drop]; simp
  have hdec : Q ++ [p] = A ++ T := by
    rw [hA, hT, ← List.append_assoc, List.take_append_drop]
  have hb : Q.length = A.length + (T.length - 1) := by rw [hAlen, hTlen]; omega
  -- `T` は自分の中に親を持つ（添字 0 ＝ もとの `j0`）
  have hnr : nextR (A ++ T) i (A.length + 0) (A.length + (T.length - 1)) := by
    have h := parent_nextR hp
    rw [hpar] at h
    rw [← hdec, ← hb]
    simpa [hAlen] using h
  have hT0 : nextR T i 0 (T.length - 1) := (L53.nextR_append_right).mp hnr
  have hTp : hasParent T i (T.length - 1) := by
    refine ⟨0, hT0, ?_⟩
    intro y hy
    have hy' : nextR (A ++ T) i (A.length + y) (A.length + (T.length - 1)) :=
      (L53.nextR_append_right).mpr hy
    rw [← hdec, ← hb] at hy'
    have := hp.unique hy' (by rw [← hdec, ← hb] at hnr; simpa using hnr)
    omega
  -- `srow` は末尾列だけで決まるので `T` のものと一致
  have hsr : srow T (T.length - 1) = i := by
    have hent : ∀ y, entry T y (T.length - 1) = entry (Q ++ [p]) y Q.length := by
      intro y
      rw [hdec, hb]
      exact (L53.entry_append_right).symm
    unfold srow
    rw [hent, hent, hi]
    rfl
  have hblk : L53.HasParentInBlock T := by
    unfold L53.HasParentInBlock
    rw [hsr]
    exact hTp
  have hTne : T ≠ [] := by
    intro hc
    have hl : T.length = 0 := by rw [hc]; rfl
    omega
  have hT2 : T.length - 1 ≠ 0 := by omega
  rw [hdec]
  exact L53.comm_of_hasParentInBlock m hTne hT2 (hz_of_hasParentInBlock hblk) hblk

/-! ### 111.1 ⟹ 3 分割の意味

    **(A) 親なし** … **無料**（`snoc_orphan_W`）。R2: `z=1` で 74.2%、`z=0` で 31.1%
    **(B) 親 ＝ 根** … §110 で **塔そのもの**（＝ `MTowerClosedS`）
    **(C) 親が内側** … **前半 `Q.take j0` は触られない**（上）
        ⟹ 残るのは **`Q.drop j0 ++ [p]`（短い `Q`）の展開**と、その前に `Q.take j0` を継ぐこと

⟹ **(C) は `|Q|` の帰納で降りられる形**である。ただし**連結（`Q.take j0 ++ …`）が残る**ので、
そこは §90 `catBlock_of_escape_head` の領域（底は「決まった 1 列」）。

⚠ **(B) が本丸**である。そこは §110 で `MTowerClosedS` と同値と分かっている。
**⟹ `TowerSnocRoot` の攻め方は「(A) 無料 ／ (C) 帰納 ／ (B) が核」。** -/

/-! ## 112. ★ 15 分の判定: **`z = 0` の核は `ShiftTowerClosedS` そのものです**

### 112.1 (1) 同値か ⟹ **同値どころか、同じ文です**

`mTower Q d 0 n` の第 `k` ブロックは `Lift1 (shiftr01 (d*k) 0 Q) (0*k) = Lift1 (…) 0 = shiftr01 (d*k) 0 Q`
（`Wset.Lift1_zero`）で、`shTower` の第 `k` ブロック `shiftr01 (k*d) 0 Q` と**同じ**。 -/

theorem mTower_e_zero_eq_shTower (Q : TrioSeq) (d n : ℕ) :
    mTower Q d 0 n = shTower Q d n := by
  unfold mTower shTower
  refine List.flatMap_congr ?_
  intro k _
  rw [Nat.zero_mul, Lift1_zero, Nat.mul_comm]

/-- `MTowerClosedS` の `e = 0` への制限。 -/
def MTowerClosedS0 : Prop :=
  ∀ (u d n : ℕ) (Q : TrioSeq), Q ∈ W u →
    (∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j) →
    mTower Q d 0 n ∈ W u

/-- **★★★★★ `z = 0` の核は `(TOW)` そのもの**（同値ではなく同一）。 -/
theorem mTowerClosedS0_iff : MTowerClosedS0 ↔ ShiftTowerClosedS := by
  constructor
  · intro h u e n Q hQ hs
    rw [← mTower_e_zero_eq_shTower]
    exact h u e n Q hQ hs
  · intro h u d n Q hQ hs
    rw [mTower_e_zero_eq_shTower]
    exact h u d n Q hQ hs

/-! ### 112.2 (2) どちらが弱いか

    `ShiftTowerClosedS` は **`MTowerClosedS` の `e = 0` への制限**である（上）
    ⟹ **フルの `MTowerClosedS` より真に弱い**（`e > 0` を含まない）
    ⟹ **しかし `z = 0` の枝に限れば、弱くも強くもない。同じ文。**

**⟹ 「`z=0` を `ShiftTowerClosedS` に落とす」は、論理的には何も得ません。**
**私の但し書き（「別の未証明に移るだけかもしれない」）が当たっていました。**

### 112.3 (3) ⟹ **それでも進む価値があります: 道具の数が違う**

索引で数えました（`grep shTower LEMMA-INDEX.tsv`）。**`shTower` 側の既存の緑:**

    `Wtower2.shTower_succ` / `L105.shTower_cons`（§43）/ `L47W.shTower_prefix`
    **`L105.oper_shTower`（§48）** … 展開は最後のブロックだけ
    `L105.entry_shTower_root` / `lev_shTower_root`（§45）… 根の `lev` は不変
    `L47W.shTower_zeroRow2` / `shiftTowerClosed_of_zeroRow2` … 行 2 ≡ 0 は無料
    **`L47W.shiftTowerClosed_iff_wself`** … 段が消える（`Wself` 版と同値）
    `Wtower2.lspOn_srow1_of_tower` / `liftStageParented_of_tower` / `towerExp1_of_tower`
    **`Final.TRIO_terminates_of_tower` / `no_infinite_expansion_of_tower`（頂点定理が既にある）**

**`mTower` 側は私が今日書いた §55-§111 だけです。**
**⟹ 同じ文でも、`shTower` の言葉で書くほうが道具が 3 倍あります。**

### 112.4 ⚠ `CORES.md` の「上流に `WCat`」について

    `Wtower2.shiftTowerClosedS_of_closed : ShiftTowerClosed → ShiftTowerClosedS`
    `Wtower2.shiftTowerClosedS_of_substG : SubstClosedG → ShiftTowerClosedS`

**どちらも「X ⟹ `ShiftTowerClosedS`」＝ X は十分条件**です。
**⟹ `ShiftTowerClosedS` を直接証明するのに `WCat` は要りません。**
**`CORES.md` の「上流」は「そこから出せる」であって「そこを通らねばならない」ではない。**

> **⟹ 判定: `z = 0` の枝は `ShiftTowerClosedS` の言葉で書く。**
> **論理的な利得はゼロだが、道具が 3 倍あり、頂点定理も既にある。`WCat` は強制されない。** -/

/-! ## 113. ★★★★★★ `(TOW)` を 2 本に割る: **底の snoc ＋ 孤児の枝。装備は要りません**

§112 で `z = 0` の核が `ShiftTowerClosedS`（＝ `(TOW)`）そのものと分かった。
**そこに §48 `oper_shTower` と §90 `catBlock_of_escape_head` をそのまま当てる。**

⚠ **`mTower` 側（§82）と違い、リフト装備（`∀ s, ∃ u', Lift1 Q s ∈ W u'`）が要りません。**
**`e = 0` なので `Lift1` が出てこず、`Q⟦m⟧ ∈ W u` が `Q ∈ W u` から直接出るからです。** -/

theorem headD_fst {Q : TrioSeq} : (Q.headD (0, 0, 0)).1 = entry Q 0 0 := by
  rw [headD_eq_getD]; rfl

theorem headD_snd {Q : TrioSeq} : (Q.headD (0, 0, 0)).2.1 = entry Q 1 0 := by
  rw [headD_eq_getD]; rfl

theorem headD_thd {Q : TrioSeq} : (Q.headD (0, 0, 0)).2.2 = entry Q 2 0 := by
  rw [headD_eq_getD]; rfl

open Classical in
/-- **★★★★★★ `(TOW)` は「底の snoc」＋「孤児の枝」の 2 本に落ちる**（装備なし）。 -/
theorem shTower_mem_of_escape {u e : ℕ} {Q : TrioSeq} (hQne : Q ≠ [])
    (hQ2 : Q.length - 1 ≠ 0)
    (hzQ : ¬ (entry Q 0 (Q.length - 1) = 0 ∧ entry Q 1 (Q.length - 1) = 0 ∧
      entry Q 2 (Q.length - 1) = 0))
    (hblk : L53.HasParentInBlock Q) (hQ : Q ∈ W u)
    (hsnoc : ∀ n : ℕ, shTower Q e n ∈ W u →
      shTower Q e n ++ [((entry Q 0 0 + n * e, entry Q 1 0, entry Q 2 0) : ℕ × ℕ × ℕ)]
        ∈ W u)
    (hesc : ∀ (n : ℕ) (B : TrioSeq), 2 ≤ B.length →
      ¬ L53.HasParentInBlock (shiftr01 (n * e) 0 B) →
      shTower Q e n ∈ W u → shTower Q e n ++ shiftr01 (n * e) 0 B ∈ W u) :
    ∀ n, shTower Q e n ∈ W u := by
  have hQlen : 2 ≤ Q.length := by
    have : 0 < Q.length := List.length_pos_iff.mpr hQne
    omega
  intro n
  induction n with
  | zero => simpa using W_nil u
  | succ n ih =>
      refine mem_of_oper_mem (fun m hm => ?_)
      rw [oper_shTower hQne hQ2 hzQ hblk e n m]
      refine catBlock_of_escape_head (p := Q.headD (0, 0, 0)) ih ?_
        (fun B hB2 hnb => hesc n B hB2 hnb ih) (Q⟦m⟧)
        (oper_mem_of_mem hQlen hQ m hm) ?_
      · rw [headD_fst, headD_snd, headD_thd]
        exact hsnoc n ih
      · intro _
        exact oper_headD Q (by omega) hm

/-! ### 113.1 ⟹ `(TOW)` の残差は 2 本

    **(T1) 底の snoc** … `shTower Q e n ++ [(entry Q 0 0 + n*e, entry Q 1 0, entry Q 2 0)]`
        **＝ 塔に「行 0 だけ `n*e` ずらした根」を 1 列足す**（**行 1 も行 2 も変わらない**）
    **(T2) 孤児の枝** … `Q` の導出の途中 `B` が段内で孤児のときの連結

⚠ **`mTower` 側の (A1)（§91）と比べると、`(T1)` は行 1 も動きません**
（`mTower` 側は `entry Q 1 0 + e*n` でした）。⟹ **足す列は `Q` の根の行 0 だけをずらしたもの。**

### 113.2 ⟹ そして `(T1)` は §110 と同じ形

§110 `oper_snocRoot` は `Q ++ [(根の行0+d, 根の行1+e, 根の行2)]` の展開が `mTower Q d e m` だと言う。
**`(T1)` は `e = 0` の場合で、土台が `Q` ではなく `shTower Q e n`。**
⟹ **`(T1)` の展開も、同じ手順で書き下せるはず**（`oper_eq_gexp_gen` を悪根の位置で読む）。

**⟹ `(TOW)` の攻め方: `(T1)` を §110 の手順で開き、`(T2)` は §102 の `e = 0` 版で。** -/

/-! ## 114. ⚠ `e = 0`（`(TOW)`）で **どの壁が生き残るか**（署名を索引で写して確認）

team-lead の警告「`gexp_orphan_row1` は `hd1pos : 0 < d1` を持っていたはず」を確かめた。
**索引で 7 本の署名を写した結果、生死がきれいに分かれる。**

    ✅ **§86 `nextrel0_gexp_no_skip`** … **`hd1pos` なし** ⟹ **`e = 0` でも生きる**
    ✅ **§99 `gexp_anc_through_root`** … **`hd1pos` なし** ⟹ **生きる**
    ✅ **§87 `nextrel1_gexp_no_enter`（錐の中）** … **`hd1pos` なし** ⟹ **生きる**
    ⛔ §98 `gexp_blockRoot_cone` / `gexp_blockRoot_anc` … **`hd1pos` あり**
    ⛔ §99 `gexp_outer_anc_row1` … **`hd1pos` あり**
    ⛔ §107 `nextrel1_gexp_no_enter_out`（錐の外） … **`hd1pos` あり**
    ⛔ §102 `gexp_orphan_row1` … **`hd1pos` あり**（§99 経由）

### 114.1 ★ `§87` が生きる理由（`d1` が打ち消し合う）

§87 の極小性は **ブロック `k` の根**を代入して

    `entry M 1 (0+q) + k*d1 ≤ entry M 1 (0+0) + k*d1`

を得る。**`k*d1` は両辺にあるので `d1 = 0` でも同じ結論**（`entry M 1 q ≤ entry M 1 0`）が出て、
`le1_entry1_lt` と矛盾する。⟹ **`d1` の値に依らない。**

### 114.2 ⛔ §98 が死ぬ理由（そこが `e = 0` の本質的な違い）

§98 は **`le1 T 0 (ブロック `k` の根)` が真**であることに乗っている。それは §84 の `q = 0` の場合で、
**§84 は `0 < d1` が無いと偽**（§84.1: `d1 = 0` ではブロックの根の行 1 が上がらず
`nextrel1` の狭義増加が破れる）。

> **⟹ `d1 = 0` では「ブロックの根は塔の根の錐に入る」が偽。**
> **⟹ §98 → §99 → §107 → §102 の連鎖が根元から切れる。**

### 114.3 ⟹ `(TOW)` で足りないもの（1 本）

    **「錐の外の列にも、ブロック外から行 1 の親は来ない」の `d1 = 0` 版**

§107 の骨（ブロッカーの像が同ブロック内の行 0 祖先）はそのまま使えるが、
最後の矛盾で **§99 の `entry M 1 0 < entry T 1 c`** を使っている。
`d1 = 0` では `entry T 1 c = entry M 1 q_c`（リフト無し）なので、
**`entry M 1 q_c ≥ entry M 1 0` を別の理由で出す必要がある。**

⚠ **`(TOW)` の側には「塔は段を一切上げない」という構造がある**（`Wtower2:1763` docstring、
`probe_core1.py` (C) 6244 例・`minstage` は等号）。**そこが使えるかは未確認。**

### 114.4 ⟹ 判断

**`(TOW)` は「道具 3 倍」だが、私が今日作った壁のうち 4 本は `e = 0` で死ぬ。**
**生き残るのは 3 本（§86 / §99 の鎖 / §87）で、足りないのは §107 の `d1 = 0` 版 1 本。**

> **⟹ `(TOW)` に移る利得は「既存の 12 本」であって「今日の壁」ではない。**
> **⟹ §113 の 2 本（`(T1)` 底の snoc ／ `(T2)` 孤児の枝）のうち、
> `(T2)` は §102 が使えないので、`e = 0` 版を作るところから。** -/

/-! ## 115. ★★★★★★★ **`hd1pos` は落とせます**: §107 を `hlp` だけで作り直す

R2 の §R138 (3)（「`e = 0` も含めて 100% 閉じる」）に機構が付いた。
**§107 が `hd1pos` を使っていたのは `gexp_outer_anc_row1`（§99 ← §98 ← §84）経由だけ**で、
**そこは `hlp`（宿主の末尾列が `M` の錐の中）＋ `Gtrans.gexp_chain_inversion` で置き換わる。**

    `c` がブロック `k` の外 ⟹ `gexp_chain_inversion` で `c = (k', q')`、`k' < k`、
      **`RTG (nextrel0 M) (0+q') (0+Lb)`**（`M` の**末尾列**への鎖）
    **`hlp` ＋ `Lcone.le1_zero_iff`** ⟹ **`q' ≠ 0` なら `entry M 1 0 < entry M 1 (0+q')`**
    `Lift1` は行 1 を減らさない ⟹ **`entry T 1 c ≥ entry M 1 0`**（`q' = 0` の根も同じ）

**⟹ `d1` の値をまったく使わない。** -/

open Classical in
theorem nextrel1_gexp_no_enter_out' {M : TrioSeq} {Lb d0 d1 n k q c : ℕ}
    (hlen : 0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hk : k < n) (hq : q < Lb)
    (hd0e : entry M 0 (0 + Lb) = entry M 0 0 + d0)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + Lb))
    (hout : ¬ le1 M 0 (0 + q))
    (h : nextrel1 (gexp M 0 Lb d0 d1 n) c (0 + (k * Lb + q))) :
    k * Lb ≤ c := by
  by_contra hc
  have hn : 0 < n := by omega
  have hup : ∀ l, 0 < l → l ≤ 0 + Lb → entry M 0 0 < entry M 0 l :=
    fun l hl0 hl1 => hr0 l hl0 (by omega)
  have hXlen : (gexp M 0 Lb d0 d1 n).length = 0 + n * Lb := gexp_length hlen
  have hbnd : k * Lb + q < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  -- 目標の行 1（錐の外なのでリフト無し）
  have hb1 : entry (gexp M 0 Lb d0 d1 n) 1 (0 + (k * Lb + q)) = entry M 1 (0 + q) := by
    rw [gexp_entry1_mir hlen hk hq, if_neg hout]
    omega
  -- ブロッカー
  obtain ⟨y, hy, hy0, hyle⟩ := (not_le1_zero_iff hr0 (show 0 + q < M.length by omega)).mp hout
  obtain ⟨y', hy'⟩ : ∃ y', y = 0 + y' := ⟨y, (Nat.zero_add y).symm⟩
  subst hy'
  have hyq : 0 + y' ≤ 0 + q := nextrel0_rtrancl_index_le hy
  have hy'lt : y' < Lb := by omega
  have hmir : Relation.ReflTransGen (nextrel0 (gexp M 0 Lb d0 d1 n))
      (0 + (k * Lb + y')) (0 + (k * Lb + q)) :=
    gexp_rtg0_mir hlen hk hy q rfl hq
  have hle0 : le0 (gexp M 0 Lb d0 d1 n) (0 + (k * Lb + y')) (0 + (k * Lb + q)) :=
    ⟨by rw [hXlen]; omega, by rw [hXlen]; omega, hmir⟩
  have houty : ¬ le1 M 0 (0 + y') := by
    intro hcy
    have := le1_entry1_lt hcy (show (0 : ℕ) ≠ 0 + y' from by omega)
    omega
  have hy1 : entry (gexp M 0 Lb d0 d1 n) 1 (0 + (k * Lb + y')) = entry M 1 (0 + y') := by
    rw [gexp_entry1_mir hlen hk hy'lt, if_neg houty]
    omega
  have hmin := h.2.2.2.2.2 (0 + (k * Lb + y')) ⟨by omega, hle0⟩
  rw [hb1, hy1] at hmin
  have hlt := h.2.2.2.1
  rw [hb1] at hlt
  -- ★ `c` の行 1 が `entry M 1 0` 以上（`hd1pos` を使わない）
  obtain ⟨k', q', hk'le, hq'lt, hxe, hcase⟩ :=
    gexp_chain_inversion hlen hk hq hup hd0e c h.2.2.2.2.1.2.2 (Nat.zero_le c)
  have hk'lt : k' < k := by
    by_contra hcon
    have hge : k * Lb ≤ k' * Lb := Nat.mul_le_mul_right _ (by omega)
    omega
  have hMlast : Relation.ReflTransGen (nextrel0 M) (0 + q') (0 + Lb) := by
    rcases hcase with ⟨he, -⟩ | ⟨-, hM⟩
    · omega
    · exact hM
  have hcge : entry M 1 0 ≤ entry (gexp M 0 Lb d0 d1 n) 1 c := by
    subst hxe
    rw [gexp_entry1_mir hlen (by omega) hq'lt]
    rcases Nat.eq_zero_or_pos q' with rfl | hq'pos
    · rw [if_pos (le1_refl (show (0 : ℕ) < M.length from by omega))]
      have he0 : entry M 1 (0 + 0) = entry M 1 0 := rfl
      omega
    · have hall := (le1_zero_iff hr0 (show 0 + Lb < M.length from by omega)).mp hlp
      have := hall (0 + q') hMlast (by omega)
      split_ifs <;> omega
  omega

/-! ### 115.1 ⟹ 何が変わったか

    §107（旧） … `hd1pos` を要求。`gexp_outer_anc_row1`（§99 ← §98 ← §84）経由
    **§115（新） … `hd1pos` 不要。`hlp` ＋ `gexp_chain_inversion` ＋ `le1_zero_iff`**

**⟹ `e = 0`（`(TOW)`）でも錐の外の壁が立ちます。**
**⟹ §114 で「死ぬ」と判定した 4 本のうち、少なくとも §107 は生き返りました。**

⚠ **§108（鎖の反復）はまだ `gexp_cone_mir_zero`（§84、`hd1pos` 必須）を
`houtc` の導出に使っています。そこは別途。**
**ただし塔の**最後の**ブロックなら `le1_append_right` ＋ `le1_block`（どちらも `hd1pos` 不要）で
置き換えられるはずです。**

⛔ **自己訂正（R2 §R140）**: 私は最初「R2 の反例 `Q=(0,1,0)(1,0,0)(1,1,0)(1,0,0)` は
`hlp` を満たさない」と書いたが、**主語違い**だった。**R2 の `Q` は**ブロック**（`M.dropLast`）で、
私はそれを**宿主 `M`** と読んでいた**（その読みではブロック長が `|Q|-1` になり別物）。

**R2 が正しい埋め込みで測り直した結果:**

    **`hlp` あり              分母 2,332,800  閉じる 99.17%  出る 0.83%**
    `hlp` なし（陰性対照）      分母 13,296,960  閉じる 96.55%  出る **3.45%**
    **`hlp` ∧ `hd0e`（`d` が `M` から決まる） 分母 583,200  閉じる 100.00%  出る 0**

> **⟹ `hlp` だけでは足りない。100% にするのは `hlp` ∧ `hd0e` である。**
> **⟹ 上の定理は `hd0e` を前提に持っているので**無事**。誤っていたのは私の「`hlp` だけで通る」
> という読みのほうで、落とせたのは `hd1pos` であって `hd0e` ではない。**

⚠ **そして `hlp` は塔の場面では `L53.tower2_root_spec` が、`hd0e` は `d0` の定義が与えます。** -/

/-! ## 116. ★★★★★ 行 1 の「同ブロック」も 3 行でした（§106 の行 1 版）

索引を引いたら **`Wset.nextrel1_Lift1`（`:1167`）が無条件**だった
（`nextrel1 (Lift1 X d) a b ↔ nextrel1 X a b`）。**`Lift1` は行 1 を動かすのに、
`nextrel1` は保たれる**（錐の上で一様に上がるので狭義増加も極小性も崩れない）。

⟹ **`nextrel1` もブロックの中で `Q` のものとそのまま一致する。§106（行 2）と同じ形。**

    `L53.nextrel1_append_right`（`:749`、緑）／`Wset.nextrel1_Lift1`（`:1167`）
    `Core.nextrel1_shiftr01`（`:3464`）／`Wset.nextrel1_uniq_src`（`:1053`） -/

open Classical in
/-- **最後のブロックの中に行 1 の親は無い**（`Q` の末尾列が行 1 の孤児なら）。 -/
theorem nextrel1_lastBlock_absurd {Q A : TrioSeq} {d0' d1' qa b : ℕ}
    (horph : ¬ hasParent Q 1 b)
    (h : nextrel1 (A ++ Lift1 (shiftr01 d0' 0 Q) d1') (A.length + qa) (A.length + b)) :
    False := by
  rw [L53.nextrel1_append_right, nextrel1_Lift1, nextrel1_shiftr01] at h
  have hnR : nextR Q 1 qa b := by
    unfold nextR
    rw [if_neg (by omega), if_pos rfl]
    exact h
  refine horph ⟨qa, hnR, ?_⟩
  intro y hy
  have hy' : nextR Q 1 y b := hy
  unfold nextR at hy'
  rw [if_neg (by omega), if_pos rfl] at hy'
  exact nextrel1_uniq_src hy' h

/-- ⟹ 塔の言葉で（`mTower_succ` で最後のブロックを切り出す）。 -/
theorem nextrel1_mTower_sameBlock {Q : TrioSeq} {d e n' qa b : ℕ}
    (horph : ¬ hasParent Q 1 b)
    (h : nextrel1 (mTower Q d e (n' + 1))
      ((mTower Q d e n').length + qa) ((mTower Q d e n').length + b)) : False := by
  rw [mTower_succ] at h
  exact nextrel1_lastBlock_absurd horph h

/-! ### 116.1 ⟹ 行 0・行 1・行 2 が揃いました（同ブロックの側）

    **行 0** … `nextrel0_shiftr01` ＋ `nextrel0_Lift1`（行 0 は動かない）
    **行 1** … **上（`nextrel1_Lift1` が無条件なのが鍵）**
    **行 2** … §106 `nextrel2_lastBlock_absurd`

⟹ **どの行でも「最後のブロックの中の親は `Q` の親」**。**`d1` の値に依りません。**

### 116.2 ⟹ `e = 0` の orphan 補題への含意

§100/§102（F1）は `gexp_chain_inversion` ＋ `hasParent_one_of` の対偶で同ブロックを処理したが、
**上の `nextrel1_lastBlock_absurd` のほうが短く、`hd1pos` も要らない。**
⟹ **`e = 0` 版の F1 は「同ブロック ＝ 上」＋「ブロック外 ＝ §87 / §115」で書ける。**

⚠ **ブロック外の側は `gexp` 座標なので、`mTower`/`shTower` への橋渡しが要ります**
（§109 の `le1_mTower_in_block` と同じ手順）。**そこが残りの作業です。** -/

/-! ## 117. ★★★★★★ §108 の `houtc` から `gexp_cone_mir_zero` を外す

§108 は「目標が錐の外なら鎖の途中も錐の外」を **§84 `gexp_cone_mir_zero`（`hd1pos` 必須）**で
出していた。**最後のブロックに限れば、そこは `Q` の中の話に落ちる:**

    **`nextrel1 (A ++ Lift1 (shiftr01 d0 0 Q) d1) (|A|+a) (|A|+b) ↔ nextrel1 Q a b`**
      （`L53.nextrel1_append_right` ＋ `Wset.nextrel1_Lift1` ＋ `Core.nextrel1_shiftr01`。
       **3 本とも無条件**）

⟹ 鎖の 1 歩がブロックの中なら **`nextrel1 Q q' q`** になり、
**「`q'` が `Q` の錐の中なら `q` も錐の中」は `Q` の中の推移律だけ**で出る。
**⟹ `gexp_cone_mir_zero` も `hd1pos` も要らない。** -/

theorem nextrel1_lastBlock_iff {Q A : TrioSeq} {d0' d1' a b : ℕ} :
    nextrel1 (A ++ Lift1 (shiftr01 d0' 0 Q) d1') (A.length + a) (A.length + b)
      ↔ nextrel1 Q a b := by
  rw [L53.nextrel1_append_right, nextrel1_Lift1, nextrel1_shiftr01]

open Classical in
/-- **★★★★★★ 最後のブロックでの `le1` の閉じ込め**（`hd1pos` 不要）。
ブロック外からの 1 歩を止める `hwall` だけを外から受け取る。 -/
theorem le1_lastBlock_in_block {Q A : TrioSeq} {d0' d1' : ℕ}
    (hwall : ∀ (q c : ℕ), q < Q.length → 0 < q → ¬ le1 Q 0 q →
      nextrel1 (A ++ Lift1 (shiftr01 d0' 0 Q) d1') c (A.length + q) → A.length ≤ c) :
    ∀ q, q < Q.length → 0 < q → ¬ le1 Q 0 q → ∀ a,
      Relation.ReflTransGen (nextrel1 (A ++ Lift1 (shiftr01 d0' 0 Q) d1')) a
        (A.length + q) →
      A.length ≤ a := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq hq1 hout a ha
    rcases ha.cases_tail with heq | ⟨c, hc1, hc2⟩
    · omega
    · have hcge : A.length ≤ c := hwall q c hq hq1 hout hc2
      obtain ⟨q', hq'⟩ : ∃ q', c = A.length + q' := ⟨c - A.length, by omega⟩
      subst hq'
      have hQrel : nextrel1 Q q' q := nextrel1_lastBlock_iff.mp hc2
      have hq'lt : q' < q := hQrel.2.2.1
      have houtq' : ¬ le1 Q 0 q' := by
        intro hcone
        exact hout ⟨hcone.1, hQrel.2.1, hcone.2.2.tail hQrel⟩
      rcases Nat.eq_zero_or_pos q' with rfl | hq'pos
      · exact absurd (le1_refl (show 0 < Q.length from by omega)) houtq'
      · exact ih q' hq'lt (by omega) hq'pos houtq' a hc1

/-! ### 117.1 ⟹ §108 との差

    §108 … `gexp` 座標。`houtc` に **`gexp_cone_mir_zero`（`hd1pos` 必須）**
    **§117 … `A ++ ブロック` 座標。`houtc` は `Q` の中の推移律だけ。`hd1pos` 不要**

⟹ **残る入力は `hwall`（ブロック外からの 1 歩を止める）だけ**で、それは

    **`q` が `Q` の錐の中** … §87 `nextrel1_gexp_no_enter`（**`hd1pos` 不要**）
    **`q` が `Q` の錐の外** … **§115 `nextrel1_gexp_no_enter_out'`（`hd1pos` 不要）**

の 2 本で尽きている（どちらも `gexp` 座標なので、そこへの橋渡しが最後の作業）。

⚠ **`hwall` は「錐の外」だけを受け取る形にしてある**（`hout` を引数に取る）ので、
**§115 だけで足ります。§87 は要りません。**

### 117.2 ⛔ §95.1 の射程、R2 の実測で確定

R2 の §R139: **`r` が孤児にならないのは `z = 0 ∧ e ≥ 1` だけ**（そこでは 0.00%、分母 787,320）。

    `z=0` ∧ `e=0`  … 孤児 **47.1〜50.1%**
    `z=1` ∧ `e≥1`  … 孤児 **75.5〜86.0%** ⟹ `snoc_orphan_W` で無料
    `z=1` ∧ `e=0`  … 孤児 **90.1〜94.4%**

**⟹ 私が §105.1 で撤回した見出しの、正確な射程が出ました。**
**⟹ `j = 0` の段の本当の残差は `z = 0 ∧ e ≥ 1` です。**
**⟹ そして `z = 0` では展開の `d1 = 0` が 100%（R2 の (2)）⟹ `shTower` の領域。**
**⟹ §112-§117 で `(TOW)` に移ったのは、まさにこの枝に効きます。** -/

/-! ## 118. ★★★★★ 橋渡し: **§115 を `shTower` の言葉へ**

`shTower M.dropLast e n = mTower M.dropLast e 0 n = gexp M 0 |M.dropLast| e 0 n`
（§112 ＋ §68）。⟹ §115（`hd1pos` 不要の壁）が `shTower` でそのまま使える。 -/

theorem shTower_length (Q : TrioSeq) (e n : ℕ) :
    (shTower Q e n).length = n * Q.length := by
  rw [← mTower_e_zero_eq_shTower, mTower_length]

theorem gexp_zero_eq_shTower {M : TrioSeq} {e n : ℕ} (hM2 : 2 ≤ M.length) :
    gexp M 0 M.dropLast.length e 0 n = shTower M.dropLast e n := by
  have hdl : M.dropLast.length = M.length - 1 := List.length_dropLast
  rw [gexp_zero_eq_mTower (by rw [hdl]; omega), hdl, ← List.dropLast_eq_take,
    mTower_e_zero_eq_shTower]

open Classical in
/-- **★★★★★★ §115 の `shTower` 版**: 錐の外の列にはブロック外から行 1 の親が来ない。 -/
theorem nextrel1_shTower_no_enter_out {M : TrioSeq} {e n' q c : ℕ} (hM2 : 2 ≤ M.length)
    (hq : q < M.dropLast.length)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + e)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hout : ¬ le1 M 0 (0 + q))
    (h : nextrel1 (shTower M.dropLast e (n' + 1))
      c (n' * M.dropLast.length + q)) :
    n' * M.dropLast.length ≤ c := by
  have hdl : M.dropLast.length = M.length - 1 := List.length_dropLast
  have hlen : 0 + M.dropLast.length + 1 = M.length := by rw [hdl]; omega
  have hLb : 0 < M.dropLast.length := by rw [hdl]; omega
  refine nextrel1_gexp_no_enter_out' (M := M) (Lb := M.dropLast.length) (d0 := e)
    (d1 := 0) (n := n' + 1) (k := n') (q := q) (c := c) hlen hLb (by omega) hq
    hd0e hr0 hlp hout ?_
  rw [gexp_zero_eq_shTower hM2, Nat.zero_add]
  exact h

/-! ### 118.1 ⟹ `e = 0` 版の F1 の材料が全部そろいました

    **ブロック外** … **§118（上）**（`shTower` 座標、`hd1pos` 不要）
    **同ブロック** … **§116 `nextrel1_lastBlock_absurd`**（`nextrel1_Lift1` が無条件）
    **鎖の閉じ込め** … **§117 `le1_lastBlock_in_block`**（`hwall` を受け取る形）

⚠ §117 は土台を `A ++ Lift1 (shiftr01 d0' 0 Q) d1'` の形で受ける。
`shTower Q e (n'+1) = shTower Q e n' ++ shiftr01 (n'*e) 0 Q`（`shTower_succ`）で
`shiftr01 (n'*e) 0 Q = Lift1 (shiftr01 (n'*e) 0 Q) 0`（`Lift1_zero`）と読めば一致する。

**⟹ あとは組み立てるだけ。** -/

/-! ## 119. ★★★★★★★ **`e = 0` 版の F1**（`shTower` の孤児補題）

§116（同ブロック）＋ §118（ブロック外）で組み立てる。**`hd1pos` はどこにも出てこない。**
⚠ 行 1 の `hasParent` は **1 歩**の話なので、§117（鎖の反復）は要らない。 -/

open Classical in
theorem shTower_orphan_row1 {M : TrioSeq} {e n' : ℕ} (hM2 : 2 ≤ M.length)
    (hQ2 : 2 ≤ M.dropLast.length)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + e)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hout : ¬ le1 M.dropLast 0 (M.dropLast.length - 1))
    (horph : ¬ hasParent M.dropLast 1 (M.dropLast.length - 1)) :
    ¬ hasParent (shTower M.dropLast e (n' + 1)) 1
      ((shTower M.dropLast e n').length + (M.dropLast.length - 1)) := by
  have hdl : M.dropLast.length = M.length - 1 := List.length_dropLast
  have hlt : M.dropLast.length - 1 < M.dropLast.length := by omega
  have htake : M.take M.dropLast.length = M.dropLast := by
    rw [hdl, ← List.dropLast_eq_take]
  have hiff : le1 M.dropLast 0 (M.dropLast.length - 1)
      ↔ le1 M 0 (M.dropLast.length - 1) := by
    have h := le1_take (X := M) (l := M.dropLast.length) (a := 0)
      (b := M.dropLast.length - 1) (by rw [hdl]; omega) hlt
    rwa [htake] at h
  have houtM : ¬ le1 M 0 (0 + (M.dropLast.length - 1)) := by
    rw [Nat.zero_add]
    exact fun hc => hout (hiff.mpr hc)
  have hAlen : (shTower M.dropLast e n').length = n' * M.dropLast.length :=
    shTower_length _ _ _
  have hdec : shTower M.dropLast e (n' + 1)
      = shTower M.dropLast e n' ++ Lift1 (shiftr01 (n' * e) 0 M.dropLast) 0 := by
    rw [shTower_succ, Lift1_zero]
  rintro ⟨a, ha, -⟩
  have hnr : nextrel1 (shTower M.dropLast e (n' + 1)) a
      ((shTower M.dropLast e n').length + (M.dropLast.length - 1)) := by
    unfold nextR at ha
    rw [if_neg (by omega), if_pos rfl] at ha
    exact ha
  have hge : n' * M.dropLast.length ≤ a := by
    refine nextrel1_shTower_no_enter_out hM2 hlt hd0e hr0 hlp houtM ?_
    rw [← hAlen]
    exact hnr
  have halt : a < (shTower M.dropLast e n').length + (M.dropLast.length - 1) :=
    hnr.2.2.1
  obtain ⟨qa, hqa⟩ : ∃ qa, a = (shTower M.dropLast e n').length + qa :=
    ⟨a - n' * M.dropLast.length, by omega⟩
  subst hqa
  rw [hdec] at hnr
  exact nextrel1_lastBlock_absurd horph hnr

/-! ### 119.1 ⟹ `z = 0` の枝の孤児補題が定理になりました

    §100/§102（F1、`mTower`、**`hd1pos` あり**）… `z = 1` 側の道具
    **§119（F1、`shTower`、`hd1pos` なし）… `z = 0` 側の道具**

**⟹ R2 の「`z = 0` なら展開の `d1 = 0` が 100%」と噛み合います。**
**⟹ `(TOW)` の `(T2)`（孤児の枝）が閉じました。**

⚠ **残るのは `(T1)`（底の snoc）だけ**:

    `shTower Q e n ++ [(entry Q 0 0 + n*e, entry Q 1 0, entry Q 2 0)]`

**§110 `oper_snocRoot` の `e = 0`・土台が塔の場合。次はそこ。** -/

/-! ## 120. ★★★★★ `(T1)` の構造: **足す列の親は「`Q` のブロッカーの像」しかありえない**

`(T1)` は `shTower Q e n ++ [r]`、`r = (entry Q 0 0 + n*e, entry Q 1 0, entry Q 2 0)`。
**`mTower` 側（§91 の (A1)）と決定的に違う点: `r` の行 1 が `entry Q 1 0` ちょうど**
（`mTower` 側は `entry Q 1 0 + e*n` だった）。

**⟹ 塔の根も、どのブロックの根も、行 1 が `entry Q 1 0` で `r` と同じ。**
**⟹ `nextrel1` の狭義増加が破れるので、根は `r` の行 1 の親になれない。** -/

open Classical in
/-- **★★★★★ 塔の根は `r` の行 1 の親になれない**（行 1 が等しいから）。 -/
theorem shTower_snoc_no_root_parent_row1 {Q : TrioSeq} {e n : ℕ} (hQne : Q ≠ []) :
    ¬ nextrel1 (shTower Q e (n + 1)
        ++ [((entry Q 0 0 + (n + 1) * e, entry Q 1 0, entry Q 2 0) : ℕ × ℕ × ℕ)])
      0 (shTower Q e (n + 1)).length := by
  intro h
  have hAlen : 0 < (shTower Q e (n + 1)).length := by
    rw [shTower_length]
    have : 0 < Q.length := List.length_pos_iff.mpr hQne
    have h1 : 0 < n + 1 := by omega
    exact Nat.mul_pos h1 this
  have h0 : entry (shTower Q e (n + 1)
      ++ [((entry Q 0 0 + (n + 1) * e, entry Q 1 0, entry Q 2 0) : ℕ × ℕ × ℕ)]) 1 0
      = entry Q 1 0 := by
    rw [entry_append_left _ _ hAlen, entry_shTower_root hQne]
  have hlast : entry (shTower Q e (n + 1)
      ++ [((entry Q 0 0 + (n + 1) * e, entry Q 1 0, entry Q 2 0) : ℕ × ℕ × ℕ)]) 1
      (shTower Q e (n + 1)).length = entry Q 1 0 := by
    rw [entry_snoc_last]
    rfl
  have hlt := h.2.2.2.1
  rw [h0, hlast] at hlt
  omega

/-! ### 120.1 ⟹ `(T1)` の残差は「`Q` にブロッカーがある」場合だけ

`shTower` ではどのブロックの根も行 1 が `entry Q 1 0`（リフト無し）なので、上と同じ理由で
**どのブロックの根も `r` の行 1 の親になれない。**

⟹ `srow r = 1` のとき、`r` の行 1 の親になれるのは
**行 1 が `entry Q 1 0` より狭義に小さい列** ＝ **`Q` のブロッカーの像**だけである。

    **`Q` にブロッカーが無い**（＝ 非根の列がすべて 行 1 > `entry Q 1 0`）
      ⟹ **`r` は行 1 の孤児 ⟹ `snoc_orphan_W`（§4、緑）で無料**
    **`Q` にブロッカーがある**
      ⟹ **その像が親になりうる ⟹ 残差**

> **⟹ `srow r = 1` のとき、`(T1)` の残差は「`Q` にブロッカーがある」場合ちょうど。**
> **⟹ 断片の残核が**ずっとブロッカーだった**という事実（(δ)、§52、§59.1）と一致する。**

⛔ **射程の限定（R2 §R142 を受けて）**: 上の議論は **`srow r = 1`**、すなわち
**`z = 0` ∧ `v ≥ 1`** のときだけである。**`v = 0` では `r = (…, 0, 0)` で `srow r = 0` になり、
親を決めるのは `nextrel0`（行 0）**なので `nextrel1` の議論はまったく当たらない。
**そこでは根が必ず狭義に浅いので親が存在し、孤児にならない**（R2: `z=0 ∧ v=0` で孤児 **0.00%**）。
**⟹ §123 で別に扱う。**

⚠ R2 の実測（`j = 0` の段、`z=0` ∧ `e=0`）で **孤児が 47.1〜50.1%** なのは、
**約半分の `Q` にブロッカーが無い**ということ。**残り半分が `(T1)` の残差。**

### 120.2 ⟹ `mTower` 側との対比

    **`mTower`（`z=1`）** … `r` の行 1 は `entry Q 1 0 + e*n` ⟹ **ブロックの根より上**
        ⟹ ブロックの根が親になれる（§95.1 の議論）⟹ **孤児にならない**（`e≥1` で 0%）
    **`shTower`（`z=0`）** … `r` の行 1 は `entry Q 1 0` ちょうど ⟹ **根と同じ**
        ⟹ **ブロッカーだけが親になれる** ⟹ ブロッカーが無ければ孤児

**⟹ 2 つの枝で「誰が親になるか」が構造的に違う。`z` の相補性（§105.5）の正体はこれ。** -/

/-! ## 121. ⛔ `snoc_flat_root` の **`srow = 1` 版は無料ではありません**（＝ `(TOW)` そのもの）

R2 の提案（`srow = 1` 版を作れば本丸の 47.6〜62.1% が無料）を、
**`Wtower2.oper_snoc_flat_root` の証明を開いて確かめた。答えは否である。**

`oper_snoc_flat_root` の中身は **`Wtower2.oper_of_srow0_par0`** で、
docstring がその理由を書いている（`Wtower2:2176`）:

> **`i1 = 0`（`d0 = d1 = 0`）かつ `j0 = 0` のときだけコピーが `C` そのものになり、
> `W_flatMap_copies` で無条件に閉じる。他の枝（`j0 ≥ 1`、または `i1 ≥ 1`）は
> コピーが持ち上がる／接頭辞が残るので核のまま。**

**⟹ `srow = 1` では `d0 = entry M 0 last − entry M 0 0 ≥ 1` なので、
コピーは `C` そのものではなく `shiftr01 (k*d0) 0 C` になる。**

**そして `srow = 1` かつ親＝根の展開は、既に `Wtower2.oper_of_srow1_par0`（`:1733`、緑）が
与えている:**

    **`X⟦n⟧ = shTower X.dropLast (entry X 0 (|X|-1) − entry X 0 0) n`**

> **⟹ 「`snoc_flat_root` の `srow = 1` 版」＝「`shTower C d0 n ∈ W u`」＝ `ShiftTowerClosedS`。**
> **⟹ 無料ではなく、`(TOW)` そのもの。R2 の見積もり「47.6〜62.1% が落ちる」は成立しない。**

### 121.1 ⟹ しかも (T1) の場合は**塔の塔**になります

(T1) は `C = shTower Q e n`、`p = r`（行 0 が `entry Q 0 0 + n*e`）。親＝根なら
`d0 = (entry Q 0 0 + n*e) − entry Q 0 0 = n*e` で

    **`(shTower Q e n ++ [r])⟦m⟧ = shTower (shTower Q e n) (n*e) m = shTower Q e (n*m)`**

（ブロックの行 0 オフセットが `0, e, …, (n-1)e` を `n*e` ずつ `m` 回 ⟹ `0, e, …, (nm-1)e`）。

> **⟹ 展開しても同じ族に留まり、`n` が **増える**。`n` の帰納では降りない。**
> **⟹ `(TOW)` が核である理由が、ここに直接見える。**

### 121.2 ★ 一方 `d = 0` の枝は本当に無料です（R2 の導出を Lean に） -/

theorem snoc_orphan_of_flat {Q : TrioSeq} {p : ℕ × ℕ × ℕ} {i : ℕ}
    (hs : ∀ j, 1 ≤ j → j < Q.length → entry Q 0 0 < entry Q 0 j)
    (hp0 : p.1 ≤ entry Q 0 0) :
    ¬ hasParent (Q ++ [p]) i Q.length := by
  rintro ⟨j0, hj0, -⟩
  have hle0 : le0 (Q ++ [p]) j0 Q.length := nextR_le0 hj0
  have hne : j0 ≠ Q.length := by
    have := nextR_index_lt hj0
    omega
  have hlt := rtg0_entry0_lt hle0.2.2 hne
  have hj0lt : j0 < Q.length := by
    have := nextR_index_lt hj0
    omega
  have hleft : entry (Q ++ [p]) 0 j0 = entry Q 0 j0 := entry_append_left _ _ hj0lt
  have hright : entry (Q ++ [p]) 0 Q.length = p.1 := by
    rw [entry_snoc_last]; rfl
  rw [hleft, hright] at hlt
  rcases Nat.eq_zero_or_pos j0 with rfl | hj0pos
  · omega
  · have := hs j0 (by omega) hj0lt
    omega

/-! ### 121.3 ⟹ 帰結

    ✅ **`d = 0`（足す列の行 0 が根と同じ）… 孤児 ⟹ `snoc_orphan_W` で無料**（上、緑）
       R2 の実測「`d = 0` は孤児 100%」の導出が Lean になった
    ⛔ **`srow = 1` かつ親＝根 … `(TOW)` そのもの。無料ではない**
    **⟹ 本丸（`z=0` ∧ `d≥1` ∧ `e≥1`、残差 100%）は、やはり `(TOW)` に帰着する。**

⚠ **R2 に「`srow = 1` 版は無料にならない」と伝えること。**
**`oper_of_srow1_par0` が既にあり、それが `shTower` を返すのが理由。** -/

/-! ## 122. ★★★★★ `(T1)` の残差（ブロッカーあり）は **§111 がそのまま当たります**

§120 より、`(T1)` で `r` の親になれるのは **`Q` のブロッカーの像**だけで、**根ではない**。
⟹ **悪根 `j0 ≥ 1`** ⟹ **§111 `snocRoot_comm_of_inner` が土台を切り分ける。** -/

open Classical in
/-- **★★★★★ `(T1)` の展開: ブロッカーの像より手前は触られない。** -/
theorem oper_towerSnoc_of_blocker {Q : TrioSeq} {e n j0 m : ℕ}
    {r : ℕ × ℕ × ℕ} (hj0lt : j0 < (shTower Q e n).length)
    (hp : hasParent (shTower Q e n ++ [r])
      (srow (shTower Q e n ++ [r]) (shTower Q e n).length)
      (shTower Q e n).length)
    (hpar : parent (shTower Q e n ++ [r])
      (srow (shTower Q e n ++ [r]) (shTower Q e n).length)
      (shTower Q e n).length = j0) :
    (shTower Q e n ++ [r])⟦m⟧
      = (shTower Q e n).take j0 ++ ((shTower Q e n).drop j0 ++ [r])⟦m⟧ :=
  snocRoot_comm_of_inner hj0lt hp hpar

/-! ### 122.1 ⟹ `(T1)` の残差の形

    **前半 `(shTower Q e n).take j0`** … **`Wset.W_take`（無条件）**で `W u`
      （`shTower Q e n ∈ W u` は §113 の帰納法の仮定）
    **後半 `((shTower Q e n).drop j0 ++ [r])⟦m⟧`** … **ブロック `n-1` の接尾辞 ＋ 1 列**の展開

⟹ **`mem_of_oper_mem` で `(T1)` を落とすには、この連結が `W u` にあればよい。**

### 122.2 ⟹ 今日の到達点（`z = 0` の枝）

    ✅ **`d = 0`** … 無料（§121.2 `snoc_orphan_of_flat`）
    ✅ **`Q` にブロッカーが無い** … `r` は孤児 ⟹ `snoc_orphan_W` で無料（§120）
    ✅ **(T2) 孤児の枝** … §119 `shTower_orphan_row1`
    **残差** … **`Q` にブロッカーがある場合の (T1)**
       ⟹ **§122（上）で「前半は触られない」まで来た**
       ⟹ 残るのは **「塔の接頭辞 ＋ 短い塊の展開」の連結**

⚠ **これは `catBlock`（§78/§90）と同じ形だが、後半が `shiftr01 c 0 B` の形ではない**
（`(shTower).drop j0 ++ [r]` の展開なので）。**そこが最後の違い。**

### 122.3 ⚠ `(TOW)` は迂回できないことが 4 方向から確認されました

    §110 `TowerSnocRoot` ＝ `MTowerClosedS`（塔を消しても同じ文）
    §112 `MTowerClosedS0` ＝ `ShiftTowerClosedS`（`z=0` では同一）
    §121 (T1) の**親＝根**の枝も `(TOW)`（塔の塔になり `n` が増える）
    **§122 (T1) の**親＝ブロッカー**の枝は、塔の接頭辞との連結に落ちる**

**⟹ どの方向から入っても「塔（またはその接頭辞）に何かを継ぐ」に戻る。**
**⟹ それが `(TOW)` が半年の核である理由の、構造的な説明である。** -/

/-! ## 123. ★★★★★ `(T1)` の `v = 0` の枝: **`srow r = 0` なので `snoc_flat_root` が当たります**

§120 の射程は `srow r = 1`（＝ `z = 0` ∧ `v ≥ 1`）だった。**`v = 0` では別の枝になる。**

    `r = (entry Q 0 0 + n*e, entry Q 1 0, entry Q 2 0)`
    `z = 0` ⟹ `entry Q 2 0 = 0`、`v = 0` ⟹ `entry Q 1 0 = 0`
    **⟹ `r = (…, 0, 0)` ⟹ `srow r = 0`**（`Trio.lean:81`）

**⟹ 親を決めるのは `nextrel0` ⟹ 根が必ず狭義に浅い ⟹ 親が存在 ⟹ 孤児にならない。**
**（R2 §R142: `z=0 ∧ v=0` で孤児 0.00%、分母 236,196。実測と一致。）** -/

theorem srow_snoc_flat {A : TrioSeq} {d0' v z : ℕ} (hv : v = 0) (hz : z = 0) :
    srow (A ++ [((d0', v, z) : ℕ × ℕ × ℕ)]) A.length = 0 := by
  subst hv
  subst hz
  unfold srow
  rw [entry_snoc_last, entry_snoc_last]
  rfl

/-! ### 123.1 ⟹ `v = 0` の枝は **`snoc_flat_root` の射程**

`Wtower2.snoc_flat_root`（`:2208`）の 3 前提:

    `hsr : srow (C ++ [p]) |C| = 0` … **上（`srow_snoc_flat`）で自動**
    `hbp : parent … = 0`（親 ＝ 根） … **R2 実測 11.11%**（26,244 / 236,196）
    `hpar : hasParent …`            … **孤児 0% なので常に真**

> **⟹ `v = 0` の枝のうち「親 ＝ 根」の 11.11% は、全前提が揃って無料。**
> **⟹ §121 で「`srow = 1` 版は書けない」と判定したが、`srow = 0` の本家はここで効く。**

**残る 88.89% は「親が最後のブロックの内部」**（R2: **ブロック戻り 0 が 100%**、分母 515,052）
⟹ **悪根 `j0 ≥ 1` ⟹ §111 / §122 がそのまま当たる**（前半は触られない）。

### 123.2 ⟹ `(T1)` の完全な地図

    **`z ≥ 1`**（`srow r = 2`）      … 孤児 66〜86% ⟹ `snoc_orphan_W` で無料
    **`z = 0` ∧ `v ≥ 1`**（`srow r = 1`）… **§120**: ブロッカーが無ければ孤児（70.6〜83.3%）
        ブロッカーがあれば **§122**（前半は触られない）
    **`z = 0` ∧ `v = 0`**（`srow r = 0`）… **孤児 0%**。
        **親 ＝ 根 11.11% は `snoc_flat_root` で無料**（上）
        **親が内部 88.89% は §111 / §122**（前半は触られない）
    **`d = 0`** … 全 `z`・全 `v` で孤児 ⟹ 無料（§121.2）

> **⟹ どの枝も「無料」か「§111 で前半を切り離す」かのどちらかになった。**
> **⟹ 残るのは切り離したあとの連結（塔の接頭辞 ＋ 短い塊の展開）1 種類だけ。**

⚠ **`d0` を `e` と置かないこと**（R2: `d0 = e` は `v = 0` でも 44〜67% だけ。
`v ≥ 1` では 0 件。`d0 = e ⟺ j0` がブロック `n-1` の根）。 -/

/-! ## 124. ★★★★★ `v = 0` の残差は **「接頭辞 ＋ 平坦なコピー」** に落ちます

§123 より `v = 0` では `srow r = 0`。⟹ §68 `oper_eq_mTower` の `d0`/`d1` が**両方 0**:

    `d0 = if 0 < srow r then … else 0 = 0`   `d1 = if 1 < srow r then … else 0 = 0`

**⟹ 展開は「同じ塊をそのまま `m` 個並べたもの」になる。** -/

theorem mTower_zero_zero (Q : TrioSeq) (m : ℕ) :
    mTower Q 0 0 m = (List.range m).flatMap fun _ => Q := by
  unfold mTower
  refine List.flatMap_congr ?_
  intro k _
  simp

/-! ### 124.1 ⟹ `v = 0` の (T1) の形

§122 の分解 ＋ 上より（`D := (shTower Q e n).drop j0`、`A := (shTower Q e n).take j0`）:

    `(shTower Q e n ++ [r])⟦m⟧ = A ++ (D を `m` 個並べたもの)`

そして **`A ++ D = shTower Q e n`**（`List.take_append_drop`）で、それは
**§113 の帰納法の仮定で `W u`**。

> **⟹ `v = 0` の残差は「`A ++ D ∈ W u` のとき `A ++ D^m ∈ W u` か」1 文。**

### 124.2 ⚠ そしてそれは **`Wtower2` の docstring が既に核と認定している形**です

`Wtower2:2176`:

> **`i1 = 0`（`d0 = d1 = 0`）かつ `j0 = 0` のときだけコピーが `C` そのものになり、
> `W_flatMap_copies` で無条件に閉じる。他の枝（**`j0 ≥ 1`**、または `i1 ≥ 1`）は
> コピーが持ち上がる／**接頭辞が残る**ので核のまま。**

    **`j0 = 0`** … `A = []` ⟹ **`Wset.W_flatMap_copies`（`:2552`、緑・無条件）で閉じる**
    **`j0 ≥ 1`** … **接頭辞 `A` が残る ⟹ 核のまま**

**⟹ `v = 0` の残差は「`W_flatMap_copies` の接頭辞つき版」ちょうど。**
**⟹ §123 の「親 ＝ 根 11.11% は無料」は、まさに `j0 = 0` の場合である。**

### 124.3 ⚠ `W_add` は使えません（team-lead の警告の確認）

`A` は塔の接頭辞で **`j0 ≥ 1` なら `A[0] = Q[0]` ＝ 塔の根を含む**。
`D` の根は `(shTower).drop j0` の先頭で、**行 0 は根より深い**（根が狭義最浅だから）。
⟹ `rsum A D` は「`D` の根の行 0 ≤ `A ++ D` の全列の行 0」を要求するが、
**`A` の根がそれを破る** ⟹ **`not_rsum_of_root_mem`（§14、緑）そのもの**。

**⟹ `Aop` の節 2（`mem_of_oper_mem`）で降りるしかない。**
**⟹ そして節 2 で降りると `A ++ D^m` の展開になり、また同じ形に戻る（§121 の「塔の塔」と同型）。**

> **⟹ `v = 0` の残差も、`(TOW)` と同じ「接頭辞つきコピー塔」の閉包である。**
> **⟹ (TOW) が迂回不能な理由の 5 方向目。** -/

/-! ## 125. ⛔ `W_flatMap_copies` は **まるごと `W_add`** でした（接頭辞つき版は別証明が要る）

`Wset.W_flatMap_copies`（`:2552`、緑）の証明を開いて、`A = []` の使い所を数えた
（今日の手筋の 5 回目）。**答え: `A = []` は使っていない。使っているのは `W_add` である。**

    `induction n` の `succ` で **`refine W_add ih hQ ?_`**
    側条件 `rsum` は **`hQr : ∀ p ∈ Q, entry Q 0 0 ≤ p.1`**（`Q` の根が `Q` の中で最浅）から出る
    ⟹ **コピーはどれも根が `entry Q 0 0` なので、`rsum` が全部通る**

**⟹ 接頭辞 `A` が付くと `A` の根（塔の根）が `D` の根より浅いので `rsum` が破れる**
（§124.3、`not_rsum_of_root_mem`）。**⟹ `W_add` の道は使えない。**

> **⟹ 「`W_flatMap_copies` の接頭辞つき版」は、既存の証明の一般化では作れない。**
> **⟹ `Aop` の節 2 で降りる別証明が要る。**

### 125.1 ⟹ 節 2 で降りるとどうなるか

`A ++ D^m` の末尾列は最後のコピーの `D` の末尾列。**`D` が段内に親を持てば**
`L53.comm_of_hasParentInBlock` で

    **`(A ++ D^m)⟦m'⟧ = (A ++ D^(m-1)) ++ D⟦m'⟧`**

⟹ **`m` について降り、最後のコピーは `D` の導出に沿って降りる。**
⟹ **これは §90 `catBlock_of_escape_head` の `c = 0` の場合そのもの**（シフト無し）。

    **底** … `A ++ D^(m-1) ++ [D の先頭列]`（`oper_headD` で先頭列は保たれる）
    **孤児の枝** … `D` の導出の途中が段内で孤児のとき

**⟹ 形は §90 と同じで、`c = 0`（シフト無し）なぶん単純。**
**⟹ ただし底がまた「接頭辞 ＋ 1 列」なので、`(T1)` と同じ入れ子に戻る。**

### 125.2 ⚠ ⟹ **5 方向のどれも「接頭辞に何かを継ぐ」に戻る**

    §110 塔を消しても同じ文 ／ §112 `z=0` では同一
    §121 親＝根は**塔の塔**（`n` が増える）
    §122 親＝ブロッカーは**接頭辞との連結**
    §124/§125 `v=0` は**接頭辞つきコピー塔**、その節 2 も**接頭辞 ＋ 1 列**に戻る

> **⟹ この断片の残核は「`W` の元の接頭辞に 1 列足す」——すなわち `WSnoc` の制限版——に
> 集約されている。§78.2 で私が「素直な分解は `WSnoc` に落ちる」と書いたのは、
> 遠回りをしたあとで見ると正しかった。**
> **⚠ ただし §90 で示したとおり、底の列は**決まっている**ので `WSnoc` そのものではない。**
> **「決まった 1 列を塔（またはその接頭辞）に足す」が、いまの断片の残核の姿である。** -/

/-! ## 126. ★★★★★★ F2b の測度: **展開の末尾列は `M` の「1 つ手前」の列**

R2 の §R143（F2b の再帰の深さが `|Q| − 2` で必ず有限）の**測度**を定理にする。

`oper` は `M.take j0 ++（`[j0, j1)` の写し `n` 個）` で `j1 = |M|-1` なので、
**結果の末尾列は最後の写しの末尾 ＝ `M[j1 - 1] = M[|M| - 2]` の像**である。
**行 2 は写しで動かない**（`Lcone.gexp_entry2_mir`）ので、行 2 はそのまま移る。 -/

open Classical in
theorem oper_last_row2 {M : TrioSeq} {n : ℕ} (hL : M.length - 1 ≠ 0)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1)) (hn : 0 < n) :
    entry (M⟦n⟧) 2 ((M⟦n⟧).length - 1) = entry M 2 (M.length - 2) := by
  have hj0lt : parent M (srow M (M.length - 1)) (M.length - 1) < M.length - 1 :=
    nextR_index_lt (parent_nextR hp)
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  set j0 := parent M (srow M (M.length - 1)) (M.length - 1) with hj0
  set Lb := M.length - 1 - j0 with hLbdef
  have hLbpos : 0 < Lb := by rw [hLbdef]; omega
  have hlen : j0 + Lb + 1 = M.length := by rw [hLbdef]; omega
  rw [oper_eq_gexp_gen (n' + 1) hL hz hp]
  have hglen : (gexp M j0 Lb
      (if 0 < srow M (M.length - 1) then entry M 0 (M.length - 1) - entry M 0 j0 else 0)
      (if 1 < srow M (M.length - 1) then entry M 1 (M.length - 1) - entry M 1 j0 else 0)
      (n' + 1)).length = j0 + (n' + 1) * Lb := gexp_length hlen
  rw [hglen]
  have hidx : j0 + (n' + 1) * Lb - 1 = j0 + (n' * Lb + (Lb - 1)) := by
    have h : (n' + 1) * Lb = n' * Lb + Lb := Nat.succ_mul n' Lb
    omega
  rw [hidx, gexp_entry2_mir hlen (by omega) (by omega)]
  congr 1
  omega

/-! ### 126.1 ⟹ これが R2 の「深さ `|Q| − 2`」の測度です

    **展開のたびに、末尾列の出所が `M` の中で 1 つ左へ動く**（`|M|-1 → |M|-2`）
    **行 2 は写しで動かない**（`gexp_entry2_mir`）
    ⟹ **`srow = 2` が続くには、そのつど行 2 > 0 の列が要る**
    ⟹ **`Q` の行 2 > 0 の列を左から使い切ったら終わり ⟹ 深さは `|Q|` で抑えられる**

**⟹ R2 の実測「深さ ＝ `|Q| − 2` にちょうど一致、打ち切り 0 件」の機構である。**

⚠ **R2 の但し書きをそのまま守る:「深さが有限」は「`W` に入る」ではない。**
**`W` の節 2 は全 `m` を要求するので、これは**構造の深さ**であって所属ではない。**
**⟹ 整礎帰納が**組める**ことが分かっただけで、F2b が証明できたわけではない。**

### 126.2 ⟹ そして 57.8% は F1 の領域へ

R2 の実測: 展開の末尾列の `srow` は **1 が 57.8%** ／ 2 が 38.9% ／ 0 が 3.3%。
**⟹ 過半数は `srow = 1` に落ち、`gexp_orphan_row1`（§102、緑）／
`shTower_orphan_row1`（§119、緑）の領域に入る。**
**⟹ F2b の再帰でまた F2b になるのは 28.4% だけ。** -/

/-! ## 127. ★ F2b の整礎帰納: **組めます。足りないのは 1 つだけ**（30 分の判定）

### 127.1 ✅ 測度は取れる（§126）

**`oper_last_row2`（§126、緑）**: `entry (M⟦n⟧) 2 (末尾) = entry M 2 (|M| − 2)`
⟹ **展開のたびに末尾列の出所が `Q` の中で 1 つ左へ動き、行 2 はそのまま移る。**
⟹ **測度は「末尾列の出所の位置 `q`」で、1 段ごとに厳密に減る。**

### 127.2 ✅ 分岐は無限でも構わない（`Aop` の節 2 がそう作られている）

⚠ R2 の但し書き「`W` の節 2 は全 `m` を要求する」は正しいが、**それは障害ではない**:

    `Wchar.mem_of_oper_mem`（`:70`、緑）… **`(∀ m ≥ 1, M⟦m⟧ ∈ W u) → M ∈ W u`**

⟹ **各 `m` について別々に降りればよい。分岐は無限、深さは有限。**
⟹ **`Aop` の節 2 はまさにその形（無限分岐・有限深さ）を許す。**
⟹ **R2 が測った「貪欲な最悪の鎖」は、その木の 1 本の枝の長さ。それが `|Q| − 2` で抑えられる。**

> **⟹ 「測度 `q` についての強帰納 ＋ 各段で `mem_of_oper_mem`」で組めます。**
> **⟹ 無限後退は起きません。R2 の懸念はこの形では問題になりません。**

### 127.3 ⛔ 足りないのは **「途中の対象に無料の補題が当たるか」** 1 つ

各段で `M⟦m⟧` の `srow` を場合分けする:

    **`srow = 0`（3.3%）** … 行 0 の親 ⟹ §121.2 / §86 の領域
    **`srow = 1`（57.8%）** … **F1 の領域**（`gexp_orphan_row1` §102 ／ `shTower_orphan_row1` §119）
    **`srow = 2`（38.9%）** … **測度が 1 減って再帰**（うち F2b は 28.4%）

⚠ **問題はここ**: §102 は **`gexp M 0 Lb d0 d1 n`**（悪根 ＝ **根**）の形を要求する。
**F2b で復活したあとの対象は `gexp T j0 Lb' d0' d1' m` で `j0 ≥ 1`**
（R2: `Lb' > |Q|` が 100% ＝ 写しがブロック境界をまたぐ）。

> **⟹ §102 / §119 は、そのままでは途中の対象に当たらない。**
> **⟹ 足りないのは「悪根が根でない `gexp` に対する F1」＝ `j0 ≥ 1` 版。**

### 127.4 ⟹ 判定

    ✅ **測度**（§126、緑）
    ✅ **帰納の形**（強帰納 ＋ `mem_of_oper_mem`。分岐が無限でも可）
    ⛔ **`j0 ≥ 1` 版の F1**（＝ 途中の対象に無料の補題を当てる）← **これ 1 つ**

**⟹ 「組める」。足りないのは `j0 ≥ 1` 版の F1 1 本。**

⚠ **そして `j0 ≥ 1` では `Lcone.liftInner_holds`（無条件・緑）が効く領域である**（§67）。
**⟹ そこが手がかりになるかもしれない。次はそれを見る。**

⚠ **R2 の但し書きは守る: 上は「組める」であって「通る」ではない。**
**`j0 ≥ 1` 版の F1 が書けるかは、まだ確かめていない。** -/

/-! ## 128. ★★★★★★★ **`j0 ≥ 1` 版の道具は、`j0 = 0` 版より**先に**揃っていた**

§127.3 で「足りないのは `j0 ≥ 1` 版の F1 1 本」と出した。**そこで手筋（開いて数える）を 6 回目。**

    ✅ `Lcone.gexp_entry1_mir` / `Gtrans.gexp_entry_root` / `Gtrans.gexp_chain_inversion`
       … **もともと `j0` は節変数。一般 `j0` で緑。**
    ✅ **`Lcone.gexp_root_shallow`（`:76`）… 前提 `hj0 : 0 < j0`**
    ✅ **`Lcone.gexp_cone_mir`（`:106`）… 前提 `hj0 : 0 < j0`**
    ✅ **`Lcone.gexp_cone_mir_flat`（`:356`）… `hj0` あり、しかも `hd0pos`/`hd0e`/`hlp` なし**

> **⟹ 私が §84 で書いた `gexp_root_shallow_zero` / `gexp_cone_mir_zero` は、
> ライブラリの `j0 ≥ 1` 版が使えなかったから書いた `j0 = 0` の特別扱いだった。**
> **⟹ つまり `j0 ≥ 1` 側は、`j0 = 0` 側より道具が**多い**。**

**⟹ 残るのは私の §86 / §98 / §99 / §102 を `j0` について一般化するだけ。以下でやる。** -/

theorem nextrel0_gexp_no_skip_gen {M : TrioSeq} {j0 Lb d0 d1 n k q y : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hk : k < n) (hq : q < Lb)
    (hq1 : 0 < q)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (h : nextrel0 (gexp M j0 Lb d0 d1 n) y (j0 + (k * Lb + q))) :
    j0 + k * Lb ≤ y := by
  by_contra hc
  have hmin := h.2.2.2.2 (j0 + k * Lb) ⟨by omega, by omega⟩
  rw [show j0 + k * Lb = j0 + (k * Lb + 0) from by omega] at hmin
  rw [gexp_entry0_mir hlen hk hq, gexp_entry0_mir hlen hk hLb] at hmin
  have hlt := hup (j0 + q) (by omega) (by omega)
  simp only [Nat.add_zero] at hmin
  omega

/-- **ブロック外の行 0 祖先は、必ずブロックの根を通る**（§99 の `j0 ≥ 1` 版）。 -/
theorem gexp_anc_through_root_gen {M : TrioSeq} {j0 Lb d0 d1 n k : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hk : k < n)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l) :
    ∀ q, q < Lb → ∀ y,
      Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n)) y (j0 + (k * Lb + q)) →
      y < j0 + k * Lb →
      Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n)) y (j0 + (k * Lb + 0)) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq y hy hylt
    rcases Nat.eq_zero_or_pos q with rfl | hqpos
    · exact hy
    · rcases hy.cases_tail with heq | ⟨c, hc1, hc2⟩
      · omega
      · have hcge : j0 + k * Lb ≤ c :=
          nextrel0_gexp_no_skip_gen hlen hLb hk hq hqpos hup hc2
        have hclt : c < j0 + (k * Lb + q) := nextrel0_index_less hc2
        obtain ⟨q', hq'⟩ : ∃ q', c = j0 + (k * Lb + q') := ⟨c - j0 - k * Lb, by omega⟩
        subst hq'
        exact ih q' (by omega) (by omega) y hc1 hylt

open Classical in
/-- **ブロック `k` の根は塔の（全体の）根の錐に入る**（§98 の `j0 ≥ 1` 版）。
⚠ `j0 = 0` では `le1_refl` で自明だったところが、ここでは前提 `hj0c : le1 M 0 j0` になる。 -/
theorem gexp_blockRoot_cone_gen {M : TrioSeq} {j0 Lb d0 d1 n k : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hj0 : 0 < j0) (hLb : 0 < Lb) (hk : k < n)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hd0pos : 0 < d0) (hd0e : entry M 0 (j0 + Lb) = entry M 0 j0 + d0)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M j0 (j0 + Lb)) (hj0c : le1 M 0 j0) :
    le1 (gexp M j0 Lb d0 d1 n) 0 (j0 + (k * Lb + 0)) := by
  rw [gexp_cone_mir hlen hj0 hLb hk hLb hup hd0pos hd0e hr0 hlp]
  simpa using hj0c

open Classical in
/-- **ブロックの根の行 0 祖先は、行 1 が塔の根より上**（§98 の `j0 ≥ 1` 版）。 -/
theorem gexp_blockRoot_anc_gen {M : TrioSeq} {j0 Lb d0 d1 n k : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hj0 : 0 < j0) (hLb : 0 < Lb) (hk : k < n)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hd0pos : 0 < d0) (hd0e : entry M 0 (j0 + Lb) = entry M 0 j0 + d0)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M j0 (j0 + Lb)) (hj0c : le1 M 0 j0) :
    ∀ y, Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n)) y (j0 + (k * Lb + 0)) →
      y ≠ 0 → entry M 1 0 < entry (gexp M j0 Lb d0 d1 n) 1 y := by
  have hrX := gexp_root_shallow (d0 := d0) (d1 := d1) (n := n) hlen hj0 hLb hr0
  have hbnd : k * Lb + 0 < n * Lb := by
    have h1 : (k + 1) * Lb ≤ n * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
    omega
  have hplt : j0 + (k * Lb + 0) < (gexp M j0 Lb d0 d1 n).length := by
    rw [gexp_length hlen]; omega
  have h10 : entry (gexp M j0 Lb d0 d1 n) 1 0 = entry M 1 0 :=
    gexp_entry_low hlen hj0
  have hall := (le1_zero_iff hrX hplt).mp
    (gexp_blockRoot_cone_gen hlen hj0 hLb hk hup hd0pos hd0e hr0 hlp hj0c)
  intro y hy hy0
  have hres := hall y hy hy0
  rwa [h10] at hres

open Classical in
/-- **ブロック外の行 0 祖先は、行 1 が塔の根より上**（§99 の `j0 ≥ 1` 版）。 -/
theorem gexp_outer_anc_row1_gen {M : TrioSeq} {j0 Lb d0 d1 n k q : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hj0 : 0 < j0) (hLb : 0 < Lb) (hk : k < n)
    (hq : q < Lb)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hd0pos : 0 < d0) (hd0e : entry M 0 (j0 + Lb) = entry M 0 j0 + d0)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M j0 (j0 + Lb)) (hj0c : le1 M 0 j0) :
    ∀ y, Relation.ReflTransGen (nextrel0 (gexp M j0 Lb d0 d1 n)) y (j0 + (k * Lb + q)) →
      y < j0 + k * Lb → y ≠ 0 →
      entry M 1 0 < entry (gexp M j0 Lb d0 d1 n) 1 y := by
  intro y hy hylt hy0
  exact gexp_blockRoot_anc_gen hlen hj0 hLb hk hup hd0pos hd0e hr0 hlp hj0c y
    (gexp_anc_through_root_gen hlen hLb hk hup q hq y hy hylt) hy0

/-! ### 128.1 ⟹ ここまでで §86 / §98 / §99 の `j0 ≥ 1` 版がすべて緑

⚠ **`j0 = 0` 版との違いは 1 つだけ**: 前提に **`hj0c : le1 M 0 j0`**（悪根が全体の根の錐に入る）
が加わった。`j0 = 0` では `le1_refl` で自明だったところである。

**⟹ 残るは §102 の `j0 ≥ 1` 版。そこでは `j0 = 0` になかった枝
「祖先 `a` が接頭辞 `M.take j0` の中」が新しく出る。** -/

/-! ## 129. ★★★★★★★ **F1 の `j0 ≥ 1` 版**（§127.3 で「足りない」と出した 1 本）

⚠ **`j0 = 0` になかった枝「祖先 `a` が接頭辞 `M.take j0` の中」は、
別扱いが要らない。** §128 の `gexp_outer_anc_row1_gen` の条件は `y < j0 + k * Lb` なので、
**接頭辞（`y < j0`）も手前のブロック（`j0 ≤ y < j0 + k*Lb`）も同じ 1 本で片づく。** -/

open Classical in
theorem gexp_orphan_row1_gen {M : TrioSeq} {j0 Lb d0 d1 n k q : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hj0 : 0 < j0) (hLb : 0 < Lb)
    (hk : k < n) (hq : q < Lb) (hq1 : 0 < q)
    (hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l)
    (hd0pos : 0 < d0) (hd0e : entry M 0 (j0 + Lb) = entry M 0 j0 + d0)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M j0 (j0 + Lb)) (hj0c : le1 M 0 j0)
    (hf1 : entry M 1 (j0 + q) ≤ entry M 1 0)
    (horph : ¬ hasParent M 1 (j0 + q)) :
    ¬ hasParent (gexp M j0 Lb d0 d1 n) 1 (j0 + (k * Lb + q)) := by
  have hroot1 : entry M 1 0 < entry M 1 j0 :=
    le1_entry1_lt hj0c (by omega)
  have hout : ¬ le1 M j0 (j0 + q) := by
    intro hc
    have := le1_entry1_lt hc (show j0 ≠ j0 + q from by omega)
    omega
  have hlast1 : entry (gexp M j0 Lb d0 d1 n) 1 (j0 + (k * Lb + q))
      = entry M 1 (j0 + q) := by
    rw [gexp_entry1_mir hlen hk hq, if_neg hout]
    omega
  rintro ⟨a, ha, -⟩
  have hnr : nextrel1 (gexp M j0 Lb d0 d1 n) a (j0 + (k * Lb + q)) := by
    unfold nextR at ha
    rw [if_neg (by omega), if_pos rfl] at ha
    exact ha
  have hlt := hnr.2.2.2.1
  rw [hlast1] at hlt
  have hle0 := hnr.2.2.2.2.1
  by_cases ha0 : a = 0
  · subst ha0
    have h10 : entry (gexp M j0 Lb d0 d1 n) 1 0 = entry M 1 0 :=
      gexp_entry_low hlen hj0
    rw [h10] at hlt
    omega
  · by_cases hain : j0 + k * Lb ≤ a
    · obtain ⟨qa, hqa⟩ : ∃ qa, a = j0 + (k * Lb + qa) := ⟨a - j0 - k * Lb, by omega⟩
      have haltp : a < j0 + (k * Lb + q) := hnr.2.2.1
      have hqalt : qa < q := by omega
      subst hqa
      have hent : entry M 1 (j0 + qa) ≤
          entry (gexp M j0 Lb d0 d1 n) 1 (j0 + (k * Lb + qa)) := by
        rw [gexp_entry1_mir hlen hk (by omega)]
        split_ifs <;> omega
      obtain ⟨k', q', hk', hq', hxe, hcase⟩ :=
        gexp_chain_inversion hlen hk hq hup hd0e _ hle0.2.2 (by omega)
      have hk'e : k' = k := by
        rcases Nat.lt_or_ge k' k with h | h
        · exfalso
          have : k' * Lb + Lb ≤ k * Lb := by
            have h1 : (k' + 1) * Lb ≤ k * Lb := Nat.mul_le_mul_right _ (by omega)
            have h2 : (k' + 1) * Lb = k' * Lb + Lb := Nat.succ_mul k' Lb
            omega
          omega
        · omega
      subst hk'e
      have hq'e : q' = qa := by omega
      have hM : Relation.ReflTransGen (nextrel0 M) (j0 + qa) (j0 + q) := by
        rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
        · rw [hq'e] at h; exact h
        · omega
      exact horph (hasParent_one_of (b := j0 + q) (k := j0 + qa)
        (by omega) (by omega) ⟨by omega, by omega, hM⟩ (by omega))
    · have := gexp_outer_anc_row1_gen hlen hj0 hLb hk hq hup hd0pos hd0e hr0 hlp hj0c a
        hle0.2.2 (by omega) ha0
      omega

/-! ### 129.1 ⟹ §127.3 の「足りない 1 本」が埋まりました

    §127.3 ⛔ **`j0 ≥ 1` 版の F1** ← **これ 1 つ**
    §129   ✅ **`gexp_orphan_row1_gen`（緑）**

**⟹ F2b の整礎帰納の途中の対象（`gexp T j0 …`, `j0 ≥ 1`）にも F1 が当たる。**

⚠ **`j0 = 0` 版との差は前提 2 つだけ**:

    **`hj0c : le1 M 0 j0`** … **悪根が全体の根の錐に入る**（`j0 = 0` では `le1_refl`）
    **`hd0pos : 0 < d0`** … `j0 = 0` 版では `hr0` から導けていた（§98）

⚠ **教訓 14: これは「F1 が当たる」であって「F2b が通る」ではない。**
残りは **(i) 途中の対象が本当に `gexp T j0 …` の形か**（`oper_eq_gexp_gen` は緑なので形は出る）、
**(ii) `hj0c` と `hd0pos` が各段で成り立つか**、の 2 点。**(ii) は R2 の実測向き。** -/

/-! ## 130. ★★★★★★★ **F2b の 1 段**: 展開そのものに F1 を当てる

§129 は `gexp` の言葉だった。**F2b の帰納で要るのは `M⟦n⟧` の言葉。**
`oper_eq_gexp_gen`（`Lcone:487`、緑）で移すだけだが、**そのとき §129 の前提
`hup` / `hd0pos` / `hd0e` / `hlp` が要る。**

★ **ここで `Aexp.amin_oper_mir`（`:236`、緑）の証明を開いて数えた（手筋 7 回目）。**
**そこでは 4 つとも `hp`（親がある）と `0 < srow` だけから導かれていた:**

    `hrtg : ReflTransGen (nextrel0 M) j0 (j0+Lb)`  … `parent_nextR hp` から
        （`srow = 0` は 1 歩、`= 1` は `.2.2.2.2.1.2.2`、`= 2` は `rtg0_of_rtg1`）
    **`hup`     := `Lcone.window_of_rtg0 hrtg`**      ← **無条件**
    **`hd0pos`  := `hup (j0+Lb)`**                     ← **`0 < srow` だけ**
    **`hd0e`    := `omega`**                           ← **同上**
    **`hlp`     := `hnr` の `srow` 場合分け**          ← **同上**

> **⟹ R2 に測ってもらおうとした (p2)(p3) は、測るまでもなく定理でした。**
> **⟹ 残る外部前提は `hj0c : le1 M 0 j0`（悪根が全体の根の錐に入る）ただ 1 つ。** -/

open Classical in
theorem oper_orphan_row1 {M : TrioSeq} {n j0 Lb k q : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hj0 : 0 < j0)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hj0e : parent M (srow M (M.length - 1)) (M.length - 1) = j0)
    (hsr : 0 < srow M (M.length - 1))
    (hk : k < n) (hq : q < Lb) (hq1 : 0 < q)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hj0c : le1 M 0 j0)
    (hf1 : entry M 1 (j0 + q) ≤ entry M 1 0)
    (horph : ¬ hasParent M 1 (j0 + q)) :
    ¬ hasParent (M⟦n⟧) 1 (j0 + (k * Lb + q)) := by
  have hL : M.length - 1 ≠ 0 := by omega
  have hj1 : M.length - 1 = j0 + Lb := by omega
  have hnr : nextR M (srow M (M.length - 1)) j0 (M.length - 1) := by
    rw [← hj0e]; exact parent_nextR hp
  have hsr2 : srow M (M.length - 1) = 1 ∨ srow M (M.length - 1) = 2 := by
    unfold srow at hsr ⊢; split_ifs at hsr ⊢ <;> omega
  have hrtg : Relation.ReflTransGen (nextrel0 M) j0 (j0 + Lb) := by
    rw [← hj1]
    rcases hsr2 with hs | hs <;> rw [hs] at hnr <;> unfold nextR at hnr
    · rw [if_neg (by omega), if_pos rfl] at hnr
      exact hnr.2.2.2.2.1.2.2
    · rw [if_neg (by omega), if_neg (by omega)] at hnr
      exact rtg0_of_rtg1 hnr.2.2.2.2.1.2.2
  have hup : ∀ l, j0 < l → l ≤ j0 + Lb → entry M 0 j0 < entry M 0 l :=
    window_of_rtg0 hrtg (by omega)
  have hd0pos : 0 < entry M 0 (j0 + Lb) - entry M 0 j0 := by
    have := hup (j0 + Lb) (by omega) (le_refl _); omega
  have hd0e : entry M 0 (j0 + Lb) = entry M 0 j0
      + (entry M 0 (j0 + Lb) - entry M 0 j0) := by omega
  have hle1 : le1 M j0 (j0 + Lb) := by
    rcases hsr2 with hs | hs
    · rw [hs, hj1] at hnr
      unfold nextR at hnr
      rw [if_neg (by omega), if_pos rfl] at hnr
      exact ⟨hnr.1, hnr.2.1, Relation.ReflTransGen.single hnr⟩
    · rw [hs, hj1] at hnr
      unfold nextR at hnr
      rw [if_neg (by omega), if_neg (by omega)] at hnr
      exact hnr.2.2.2.2.1
  have hsr' : 0 < srow M (j0 + Lb) := by rw [← hj1]; exact hsr
  rw [oper_eq_gexp_gen n hL hz hp, hj0e,
    show M.length - 1 - j0 = Lb from by omega, hj1, if_pos hsr']
  exact gexp_orphan_row1_gen hlen hj0 hLb hk hq hq1 hup hd0pos hd0e hr0
    hle1 hj0c hf1 horph

/-! ### 130.1 ⟹ F2b の帰納で使える形になりました

**`M⟦n⟧` の位置 `j0 + (k*Lb + q)` は、`M` の位置 `j0 + q` が行 1 の孤児なら孤児。**

    ✅ **前提はすべて内部で導かれる**（`hup` `hd0pos` `hd0e` `hlp`）
    ⚠ **外から要るのは `hj0c : le1 M 0 j0` 1 つだけ**
    ⚠ **`hr0`（全体の根が最浅）は塔なら `Lcone.gexp_root_shallow` で出る**
    ⚠ **`0 < srow`**（`srow = 0` は §121.2 / §86 の領域なので別扱い）

**⟹ §127.3 の「足りない 1 本」は §129 で埋まり、§130 で `oper` の言葉になりました。**

⚠ **教訓 14**: **これでも F2b は「通った」ではありません。**
残るのは **`hj0c` が F2b の各段で成り立つか**、ただ 1 点です。 -/

/-! ## 131. ★★★★★★★ **F2b の帰納の 1 段、最終列版**

§126 が測度、§130 が仕組み。**両者をつなぐと「末尾列は 1 段ごとに `M` の中を 1 つ左へ動く」
が、行 1 の孤児性についても言える。**

    §126 `oper_last_row2`     … **行 2** が `M[|M|-2]` から移る
    **§131（以下）             … **行 1 の孤児性** も `M[|M|-2]` から移る**

**⟹ 末尾列の出所が `|M|-1 → |M|-2 → …` と左へ動く。これが整礎帰納の 1 段。** -/

open Classical in
theorem oper_last_orphan_row1 {M : TrioSeq} {n j0 Lb : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 1 < Lb) (hj0 : 0 < j0) (hn : 0 < n)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hj0e : parent M (srow M (M.length - 1)) (M.length - 1) = j0)
    (hsr : 0 < srow M (M.length - 1))
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hj0c : le1 M 0 j0)
    (hf1 : entry M 1 (M.length - 2) ≤ entry M 1 0)
    (horph : ¬ hasParent M 1 (M.length - 2)) :
    ¬ hasParent (M⟦n⟧) 1 ((M⟦n⟧).length - 1) := by
  have hL : M.length - 1 ≠ 0 := by omega
  have hlen2 : (M⟦n⟧).length = j0 + n * Lb := by
    rw [oper_eq_gexp_gen n hL hz hp,
      gexp_length (by rw [hj0e]; omega), hj0e,
      show M.length - 1 - j0 = Lb from by omega]
  have hsplit : (n - 1) * Lb + Lb = n * Lb := by
    have h1 : (n - 1 + 1) * Lb = (n - 1) * Lb + Lb := Nat.succ_mul _ _
    have h2 : n - 1 + 1 = n := by omega
    rw [h2] at h1; omega
  have hpos : (M⟦n⟧).length - 1 = j0 + ((n - 1) * Lb + (Lb - 1)) := by omega
  have hsrc : M.length - 2 = j0 + (Lb - 1) := by omega
  rw [hpos]
  rw [hsrc] at hf1 horph
  exact oper_orphan_row1 hlen (by omega) hj0 hz hp hj0e hsr
    (by omega) (by omega) (by omega) hr0 hj0c hf1 horph

/-! ### 131.1 ⟹ 整礎帰納の骨が全部そろいました

    **測度**   §126 `oper_last_row2`（行 2 が `M[|M|-2]` から移る）
    **1 段**   §131 `oper_last_orphan_row1`（**行 1 の孤児性**も `M[|M|-2]` から移る）
    **停止**   `srow ≤ 1` に落ちたら §102 / §119 / §121.2 の緑へ
    **外部前提** **`hj0c : le1 M 0 j0` ただ 1 つ**

⚠ **教訓 14 を守ります。** 上は **「1 段が書ける」**であって、
**「`W` に入る」ではありません。** 各段で

    **(α)** `hj0c` が成り立つか（**R2 に (p1) として実測を依頼中**）
    **(β)** 孤児になった末尾列から `snoc_orphan_W` で本当に無料になるか

の 2 点が残ります。**(β) は既存の緑（`snoc_orphan_W`）なので、実質は (α) 1 つです。** -/

/-! ## 132. ★★★★★★★ **展開の末尾列の `srow` は `M[|M|-2]` で決まる**

§126 は行 2 だけだった。**行 1 も足すと `srow` が決まり、R2 の「57.8% が F1 に落ちる」が
Lean の場合分けになる。**

    行 2 … §126 `oper_last_row2`（**等号**）
    行 1 … 以下 `oper_last_row1_ge`（**`≥`**。リフトで増えることはあっても減らない）

**⟹ `entry M 2 (|M|-2) = 0` かつ `0 < entry M 1 (|M|-2)` なら `srow = 1`。** -/

open Classical in
theorem oper_last_row1_ge {M : TrioSeq} {n j0 Lb : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 1 < Lb) (hn : 0 < n)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hj0e : parent M (srow M (M.length - 1)) (M.length - 1) = j0) :
    entry M 1 (M.length - 2) ≤ entry (M⟦n⟧) 1 ((M⟦n⟧).length - 1) := by
  have hL : M.length - 1 ≠ 0 := by omega
  have hG : M⟦n⟧ = gexp M j0 Lb
      (if 0 < srow M (M.length - 1) then entry M 0 (M.length - 1) - entry M 0 j0
        else 0)
      (if 1 < srow M (M.length - 1) then entry M 1 (M.length - 1) - entry M 1 j0
        else 0) n := by
    rw [oper_eq_gexp_gen n hL hz hp, hj0e,
      show M.length - 1 - j0 = Lb from by omega]
  have hlen2 : (M⟦n⟧).length = j0 + n * Lb := by
    rw [hG, gexp_length hlen]
  have hsplit : (n - 1) * Lb + Lb = n * Lb := by
    have h1 : (n - 1 + 1) * Lb = (n - 1) * Lb + Lb := Nat.succ_mul _ _
    have h2 : n - 1 + 1 = n := by omega
    rw [h2] at h1; omega
  have hpos : (M⟦n⟧).length - 1 = j0 + ((n - 1) * Lb + (Lb - 1)) := by omega
  have hsrc : M.length - 2 = j0 + (Lb - 1) := by omega
  rw [hpos, hG, gexp_entry1_mir hlen (by omega) (show Lb - 1 < Lb from by omega),
    hsrc]
  split_ifs <;> omega

open Classical in
/-- **展開の末尾列が `srow = 1` になる条件は、`M` の最後から 2 番目の列だけで決まる。** -/
theorem oper_last_srow_one {M : TrioSeq} {n j0 Lb : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 1 < Lb) (hn : 0 < n)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hj0e : parent M (srow M (M.length - 1)) (M.length - 1) = j0)
    (h2 : entry M 2 (M.length - 2) = 0) (h1 : 0 < entry M 1 (M.length - 2)) :
    srow (M⟦n⟧) ((M⟦n⟧).length - 1) = 1 := by
  have hr2 := oper_last_row2 (by omega) hz hp hn
  have hr1 := oper_last_row1_ge hlen hLb hn hz hp hj0e
  unfold srow
  rw [if_neg (by omega), if_pos (by omega)]

/-! ### 132.1 ⟹ R2 の 57.8% が Lean の場合分けになりました

**`M` の最後から 2 番目の列 `(x, y, w)` だけを見ればよい:**

    **`w = 0` ∧ `y > 0`** ⟹ **`srow = 1`** ⟹ **§131 で孤児 ⟹ F1 の領域**（R2: 57.8%）
    **`w > 0`**           ⟹ `srow = 2` ⟹ **測度が 1 減って再帰**（R2: 28.4%）
    **`w = 0` ∧ `y = 0`** ⟹ `srow = 0` ⟹ §121.2 / §86 の領域（R2: 3.3%）

**⟹ 三分岐が「実測の割合」から「`M[|M|-2]` の行 2 と行 1 を見る」に変わりました。** -/

/-! ## 133. ★★★★★★★ **F2b の 1 段、`W` の言葉で**

§131（孤児）＋ §132（`srow = 1`）＋ `snoc_orphan_W`（`:144`、緑）を合成する。 -/

open Classical in
theorem oper_mem_of_dropLast {M : TrioSeq} {u n j0 Lb : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 1 < Lb) (hj0 : 0 < j0) (hn : 0 < n)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hj0e : parent M (srow M (M.length - 1)) (M.length - 1) = j0)
    (hsr : 0 < srow M (M.length - 1))
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hj0c : le1 M 0 j0)
    (h2 : entry M 2 (M.length - 2) = 0) (h1 : 0 < entry M 1 (M.length - 2))
    (hf1 : entry M 1 (M.length - 2) ≤ entry M 1 0)
    (horph : ¬ hasParent M 1 (M.length - 2))
    (hC : (M⟦n⟧).dropLast ∈ W u) :
    M⟦n⟧ ∈ W u := by
  have hL : M.length - 1 ≠ 0 := by omega
  have hlen2 : (M⟦n⟧).length = j0 + n * Lb := by
    rw [oper_eq_gexp_gen n hL hz hp,
      gexp_length (by rw [hj0e]; omega), hj0e,
      show M.length - 1 - j0 = Lb from by omega]
  have hmul : Lb ≤ n * Lb := Nat.le_mul_of_pos_left _ hn
  have hne : M⟦n⟧ ≠ [] := by
    intro h
    have h0 : (M⟦n⟧).length = 0 := by rw [h]; rfl
    omega
  have hClen : (M⟦n⟧).dropLast.length = (M⟦n⟧).length - 1 := List.length_dropLast
  have hCne : (M⟦n⟧).dropLast ≠ [] := by
    intro h
    have h0 : (M⟦n⟧).dropLast.length = 0 := by rw [h]; rfl
    omega
  have hEq : (M⟦n⟧).dropLast ++ [(M⟦n⟧).getLast hne] = M⟦n⟧ :=
    List.dropLast_append_getLast hne
  have horph2 : ¬ hasParent (M⟦n⟧)
      (srow (M⟦n⟧) ((M⟦n⟧).length - 1)) ((M⟦n⟧).length - 1) := by
    rw [oper_last_srow_one hlen hLb hn hz hp hj0e h2 h1]
    exact oper_last_orphan_row1 hlen hLb hj0 hn hz hp hj0e hsr hr0 hj0c hf1 horph
  have hres := snoc_orphan_W ((M⟦n⟧).getLast hne) hC hCne
    (by rw [hEq, hClen]; exact horph2)
  rwa [hEq] at hres

/-! ### 133.1 ⟹ **F2b の 1 段が `W` の言葉になりました**

    **`(M⟦n⟧).dropLast ∈ W u` ⟹ `M⟦n⟧ ∈ W u`**

⚠ **そして、ここで (a) と (b) が合流します。**
`hC : (M⟦n⟧).dropLast ∈ W u` は、**まさに「塔（またはその接頭辞）」が `W` に入ること**です。
**⟹ §110/§112/§121/§122/§124 の 5 方向が集まった「塔に決まった 1 列を足す」の、
「塔の側」がこの前提そのもの。**

> **⟹ F2b は (a) を回避しません。回避しないことが、いま定理として見えました。**
> **⟹ ただし F2b は (a) に**帰着**します。それは「別の壁」ではなく「同じ壁」です。**

⚠ **教訓 14 を守ります。** 残る外部前提は 2 つ:

    **`hj0c : le1 M 0 j0`** … R2 に (p1) として実測を依頼中
    **`hC : (M⟦n⟧).dropLast ∈ W u`** … **(a) そのもの**

**⟹ 今日の到達点は「F2b の残りは (a) と `hj0c` だけ」と、定理の形で言えたことです。** -/

/-! ## 134. ⛔ **`hj0c : le1 M 0 j0` は外せません**（教訓 45: 反例の形を先に書く）

§130/§133 に唯一残った外部前提 `hj0c` について、**「外せるか」を先に確かめる。**
手筋は 教訓 45 のとおり **反例の形を先に書く**:

> **`hj0c` が破れるとは、`le1_zero_iff`（`Lcone:36`）より
> 「悪根 `j0` の非根の行 0 祖先に、行 1 が根以下の列がある」ということ。**
> **その列こそ「ブロッカー」であり、`hasParent` を作る当の相手である。**

**⟹ つまり `¬ hj0c` は「反例がありそう」ではなく「反例の材料が `M` の中に必ずある」。**
以下でそれを定理にする。 -/

open Classical in
theorem badroot_blocker_anc {M : TrioSeq} {j0 Lb : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb) (hj0 : 0 < j0)
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hj0e : parent M (srow M (M.length - 1)) (M.length - 1) = j0)
    (hsr : 0 < srow M (M.length - 1))
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hnc : ¬ le1 M 0 j0) :
    ∃ y, Relation.ReflTransGen (nextrel0 M) y (M.length - 1) ∧ y ≠ 0 ∧
      entry M 1 y ≤ entry M 1 0 := by
  have hj1 : M.length - 1 = j0 + Lb := by omega
  have hnr : nextR M (srow M (M.length - 1)) j0 (M.length - 1) := by
    rw [← hj0e]; exact parent_nextR hp
  have hsr2 : srow M (M.length - 1) = 1 ∨ srow M (M.length - 1) = 2 := by
    unfold srow at hsr ⊢; split_ifs at hsr ⊢ <;> omega
  have hrtg : Relation.ReflTransGen (nextrel0 M) j0 (M.length - 1) := by
    rcases hsr2 with hs | hs <;> rw [hs] at hnr <;> unfold nextR at hnr
    · rw [if_neg (by omega), if_pos rfl] at hnr
      exact hnr.2.2.2.2.1.2.2
    · rw [if_neg (by omega), if_neg (by omega)] at hnr
      exact rtg0_of_rtg1 hnr.2.2.2.2.1.2.2
  obtain ⟨y, hy, hy0, hy1⟩ := (not_le1_zero_iff hr0 (show j0 < M.length from by omega)).mp hnc
  exact ⟨y, hy.trans hrtg, hy0, hy1⟩

/-! ### 134.1 ⟹ 判定: **`hj0c` は証明の都合ではなく、場面そのものの条件**

    **`¬ hj0c`** ⟹ **`M` の末尾列の行 0 祖先に、行 1 が根以下の列 `y` がある**
              ⟹ **それはまさに「末尾列が行 1 で孤児でない」配置の材料**

> **⟹ `hj0c` を落とすと、結論（孤児）が偽になりうる側に入る。**
> **⟹ §129/§130/§131/§133 の `hj0c` は外せません。前提として残します。**

⚠ **教訓 14 を守ります。** 上は **「反例の材料がある」**であって
**「反例がある」ではありません。** `y` が実際に `nextR` の**親**になる（最大性）ところまでは
示していません。**⟹ R2 の (p1) の実測は、その意味でまだ有効です。**

⚠ **そして §133 の `hC : (M⟦n⟧).dropLast ∈ W u` の側は別です。**
そちらは **(a) そのもの**であり、外部前提というより**核**です。

### 134.2 ⟹ 「対象が伸びる」問題の判定（§133 で約束した 1 行）

`X ∈ W u` を `mem_of_oper_mem` で降ろすと `X⟦m⟧ ∈ W u` が要る。**`m = 1` なら
`|X⟦1⟧| = |X| - 1` で短くなるが、`m ≥ 2` では `|X⟦m⟧| = j0 + m*Lb` で伸びる。**
`Aop` の節 2 は **すべての `m ≥ 1`** を要求するので、**伸びる側も必ず現れる。**

> **⟹ 節 2 だけで降り続ける道は、いま手元の道具では閉じません。**
> **⟹ 降下は「すでに `W` に入っていると分かっている、より小さい対象」に着地しないといけない。
> `snoc_orphan_W` がまさにその形で、着地先が `hC`（＝ (a)）です。**

⚠ **これは「原理的に無理」ではなく「手元の道具では届かない」という意味です。**
**節 1（`|M| ≤ 1`）には塔からは届かず、節 3（graft）は主線から外したところです。** -/

/-! ## 135. ⛔ **節 3（graft）は (a) の近道になりません**

§134.2 で「節 2 だけでは降り続けられない。節 1 には塔から届かない」と出した。
**残るのは節 3。そこで `domT` の定義を開いた（手筋 8 回目）:**

    `domT M m := lev M (|M|-1) = m + 1 ∧ **¬ hasParent M (srow M (|M|-1)) (|M|-1)**`

> **⟹ 節 3 は「末尾列が孤児」を要求する。**
> **⟹ ところが末尾列が孤児なら、`snoc_orphan_W`（`:144`、緑）が
> `dropLast ∈ W u` だけで済ませてしまう。**
> **⟹ 節 3 の残り（`∀ z ∈ W m, based z → graft M z ∈ X`）は、それより**強い**要求である。**

**⟹ 節 3 は (a) を弱めない。以下でそれを定理にする。** -/

theorem mem_of_domT_dropLast {u m : ℕ} {M : TrioSeq} (hne : M ≠ [])
    (hCne : M.dropLast ≠ []) (hd : domT M m) (hC : M.dropLast ∈ W u) :
    M ∈ W u := by
  have hEq : M.dropLast ++ [M.getLast hne] = M := List.dropLast_append_getLast hne
  have hClen : M.dropLast.length = M.length - 1 := List.length_dropLast
  have hres := snoc_orphan_W (M.getLast hne) hC hCne
    (by rw [hEq, hClen]; exact hd.2)
  rwa [hEq] at hres

/-! ### 135.1 ⟹ 三つの節すべてについて判定が出ました

    **節 1**（`|M| ≤ 1`）… 塔からは届かない（長さが 2 以上）
    **節 2**（`∀ m ≥ 1, M⟦m⟧ ∈ X`）… §134.2。`m ≥ 2` で対象が伸びるので降り続けられない
    **節 3**（graft）… **上のとおり `domT` が「末尾列が孤児」を含むので、
      `snoc_orphan_W` より弱くならない**

> **⟹ どの節から入っても、着地先は `dropLast ∈ W u` ＝ (a) である。**
> **⟹ §110/§112/§121/§122/§124 の 5 方向に加えて、
> **`Aop` の 3 つの節そのもの**からも同じ点に来ました。合計 8 方向。**

⚠ **これは「原理的に無理」ではありません。** 意味はこうです:

> **`W` に新しく入れるには「すでに `W` に入っている、より短いもの」に着地するしかなく、
> 塔についてはその「より短いもの」が塔から 1 列削ったものである。
> ⟹ 核は「長さについての帰納」に集約されており、その 1 段が (a) である。**

**⟹ (a) は迂回路の問題ではなく、帰納の 1 段そのものです。** -/

/-! ## 136. ★★★★★★ **`take` 不変性**: §102/§129 を snoc の場面につなぐ 1 本

§94 `mTowerClosed_of_snocStep`（緑）が扱う対象は **`塔 ++ (block n).take j`** であり、
これは **完成した塔の接頭辞** `(mTower Q d e (n+1)).take (n*|Q| + j)` である。
**⟹ §102/§129 は「完成した塔」の言葉なので、`take` を跨ぐ必要がある。**

    ✅ `Wset.nextrel0_take` / `nextrel1_take` / `le1_take` … **iff で緑**
    ⛔ **`nextrel2_take` / `nextR_take` / `hasParent_take` … なかった**

**⟹ 以下で埋める。`nextrel1_take` の証明と同じ骨（`le0` を `le1` に、`rtg0_le` を `rtg1_le` に）。** -/

theorem nextrel2_take {X : TrioSeq} {l a b : ℕ} (hl : l ≤ X.length) (hb : b < l) :
    nextrel2 (X.take l) a b ↔ nextrel2 X a b := by
  have hlen : (X.take l).length = l := by rw [List.length_take]; omega
  unfold nextrel2
  rw [hlen]
  constructor
  · rintro ⟨ha, -, hab, hlt, hle, hmin⟩
    refine ⟨by omega, by omega, hab, ?_, (le1_take hl hb).1 hle, ?_⟩
    · rw [entry_take (by omega : a < l), entry_take hb] at hlt; exact hlt
    · intro j hj
      have hjb : j ≤ b := rtg1_le hj.2.2.2
      have hres := hmin j ⟨hj.1, (le1_take hl hb).2 hj.2⟩
      rw [entry_take hb, entry_take (by omega : j < l)] at hres
      exact hres
  · rintro ⟨ha, -, hab, hlt, hle, hmin⟩
    refine ⟨by omega, hb, hab, ?_, (le1_take hl hb).2 hle, ?_⟩
    · rw [entry_take (by omega : a < l), entry_take hb]; exact hlt
    · intro j hj
      have hjb : j ≤ b := rtg1_le ((le1_take hl hb).1 hj.2).2.2
      have hres := hmin j ⟨hj.1, (le1_take hl hb).1 hj.2⟩
      rw [entry_take hb, entry_take (by omega : j < l)]
      exact hres

theorem nextR_take {X : TrioSeq} {l i a b : ℕ} (hl : l ≤ X.length) (hb : b < l) :
    nextR (X.take l) i a b ↔ nextR X i a b := by
  unfold nextR
  split_ifs
  · exact Wset.nextrel0_take hl hb
  · exact nextrel1_take hl hb
  · exact nextrel2_take hl hb

theorem srow_take {X : TrioSeq} {l b : ℕ} (hb : b < l) :
    srow (X.take l) b = srow X b := by
  unfold srow
  rw [entry_take hb, entry_take hb]

theorem hasParent_take {X : TrioSeq} {l i b : ℕ} (hl : l ≤ X.length) (hb : b < l) :
    hasParent (X.take l) i b ↔ hasParent X i b := by
  unfold hasParent
  constructor
  · rintro ⟨a, ha, hu⟩
    exact ⟨a, (nextR_take hl hb).1 ha, fun y hy => hu y ((nextR_take hl hb).2 hy)⟩
  · rintro ⟨a, ha, hu⟩
    exact ⟨a, (nextR_take hl hb).2 ha, fun y hy => hu y ((nextR_take hl hb).1 hy)⟩

/-! ### 136.1 ⟹ これで §94 の `hstep` に §102/§129 が直接当たります

    `塔 ++ (block n).take (j+1)` ＝ `(mTower Q d e (n+1)).take (n*|Q| + j + 1)`
    **`hasParent_take` + `srow_take`** ⟹ **親の有無は完成した塔で判定してよい**
    **⟹ §102 `gexp_orphan_row1`（`k = n`, `q = j`）がそのまま `hstep` の場面の判定になる**

**⟹ §102.1（§102 の直後の設計メモ）が、設計から定理の適用に変わりました。**

⚠ **教訓 14**: これは **「孤児の枝が繋がった」**であって、
**「`hstep` が通った」ではありません。** 残るのは **足す列が親を持つ枝**です。 -/

/-! ## 137. ★★★★★★★ **§94 の `hstep`、孤児の枝**（`take` 不変性で繋いだ）

§136 で `hasParent_take` / `srow_take` が入ったので、
**§102 `gexp_orphan_row1`（完成した塔の言葉）が `hstep` の場面にそのまま当たる。** -/

open Classical in
theorem snocStep_of_orphan {u : ℕ} {M : TrioSeq} {d e n j : ℕ}
    (hM2 : 2 ≤ M.length) (hepos : 0 < e)
    (hd0e : entry M 0 (0 + M.dropLast.length) = entry M 0 0 + d)
    (hr0 : ∀ l, 0 < l → l < M.length → entry M 0 0 < entry M 0 l)
    (hlp : le1 M 0 (0 + M.dropLast.length))
    (hj : j < M.dropLast.length) (hj1 : 0 < j)
    (hf1 : entry M 1 (0 + j) ≤ entry M 1 0)
    (horph : ¬ hasParent M 1 (0 + j))
    (h2 : entry M 2 j = 0) (h1 : 0 < entry M 1 j)
    (hC : mTower M.dropLast d e n
      ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take j ∈ W u) :
    mTower M.dropLast d e n
      ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1) ∈ W u := by
  set Q := M.dropLast with hQ
  set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
  set X := mTower Q d e (n + 1) with hX
  have hdl : Q.length = M.length - 1 := List.length_dropLast
  have hlen : 0 + Q.length + 1 = M.length := by omega
  have hLb : 0 < Q.length := by omega
  have hBlen : B.length = Q.length := by
    rw [hB, Lift1_length, shiftr01_length]
  have hTlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have hXlen : X.length = (n + 1) * Q.length := mTower_length Q d e (n + 1)
  have hXsucc : X = mTower Q d e n ++ B := mTower_succ Q d e n
  have hmul : (n + 1) * Q.length = n * Q.length + Q.length := Nat.succ_mul n Q.length
  have hTake : ∀ t, t ≤ Q.length →
      X.take (n * Q.length + t) = mTower Q d e n ++ B.take t := by
    intro t _
    rw [hXsucc, ← hTlen, List.take_append,
      List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
  have hQt : M.take Q.length = Q := by rw [hdl, hQ, ← List.dropLast_eq_take]
  have hXg : gexp M 0 Q.length d e (n + 1) = X := by
    rw [gexp_zero_eq_mTower (by omega), hQt]
  -- 完成した塔での孤児性（§102）
  have horph2 : ¬ hasParent X 1 (n * Q.length + j) := by
    have h := gexp_orphan_row1 (M := M) (Lb := Q.length) (d0 := d) (d1 := e)
      (n := n + 1) (k := n) (q := j) hlen hLb (by omega) (by omega) hj hj1
      hepos hd0e hr0 hlp hf1 horph
    rw [hXg, Nat.zero_add] at h
    exact h
  -- 完成した塔での `srow`（§132 と同じ二つの成分）
  have he2 : entry X 2 (n * Q.length + j) = 0 := by
    have h := gexp_entry2_mir (M := M) (j0 := 0) (Lb := Q.length) (n := n + 1)
      (k := n) (q := j) hlen (by omega) hj d e
    rw [hXg, Nat.zero_add, Nat.zero_add] at h
    rw [h]; exact h2
  have he1 : 0 < entry X 1 (n * Q.length + j) := by
    have h := gexp_entry1_mir (M := M) (j0 := 0) (Lb := Q.length) (d0 := d) (d1 := e)
      (n := n + 1) (k := n) (q := j) hlen (by omega) hj
    rw [hXg, Nat.zero_add, Nat.zero_add] at h
    rw [h]; split_ifs <;> omega
  have hsrow : srow X (n * Q.length + j) = 1 := by
    unfold srow; rw [if_neg (by omega), if_pos (by omega)]
  -- `take` へ移す（§136）
  have hbnd : n * Q.length + j < n * Q.length + j + 1 := by omega
  have hle : n * Q.length + j + 1 ≤ X.length := by omega
  have hT1 : X.take (n * Q.length + j + 1) = mTower Q d e n ++ B.take (j + 1) :=
    hTake (j + 1) (by omega)
  have hT0 : X.take (n * Q.length + j) = mTower Q d e n ++ B.take j :=
    hTake j (by omega)
  -- 足す 1 列
  have hBt : B.take (j + 1) = B.take j ++ [B.getD j (0, 0, 0)] := by
    rw [List.take_add_one]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have hsplit : mTower Q d e n ++ B.take (j + 1)
      = (mTower Q d e n ++ B.take j) ++ [B.getD j (0, 0, 0)] := by
    rw [hBt, ← List.append_assoc]
  have hCne : mTower Q d e n ++ B.take j ≠ [] := by
    intro h
    have h0 : (mTower Q d e n ++ B.take j).length = 0 := by rw [h]; rfl
    rw [List.length_append, hTlen, List.length_take, hBlen] at h0
    omega
  have hClen : (mTower Q d e n ++ B.take j).length = n * Q.length + j := by
    rw [List.length_append, hTlen, List.length_take, hBlen, Nat.min_eq_left (by omega)]
  rw [hsplit]
  refine snoc_orphan_W _ hC hCne ?_
  rw [hClen, ← hsplit, ← hT1, srow_take hbnd, hsrow, hasParent_take hle hbnd]
  exact horph2

/-! ### 137.1 ⟹ `hstep` の孤児の枝が緑になりました

**足す列 `(block n)[j]` が「`Q` の第 `j` 列が行 1 の孤児」から来ていれば、
塔に足しても無料。** 残る前提は `Q` の第 `j` 列の側だけ:

    `hj1 : 0 < j`（根でない）／ `hf1 : entry M 1 j ≤ entry M 1 0`（行 1 が根以下）
    `horph : ¬ hasParent M 1 j`（`M` の中で行 1 の孤児）
    `h2 : entry M 2 j = 0`（行 2 が 0）／ `h1 : 0 < entry M 1 j`（行 1 が正）

⚠ **教訓 14**: これは **`hstep` の**一つの枝**です。
**残るのは「足す列が親を持つ」枝**で、そこが (a) の本体です。 -/

/-! ## 138. ★★★★★★★ **`hstep` の残りの枝**（足す列が親を持つ）**の姿**

§137 で孤児の枝が閉じた。**残るのは「足す列が親を持つ」枝。**
そこでは `snoc_orphan_W` が使えないので `mem_of_oper_mem` で降りる。
**その展開の姿を、`gexp` の定義（`M.take j0 ++ gcopies …`）から取り出す。** -/

open Classical in
theorem snocStep_oper_prefix {M : TrioSeq} {d e n j p m : ℕ}
    (hj : j < M.dropLast.length) (hpj : p < j)
    (hz : ¬ (entry (mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)) 0
        ((mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)).length - 1) = 0 ∧
      entry (mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)) 1
        ((mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)).length - 1) = 0 ∧
      entry (mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)) 2
        ((mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)).length - 1) = 0))
    (hpar : hasParent (mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
      (srow (mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
        ((mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)).length - 1))
      ((mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)).length - 1))
    (hpe : parent (mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
      (srow (mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))
        ((mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)).length - 1))
      ((mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1)).length - 1)
      = n * M.dropLast.length + p) :
    ∃ C : TrioSeq,
      (mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take (j + 1))⟦m⟧
      = (mTower M.dropLast d e n
        ++ (Lift1 (shiftr01 (d * n) 0 M.dropLast) (e * n)).take p) ++ C := by
  set Q := M.dropLast with hQ
  set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
  set T := mTower Q d e n ++ B.take (j + 1) with hT
  have hdl : Q.length = M.length - 1 := List.length_dropLast
  have hLb : 0 < Q.length := by omega
  have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
  have hTlen : (mTower Q d e n).length = n * Q.length := mTower_length Q d e n
  have hTl : T.length = n * Q.length + (j + 1) := by
    rw [hT, List.length_append, hTlen, List.length_take, hBlen,
      Nat.min_eq_left (by omega)]
  have hL : T.length - 1 ≠ 0 := by omega
  refine ⟨gcopies T (n * Q.length + p) (T.length - 1 - (n * Q.length + p))
    (if 0 < srow T (T.length - 1) then entry T 0 (T.length - 1)
      - entry T 0 (n * Q.length + p) else 0)
    (if 1 < srow T (T.length - 1) then entry T 1 (T.length - 1)
      - entry T 1 (n * Q.length + p) else 0) m, ?_⟩
  rw [oper_eq_gexp_gen m hL hz hpar, hpe]
  unfold gexp
  congr 1
  · rw [hT, List.take_append, ← hTlen, List.take_of_length_le (by omega),
      hTlen, Nat.add_sub_cancel_left, List.take_take, Nat.min_eq_left (by omega)]

/-! ### 138.1 ⟹ 残りの枝の姿が出ました

    **`T_{j+1}⟦m⟧ = T_p ++ （窓 `[p, j]` の `m` 個のコピー）**

**⟹ 接頭辞は `T_p`（`p < j` なので `j` について**厳密に小さい**）。**
**⟹ しかしコピーの側は「部分ブロックの塔」であり、`m` を大きくすると伸びる。**

★ **測度の候補は「窓の長さ `j - p`」である:**

    **`p ≥ 1`** ⟹ 窓 `[p, j]` は**ブロックより短い** ⟹ **`|C|` が厳密に減る** ⟹ 整礎
    **`p = 0`** ⟹ 窓 ＝ **ブロック全体** ⟹ **減らない**
        （§121 の「親＝根は**塔の塔**（`n → n·m`）」がまさにこれ）

> **⟹ 残りの枝は `p ≥ 1` と `p = 0` に割れ、`p ≥ 1` 側には整礎測度がある。**
> **⟹ `p = 0`（親がブロックの根）だけが、測度の候補をもたない。**

⚠ **教訓 14**: 上は **「`p ≥ 1` 側に測度の候補がある」**であって、
**「`p ≥ 1` 側が通る」ではありません。**
**⟹ R2 に「`p = 0` が何 % か」を測ってもらうのが、いちばん効きます。** -/

/-! ## 139. ★★★★★★★ **核を「親を持つ列」だけに絞る**

§94 `mTowerClosed_of_snocStep` は **すべての** `j` について 1 列足すことを要求していた。
**だが孤児の場合は `snoc_orphan_W`（`:144`、緑）が**前提なしで**片づける。**

> **⟹ §137 のような前提（`hf1` / `horph` / `h2` / `h1`）は、
> 「孤児であることを**示す**ため」に要っただけで、
> **場合分けにすれば要らない。****

**⟹ 核は「足す列が親を持つとき」だけになる。** -/

open Classical in
theorem mTowerClosed_of_snocStepPar {u : ℕ} {Q : TrioSeq} {d e : ℕ}
    (hstep : ∀ (n j : ℕ), j < Q.length →
      (hasParent (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
          (srow (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1))
            (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length)
          (mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j).length
        ∨ mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j = []) →
      mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take j ∈ W u →
      mTower Q d e n ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1) ∈ W u) :
    ∀ n, mTower Q d e n ∈ W u := by
  refine mTowerClosed_of_snocStep ?_
  intro n j hj hC
  set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
  have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
  have hBt : B.take (j + 1) = B.take j ++ [B.getD j (0, 0, 0)] := by
    rw [List.take_add_one]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have hsplit : mTower Q d e n ++ B.take (j + 1)
      = (mTower Q d e n ++ B.take j) ++ [B.getD j (0, 0, 0)] := by
    rw [hBt, ← List.append_assoc]
  by_cases hE : mTower Q d e n ++ B.take j = []
  · exact hstep n j hj (Or.inr hE) hC
  · by_cases hP : hasParent (mTower Q d e n ++ B.take (j + 1))
        (srow (mTower Q d e n ++ B.take (j + 1))
          (mTower Q d e n ++ B.take j).length)
        (mTower Q d e n ++ B.take j).length
    · exact hstep n j hj (Or.inl hP) hC
    · rw [hsplit]
      exact snoc_orphan_W _ hC hE (by rw [← hsplit]; exact hP)

/-! ### 139.1 ⟹ 核が 1 段小さくなりました

    §94  … **すべての** `j` について「塔に 1 列足す」
    **§139 … **足す列が親を持つ** `j` についてだけ「塔に 1 列足す」**

**⟹ §137 で入れた 5 つの前提（`hf1` / `horph` / `h2` / `h1` / `0 < j`）は、
場合分けにすれば**要りません**でした。**

⚠ **これは §137 が無駄だったという意味ではありません。**
§137 は **「`Q` の孤児が塔でも孤児」**という**内容のある**定理で、
§136 の `take` 不変性とあわせて **(T1) の道具**として残ります。
**ここで消えたのは「核の前提」であって「定理」ではありません。**

### 139.2 ⟹ そして §138 とつなぐと、核は 1 行になります

    **足す列が親を持つ ⟹ `T_{j+1}⟦m⟧ = T_p ++ （窓 `[p, j]` の `m` 個のコピー）**（§138、緑）
    **`p ≥ 1`** ⟹ 窓がブロックより短い ⟹ **測度あり**
    **`p = 0`** ⟹ 窓 ＝ ブロック全体 ⟹ **測度なし**（§121 の「塔の塔」）

⚠ **正確には 3 分岐です**（§138 の `hpe` は「親が同じブロックの中」を仮定しています）:

    **(i)** 孤児 … §139 で場合分けにより消える
    **(ii)** 親が**同じブロック**の位置 `p`（**`p = 0` を含む**）
        ⟹ 新しい窓の長さは `j - p ≤ j ≤ |Q| - 1 < |Q|` ⟹ **測度が厳密に減る**
    **(iii)** 親が**手前のブロック**（または接頭辞）
        ⟹ 新しい窓は**ブロックより長い** ⟹ **測度なし**
        （R2 の「`Lb' > |Q|` が 100%」＝ **復活**。§121 の塔の塔と同じ姿）

⚠⚠ **自己訂正**: 私は最初 `p = 0`（親＝ブロックの根）を (iii) に入れていたが、**誤り**である。
**窓の長さは `j - p` であって `|Q|` ではない。`p = 0` でも `j < |Q|` なので減る。**
**⟹ `p = 0` は (ii) 側。核は「復活」だけ。**

> **⟹ 核 ＝ (iii)「親が手前のブロックにある列（＝復活）を、塔に足す」。**

⚠ **教訓 14**: これは **核の姿**であって、**核が解けたのではありません。** -/

/-! ## 140. ⛔ **(ii) の整礎帰納は、単独では組む意味がありません**（1 行の判定）

§139.2 の (ii) には測度がある。**では (ii) だけ先に組めるか。** 答えは **否**である。

`A ++ gcopies T j0 Lb' d0 d1 m` を右から 1 列ずつ剥がすと、**各段で同じ 3 分岐が再び出る。**

    **(i)** で止まる／**(ii)** で窓が縮む／**(iii)** で窓が伸びる

> **⟹ 窓の長さについての強帰納は、「(iii) を一度も踏まない導出」に限ってのみ整礎。**
> **⟹ (iii) は各段で起こりうる（R2 の実測どおり復活は普通に起きる）。**
> **⟹ (ii) の帰納を単独で組んでも、(iii) が解けるまで一歩も進まない。**

**⟹ 判定: (ii) は独立した宿題ではない。(iii) が解ければ同時に閉じる。**
**⟹ 手を (iii)（復活）に集中させます。**

⚠ **これは「(ii) が無意味」ではなく「(ii) の証明を先に書いても得がない」という意味です。**
**測度が (ii) にあるという事実（§138）は、(iii) を解いたあと**そのまま**使えます。** -/

/-! ## 141. ★★★★★★★ **復活は「ブロックの中で孤児」のときにしか起きない**

§140 で「核は (iii) の復活だけ」と出した。**では復活はいつ起きるか。**
`Wset.nextR_src_ge`（`:2573`、緑、**前提なし**）と §101 `parent_ge_of_inner` が答える:

> **「接頭辞は、ブロック自身が親を持つときは `nextR` の前身を供給できない」**

**⟹ 足す列が**自分のブロックの中で**親を持つなら、塔全体でも親は同じブロックの中。**
**⟹ 復活が起きるのは、足す列が**自分のブロックの中では孤児**のときだけ。** -/

open Classical in
theorem snocStep_parent_sameBlock {Q : TrioSeq} {d e n j i : ℕ}
    (hj : j < Q.length)
    (hloc : hasParent ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) i j)
    (hp : hasParent (mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) i
      ((mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1)) :
    n * Q.length ≤ parent (mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) i
      ((mTower Q d e n
        ++ (Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)).length - 1) := by
  set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
  have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
  have hTlen : (B.take (j + 1)).length = j + 1 := by
    rw [List.length_take, hBlen]; omega
  have hTne : B.take (j + 1) ≠ [] := by
    intro h
    have h0 : (B.take (j + 1)).length = 0 := by rw [h]; rfl
    omega
  have hloc' : hasParent (B.take (j + 1)) i ((B.take (j + 1)).length - 1) := by
    rw [hTlen]; simpa using hloc
  have hres := parent_ge_of_inner (A := mTower Q d e n) hTne hloc' (parent_nextR hp)
  rwa [mTower_length] at hres

/-! ### 141.1 ⟹ **核が「ブロックの中で孤児な列」に絞れました**

    **足す列がブロックの中で親を持つ** ⟹ 塔でも親は同じブロック ⟹ **(ii)、測度あり**
    **足す列がブロックの中で孤児**     ⟹ **(i) 塔でも孤児（無料）** か **(iii) 復活**

> **⟹ 核 ＝「`Q` の中で孤児な列が、塔では親を持つ」場合だけ。**

★ **そしてその「親」は、鎖の上にある**ブロックの根**しかありえない**（§86 `nextrel0_gexp_no_skip`
＋ §99 `gexp_anc_through_root`: ブロック外の行 0 祖先は必ずブロックの根を通る）。
**⟹ 候補は `n+1` 個のブロック根だけ。**

⚠ **教訓 14**: 「候補が絞れた」であって「解けた」ではありません。

### 141.2 ⟹ ここから見える形（R2 に測ってもらう価値がある）

ブロック `k` の根の行 1 は **`entry Q 1 0 + e*k`**（根は錐の中なのでリフトされる）。
足す列（ブロック `n`、位置 `j`）の行 1 は **`entry Q 1 j + (if le1 Q 0 j then e*n else 0)`**。

    **`le1 Q 0 j`（錐の中、`j ≠ 0`）** ⟹ `entry Q 1 0 < entry Q 1 j`（`le1_entry1_lt`）
        ⟹ **ブロック `n` 自身の根が候補** ⟹ **親は同じブロック ⟹ (ii)**
    **錐の外で `entry Q 1 j ≤ entry Q 1 0`** ⟹ **§102 で塔でも孤児 ⟹ (i) 無料**
    **錐の外で `entry Q 1 0 < entry Q 1 j`** ⟹ リフトなし ⟹ 行 1 は `entry Q 1 j` のまま
        ⟹ **`entry Q 1 0 + e*n` がそれを越えると、ブロック `n` の根は候補でなくなる**
        ⟹ **手前のブロックの根が親 ＝ 復活**

> **⟹ 復活の候補は「`Q` の錐の外で、行 1 が根より上の列」だけ。**

⚠ **これは設計であって証明ではありません。**（`le1 Q 0 j` から (ii) を出すには
「ブロック `n` の根が行 0 祖先である」も要る。§79 `le0_zero_of_shallow` の領域。） -/

/-! ## 142. ★★★★★★★ **錐の中の列は、必ずブロックの中に親を持つ**（§141.2 の設計を定理に）

§141 で「復活はブロックの中で孤児のときだけ」と出た。
**では `Q` の錐の中の列はどうか。ブロックの根の行 1 は `entry Q 1 0 + e*n`、
錐の中の列の行 1 は `entry Q 1 j + e*n` で、`le1_entry1_lt` より前者が狭義に小さい。**
**⟹ ブロックの根が行 1 の候補親になる ⟹ ブロックの中に親がある ⟹ §141 で同ブロック。** -/

open Classical in
theorem block_blockParent_of_row1 {Q : TrioSeq} {d e n j : ℕ}
    (hj : j < Q.length) (hj1 : 0 < j)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hrow1 : entry Q 1 0 + e * n
      < entry Q 1 j + (if le1 Q 0 j then e * n else 0)) :
    hasParent ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 1 j := by
  set B := Lift1 (shiftr01 (d * n) 0 Q) (e * n) with hB
  set T := B.take (j + 1) with hT
  have hBlen : B.length = Q.length := by rw [hB, Lift1_length, shiftr01_length]
  have hTlen : T.length = j + 1 := by rw [hT, List.length_take, hBlen]; omega
  have hE0 : ∀ x, x < Q.length → entry B 0 x = entry Q 0 x + d * n := by
    intro x hx
    show (B.getD x (0, 0, 0)).1 = _
    rw [hB, block_getD hx]
  have hE1 : ∀ x, x < Q.length →
      entry B 1 x = entry Q 1 x + (if le1 Q 0 x then e * n else 0) := by
    intro x hx
    show (B.getD x (0, 0, 0)).2.1 = _
    rw [hB, block_getD hx]
  have hTE : ∀ i x, x < j + 1 → entry T i x = entry B i x := by
    intro i x hx
    exact Wset.entry_take (X := B) (l := j + 1) (i := i) (j := x) hx
  have hshal : ∀ l, 1 ≤ l → l < T.length → entry T 0 0 < entry T 0 l := by
    intro l hl0 hl1
    rw [hTlen] at hl1
    rw [hTE 0 0 (by omega), hTE 0 l (by omega), hE0 0 (by omega),
      hE0 l (by omega)]
    have := hr0 l (by omega) (by omega)
    omega
  have hle0 : le0 T 0 j := le0_zero_of_shallow hshal (by omega)
  have hrefl : le1 Q 0 0 := le1_refl (by omega)
  have hk2 : entry T 1 0 < entry T 1 j := by
    rw [hTE 1 0 (by omega), hTE 1 j (by omega), hE1 0 (by omega),
      hE1 j (by omega), if_pos hrefl]
    exact hrow1
  exact hasParent_one_of (by omega) (by omega) hle0 hk2

/-! ### 142.1 ⟹ 錐の中の列は復活しません

`le1 Q 0 j`（`j ≠ 0`）なら `le1_entry1_lt` より **`entry Q 1 0 < entry Q 1 j`**、
よって `entry Q 1 0 + e*n < entry Q 1 j + e*n` ⟹ **上の `hrow1` が成り立つ。** -/

open Classical in
theorem block_blockParent_of_cone {Q : TrioSeq} {d e n j : ℕ}
    (hj : j < Q.length) (hj1 : 0 < j)
    (hr0 : ∀ l, 0 < l → l < Q.length → entry Q 0 0 < entry Q 0 l)
    (hcone : le1 Q 0 j) :
    hasParent ((Lift1 (shiftr01 (d * n) 0 Q) (e * n)).take (j + 1)) 1 j := by
  have h1 : entry Q 1 0 < entry Q 1 j := le1_entry1_lt hcone (by omega)
  refine block_blockParent_of_row1 (d := d) hj hj1 hr0 ?_
  rw [if_pos hcone]
  omega

/-! ### 142.2 ⟹ **核が「錐の外で、行 1 が高い列」に絞れました**

    **錐の中（`le1 Q 0 j`, `j ≠ 0`）** ⟹ §142 でブロック内に親 ⟹ §141 で同ブロック ⟹ **(ii)**
    **錐の外で `entry Q 1 j ≤ entry Q 1 0`** ⟹ §102 / §137 で塔でも孤児 ⟹ **(i) 無料**
    **錐の外で `entry Q 1 0 < entry Q 1 j ≤ entry Q 1 0 + e*n`**
        ⟹ ブロックの根は候補でない ⟹ **(iii) 復活しうる ← 核**

> **⟹ 核 ＝「`Q` の錐の外にあり、行 1 が根より上だが `e*n` ぶんの持ち上げには届かない列」。**
> **⟹ しかも `n` が大きいほどこの帯は広い。`n` に依存する核である。**

⚠ **教訓 14**: 上の 3 分割は **`srow = 1` の話**です。
**`srow = 2`（F2b）と `srow = 0` は別の場合分けが要ります。**
**`srow = 0` は §79 `hasParentInBlock_of_srow_zero`（緑）で必ずブロック内に親をもつので (ii)。
残るのは `srow = 2`。** -/

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
