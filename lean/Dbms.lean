/-
DBMS（Dimensional BMS）の 2 行版と、BMS -> DBMS の変換関数。

BMS と DBMS は**展開規則が完全に同一**で、違うのは標準形の対角だけ。

    対角 diag[x][y]     BMS: x        DBMS: max(x-y, 0)

2 行なら BMS の対角は (0,0)(1,1)(2,2)... 、DBMS の対角は (0,0)(1,0)(2,1)(3,2)... 。
行 y は位置 y からしか立ち上がれないので、DBMS の列は段を 1 つずつしか上げられない。

範囲は ψ_0(Ω_ω) 未満、すなわち **2 行 BMS の全体**。

## この版の要点（2026-08-24）

変換は、`Pair/Term.lean` の `translate` と**まったく同じ形の 2 分岐の構造再帰**
`convD` で書ける（親子関係も影の管理も要らない）。読み `readD` も `translate` に
**節を 1 つ足しただけ**である:

> ブロックの先頭 `p` の段が親の段と同じで、次の列がちょうど `p + (1,1)` なら、
> `p` は段を 1 つ上げるための**影**である。捨てて次の列から読み直す。

主定理:

    readD_conv_ST : ST_PS M → readD (conv M) true 0 = translate M

仮定なし（BMS 2 行標準形であることだけ）。途中で要る 3 条件

    blockok 0 M   BMS 側のブロック規律      … Pair/Seqlex.lean の blockok_ST_PS
    colOK M       どの列も 行1 ≤ 行0        … colOK_ST_PS（本ファイル、展開で保存）
    descOK M      同じ深さの後続で段が増えない … descOK_ST_PS（Pair/Cnf.lean の cnf から）

はいずれも標準形なら自動で成り立つ。系として

    conv_olt_iff_seqlex : readD (conv M) <o readD (conv N) ↔ seqlex M N
    conv_injective      : conv M = conv N → M = N

つまり **`conv` は 2 行 BMS 標準形の上で順序を保ち単射で、項（順序数）を保つ**。

## 縮約つきの `conC` / `readC`（定義のみ、定理はまだ）

`conv M` は DBMS の**標準形とは限らない**。BMS 2 行標準形 44653 個（≤8 列）のうち
**120 個**で像が非標準になる（`(0,0)(1,1)(1,0)(2,1)(2,0)` 型。DBMS 側では
梯子が二役を兼ねて縮む）。これを入れたのが `conC` / `readC`:

| | `conv` | `conC` |
|---|---|---|
| シート 264 件に一致 | 245 | **264** |
| 像が DBMS 標準形（≤8 列 44653 個） | 120 個が非標準 | **全部標準** |
| `読み (変換 M) = translate M` | **定理**（本ファイル） | 全数検査のみ |

`DbmsConv.lean` に 264 件の `conC A = E` と `readC E = translate A` の #guard。

## 残る穴

`conC` は DBMS 標準形 ≤6 列（358 個）には**全単射**だが、7 列で **6 個**外れる:

    DBMS 標準形  (0,0)(1,0)(2,1)(3,2)(2,1)(3,1)(2,0)   ← 逆像が無い
    conC の像    (0,0)(1,0)(2,1)(3,2)(2,1)(3,1)(1,0)

この 2 つは `readC` でも同じ項に読まれる（`readC` は DBMS 標準形の上では単射でない）。
まだ機構が足りないのか、それとも DBMS 2 行が BMS 2 行より真に細かいのかが未決。
`conC` 自身は ord の定義から来る共終性の検査（`tools/dbms/cofinal_check.py`）を
BMS 2 行標準形 7256 個（≤7 列）で 1 件も落とさない。

展開 `oper`・親子関係は `Pair/Pss.lean`（YAPSS 名前空間）のものをそのまま使う。
-/
import Pair.Pss
import Pair.Term
import Pair.Seqlex

namespace DBMS

open YAPSS

/-! ## 1. DBMS の標準形（2 行） -/

/-- DBMS の 2 行対角の第 `j` 列 `(j, j-1)`（ℕ の切り捨て引き算なので `j = 0` は `(0,0)`）。 -/
def dcol (j : ℕ) : ℕ × ℕ := (j, j - 1)

/-- DBMS の 2 行対角 `(0,0)(1,0)(2,1)…(v,v-1)`。 -/
def ddiagSeq (v : ℕ) : PairSeq := (List.range (v + 1)).map dcol

/-- DBMS の標準形: 対角から展開 `M⟦n⟧`（`n ≥ 1`）で到達できるもの。
展開 `oper` は BMS と同一のものを使う。 -/
inductive ST_D : PairSeq → Prop where
  | diag (v : ℕ) : ST_D (ddiagSeq v)
  | oper {M : PairSeq} {n : ℕ} : ST_D M → 1 ≤ n → ST_D (M⟦n⟧)

/-! ## 2. DBMS の読み `readD`

`Pair/Term.lean` の `translate` は「行 1 = 添字、行 0 = 森」で BMS の行列を項に読む。
DBMS の読みはそれに**節を 1 つ足しただけ**:

> ブロックの先頭 `p` の段が親の段と同じで、次の列がちょうど `p + (1,1)` なら、
> `p` は段を 1 つ上げるための**影**である。捨てて次の列から読み直す。

`first` は「そのブロックの先頭か」、`plev` は「親の段」。 -/

open Three in
def readD (l : PairSeq) (first : Bool) (plev : ℕ) : Three :=
  match l with
  | [] => Z
  | p :: r =>
      if first = true ∧ p.2 = plev ∧ r.headI = (p.1 + 1, p.2 + 1) then
        readD r true plev
      else
        P p.2 (readD (r.takeWhile fun q => p.1 < q.1) true p.2)
              (readD (r.dropWhile fun q => p.1 < q.1) false p.2)
  termination_by l.length
  decreasing_by
  · simp only [List.length_cons]; omega
  · exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ r)

/-! ## 3. 変換 `convD`

`translate` と同じ引数／後続の 2 分岐で、BMS の列 1 本を DBMS の 1 本か 2 本に写す。

* `d` はいま書いている DBMS 側のブロックの深さ、`plev` は親の段
* `lad`（梯子）: 段が親の +1 で、その深さでは段 `s` を直接書けない（`d ≤ s`）か、
  親の列が影と読まれてしまう（`force`）とき。影 `(d, plev)` を先に置く
* `force`: 「親の列が影と読まれる危険があるので、影の形で書け」という指示 -/

/-- 影の列を挿すか。 -/
def ladOf (s d plev : ℕ) (first force : Bool) : Bool :=
  first && (s == plev + 1) && (decide (d ≤ s) || force)

/-- 本体の列の深さ。 -/
def ddOf (s d plev : ℕ) (first force : Bool) : ℕ :=
  if ladOf s d plev first force then d + 1
  else if 0 < s ∧ d ≤ s then s + 1 else d

/-- BMS 2 行 -> DBMS 2 行。 -/
def convD : PairSeq → ℕ → ℕ → Bool → Bool → PairSeq
  | [], _, _, _, _ => []
  | p :: r, d, plev, first, force =>
      (if ladOf p.2 d plev first force then [(d, plev), (d + 1, p.2)]
       else [(ddOf p.2 d plev first force, p.2)])
      ++ convD (r.takeWhile fun q => p.1 < q.1)
           (ddOf p.2 d plev first force + 1) p.2 true
           (!ladOf p.2 d plev first force && first && (p.2 == plev))
      ++ convD (r.dropWhile fun q => p.1 < q.1) d p.2 false false
  termination_by M => M.length
  decreasing_by
  · exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ r)

/-- 変換の入口。 -/
def conv (M : PairSeq) : PairSeq := convD M 0 0 true false

/-! ### 動作確認 -/

#guard conv [(0,0)] = [(0,0)]
#guard conv [(0,0),(1,1)] = [(0,0),(1,0),(2,1)]
#guard conv [(0,0),(1,1),(2,2)] = [(0,0),(1,0),(2,1),(3,2)]
#guard conv [(0,0),(1,1),(1,1)] = [(0,0),(1,0),(2,1),(2,1)]
#guard conv [(0,0),(1,1),(1,0),(2,1)] = [(0,0),(1,0),(2,1),(1,0),(2,1)]
#guard conv [(0,0),(1,0),(2,1)] = [(0,0),(1,0),(2,0),(3,1)]
#guard conv [(0,0),(0,0),(1,1)] = [(0,0),(0,0),(1,0),(2,1)]

open Three in
#guard readD (conv [(0,0),(1,1)]) true 0 = translate [(0,0),(1,1)]
open Three in
#guard readD (conv [(0,0),(1,1),(1,0),(2,1)]) true 0 = translate [(0,0),(1,1),(1,0),(2,1)]
open Three in
#guard readD (conv [(0,0),(1,0),(2,1)]) true 0 = translate [(0,0),(1,0),(2,1)]

/-! ## 4. 主定理の仮定

* `colOK M`: どの列も 行1 ≤ 行0（BMS 標準形は対角 `(x,x)` 以下なので成り立つ）
* `descOK M`: 同じ深さの後続の鎖では段が増えない（CNF の降下条件） -/

/-- どの列も 行1 ≤ 行0。 -/
def colOK (M : PairSeq) : Prop := ∀ c ∈ M, c.2 ≤ c.1

/-- 同じ深さの後続の鎖では段が増えない。 -/
def descOK : PairSeq → Prop
  | [] => True
  | p :: r =>
      ((r.dropWhile fun q => p.1 < q.1) ≠ [] →
         ((r.dropWhile fun q => p.1 < q.1).headI).2 ≤ p.2) ∧
      descOK (r.takeWhile fun q => p.1 < q.1) ∧
      descOK (r.dropWhile fun q => p.1 < q.1)
  termination_by M => M.length
  decreasing_by
  · exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ r)

theorem descOK_nil : descOK [] := by rw [descOK]; trivial

theorem descOK_cons {p : ℕ × ℕ} {r : PairSeq} :
    descOK (p :: r) ↔
      ((r.dropWhile fun q => p.1 < q.1) ≠ [] →
         ((r.dropWhile fun q => p.1 < q.1).headI).2 ≤ p.2) ∧
      descOK (r.takeWhile fun q => p.1 < q.1) ∧
      descOK (r.dropWhile fun q => p.1 < q.1) := by
  rw [descOK]

theorem colOK_sublist {M N : PairSeq} (h : N.Sublist M) (hc : colOK M) : colOK N :=
  fun c hcn => hc c (h.subset hcn)

/-! ## 5. `convD` の形についての補題 -/

theorem le_ddOf (s d plev : ℕ) (first force : Bool) : d ≤ ddOf s d plev first force := by
  unfold ddOf
  split
  · omega
  · split
    · omega
    · exact Nat.le_refl d

@[simp] theorem convD_nil (d plev : ℕ) (first force : Bool) :
    convD [] d plev first force = [] := by rw [convD]

theorem convD_cons (p : ℕ × ℕ) (r : PairSeq) (d plev : ℕ) (first force : Bool) :
    convD (p :: r) d plev first force =
      (if ladOf p.2 d plev first force then [(d, plev), (d + 1, p.2)]
       else [(ddOf p.2 d plev first force, p.2)])
      ++ convD (r.takeWhile fun q => p.1 < q.1)
           (ddOf p.2 d plev first force + 1) p.2 true
           (!ladOf p.2 d plev first force && first && (p.2 == plev))
      ++ convD (r.dropWhile fun q => p.1 < q.1) d p.2 false false := by
  rw [convD]

/-- 出てくる列はどれも深さ `d` 以上。 -/
theorem convD_ge : ∀ (n : ℕ) (M : PairSeq), M.length ≤ n → ∀ (d plev : ℕ) (first force : Bool),
    ∀ c ∈ convD M d plev first force, d ≤ c.1 := by
  intro n
  induction n with
  | zero =>
    intro M hM d plev first force c hc
    have : M = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp at hc
  | succ n ih =>
    intro M hM d plev first force c hc
    match M with
    | [] => simp at hc
    | p :: r =>
      rw [convD_cons] at hc
      have hA : (r.takeWhile fun q => p.1 < q.1).length ≤ n := by
        have := (List.takeWhile_sublist (fun q : ℕ × ℕ => p.1 < q.1) (l := r)).length_le
        simp only [List.length_cons] at hM
        omega
      have hB : (r.dropWhile fun q => p.1 < q.1).length ≤ n := by
        have := List.length_dropWhile_le (fun q : ℕ × ℕ => p.1 < q.1) r
        simp only [List.length_cons] at hM
        omega
      rcases List.mem_append.1 hc with h | h
      · rcases List.mem_append.1 h with h | h
        · split at h
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl
            · exact Nat.le_refl d
            · exact Nat.le_succ d
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            subst h
            exact le_ddOf _ _ _ _ _
        · have := ih _ hA _ p.2 true _ c h
          have hd := le_ddOf p.2 d plev first force
          omega
      · exact ih _ hB _ p.2 false false c h

theorem convD_eq_nil_iff (M : PairSeq) (d plev : ℕ) (first force : Bool) :
    convD M d plev first force = [] ↔ M = [] := by
  match M with
  | [] => simp
  | p :: r =>
    rw [convD_cons]
    constructor
    · intro h
      split at h <;> simp at h
    · intro h; simp at h

/-- 先頭の列。 -/
theorem convD_headI (p : ℕ × ℕ) (r : PairSeq) (d plev : ℕ) (first force : Bool) :
    (convD (p :: r) d plev first force).headI =
      (if ladOf p.2 d plev first force then (d, plev)
       else (ddOf p.2 d plev first force, p.2)) := by
  rw [convD_cons]
  split <;> simp

/-- 先頭の深さは本体の深さ以下。 -/
theorem convD_head_le (p : ℕ × ℕ) (r : PairSeq) (d plev : ℕ) (first force : Bool) :
    ((convD (p :: r) d plev first force).headI).1 ≤ ddOf p.2 d plev first force := by
  rw [convD_headI]
  by_cases h : ladOf p.2 d plev first force = true
  · rw [if_pos h]
    exact le_ddOf _ _ _ _ _
  · rw [if_neg h]

/-- 出てくる列はどれも深さ `d` 以上（`n` を落とした形）。 -/
theorem convD_ge' (M : PairSeq) (d plev : ℕ) (first force : Bool) :
    ∀ c ∈ convD M d plev first force, d ≤ c.1 :=
  convD_ge M.length M (Nat.le_refl _) d plev first force

/-- 本体の深さは `d+1` か、あるいは「段を直接書ける」場合。 -/
theorem ddOf_cases (s d plev : ℕ) (first force : Bool) (hs : s ≤ d) :
    ddOf s d plev first force = d + 1 ∨ ¬ (0 < s ∧ d ≤ s) := by
  by_cases hl : ladOf s d plev first force = true
  · left; unfold ddOf; rw [if_pos hl]
  · by_cases hcase : 0 < s ∧ d ≤ s
    · left; unfold ddOf; rw [if_neg hl, if_pos hcase]; omega
    · right; exact hcase

/-- 深さでの切り分け。`X` が全部深く、`Y` の先頭が浅ければ、切れ目はちょうど `X | Y`。 -/
theorem split_append {X Y : PairSeq} {dd : ℕ}
    (hX : ∀ c ∈ X, dd < c.1) (hY : Y = [] ∨ ¬ (dd < (Y.headI).1)) :
    ((X ++ Y).takeWhile fun q => dd < q.1) = X ∧
      ((X ++ Y).dropWhile fun q => dd < q.1) = Y := by
  have hYt : (Y.takeWhile fun q => dd < q.1) = [] ∧ (Y.dropWhile fun q => dd < q.1) = Y := by
    rcases hY with rfl | h
    · simp
    · match Y with
      | [] => simp
      | q :: Y' =>
        refine ⟨List.takeWhile_cons_of_neg (by simpa using h),
          List.dropWhile_cons_of_neg (by simpa using h)⟩
  refine ⟨?_, ?_⟩
  · rw [takeWhile_append_all (by simpa using hX), hYt.1, List.append_nil]
  · rw [dropWhile_append_all (by simpa using hX), hYt.2]

/-! ## 6. 読みの 1 段（補題）

`convD` が出す列 `cols ++ X ++ Y` を `readD` が読むと、ちょうど
`P s (readD X true s) (readD Y false s)` になる。影を挟む場合と挟まない場合。 -/

open Three in
/-- 影を挟む場合。 -/
theorem readD_lad {X Y : PairSeq} {d plev s : ℕ}
    (hs : s = plev + 1)
    (hXge : ∀ c ∈ X, d + 1 < c.1) (hYhead : Y = [] ∨ ¬ (d + 1 < (Y.headI).1)) :
    readD ((d, plev) :: (d + 1, s) :: (X ++ Y)) true plev
      = P s (readD X true s) (readD Y false s) := by
  obtain ⟨h1, h2⟩ := split_append hXge hYhead
  rw [readD, if_pos (by exact ⟨rfl, rfl, by simp [hs]⟩), readD,
    if_neg (by rintro ⟨-, h, -⟩; simp only [] at h; omega)]
  dsimp only
  rw [h1, h2]

open Three in
/-- 影を挟まない場合。 -/
theorem readD_dir {X Y : PairSeq} {dd plev s : ℕ} {first : Bool}
    (hne : ¬ (first = true ∧ s = plev ∧ (X ++ Y).headI = (dd + 1, s + 1)))
    (hXge : ∀ c ∈ X, dd < c.1) (hYhead : Y = [] ∨ ¬ (dd < (Y.headI).1)) :
    readD ((dd, s) :: (X ++ Y)) first plev = P s (readD X true s) (readD Y false s) := by
  obtain ⟨h1, h2⟩ := split_append hXge hYhead
  rw [readD, if_neg (by dsimp only; exact hne)]
  dsimp only
  rw [h1, h2]

/-- 後続の先頭は本体の深さより深くならない。 -/
theorem convD_tail_head_le {B : PairSeq} {d s dd : ℕ}
    (hs : s ≤ d) (hddd : d ≤ dd)
    (hd1 : dd = d + 1 ∨ ¬ (0 < s ∧ d ≤ s))
    (hq : B ≠ [] → (B.headI).2 ≤ s) :
    convD B d s false false = [] ∨ ¬ (dd < ((convD B d s false false).headI).1) := by
  match B with
  | [] => left; rw [convD_nil]
  | q :: B' =>
    right
    have h1 := convD_head_le q B' d s false false
    have hq2 : q.2 ≤ s := by simpa using hq (by simp)
    have h2 : ddOf q.2 d s false false ≤ dd := by
      have hnl : ladOf q.2 d s false false = false := by simp [ladOf]
      unfold ddOf
      rw [if_neg (by rw [hnl]; simp)]
      by_cases hcase : 0 < q.2 ∧ d ≤ q.2
      · rw [if_pos hcase]
        rcases hd1 with h | h
        · omega
        · exact absurd (⟨by omega, by omega⟩ : 0 < s ∧ d ≤ s) h
      · rw [if_neg hcase]; omega
    omega

/-- 影を挟まないとき、続く列が影の形にならない（`force` を渡しているので）。 -/
theorem head_ne_shadow (A Y : PairSeq) (dd s : ℕ)
    (hY : Y = [] ∨ ¬ (dd < ((Y.headI).1))) :
    (convD A (dd + 1) s true true ++ Y).headI ≠ (dd + 1, s + 1) := by
  match A with
  | [] =>
    rw [convD_nil, List.nil_append]
    rcases hY with rfl | h
    · intro he
      have h2 : ((0 : ℕ), (0 : ℕ)) = (dd + 1, s + 1) := he
      rw [Prod.mk.injEq] at h2
      omega
    · intro he; rw [he] at h; simp only [] at h; omega
  | q :: A' =>
    rw [headI_append_left (by simp [convD_eq_nil_iff]), convD_headI]
    by_cases hlq : ladOf q.2 (dd + 1) s true true = true
    · rw [if_pos hlq]
      intro he
      have := congrArg Prod.snd he
      simp only [] at this
      omega
    · rw [if_neg hlq]
      intro he
      have hq : q.2 = s + 1 := by
        have := congrArg Prod.snd he
        simpa using this
      exact hlq (by simp [ladOf, hq])

/-! ## 7. 主定理

    readD (convD M d plev first force) first plev = translate M

仮定は BMS 側のブロック規律 `blockok bd M` と `bd ≤ d`、`colOK M`、`descOK M`。
BMS 2 行標準形 5351 個（≤9 列）で 3 条件はいずれも違反 0（`tools/dbms/rows2.py`）。 -/

/-- 帰納法の 1 段。列 1 本ぶんの読み。 -/
theorem readD_convD_step {p : ℕ × ℕ} {r : PairSeq} {d plev : ℕ} {first force : Bool}
    (hyd : p.2 ≤ d)
    (hArg : readD (convD (r.takeWhile fun q => p.1 < q.1)
              (ddOf p.2 d plev first force + 1) p.2 true
              (!ladOf p.2 d plev first force && first && (p.2 == plev))) true p.2
            = translate (r.takeWhile fun q => p.1 < q.1))
    (hTail : readD (convD (r.dropWhile fun q => p.1 < q.1) d p.2 false false) false p.2
            = translate (r.dropWhile fun q => p.1 < q.1))
    (hdesc : (r.dropWhile fun q => p.1 < q.1) ≠ [] →
              ((r.dropWhile fun q => p.1 < q.1).headI).2 ≤ p.2) :
    readD (convD (p :: r) d plev first force) first plev = translate (p :: r) := by
  have hddd : d ≤ ddOf p.2 d plev first force := le_ddOf _ _ _ _ _
  have hXge : ∀ c ∈ convD (r.takeWhile fun q => p.1 < q.1)
      (ddOf p.2 d plev first force + 1) p.2 true
      (!ladOf p.2 d plev first force && first && (p.2 == plev)),
      ddOf p.2 d plev first force < c.1 := by
    intro c hc
    have := convD_ge' _ _ _ _ _ c hc
    omega
  have hYhead := convD_tail_head_le (B := r.dropWhile fun q => p.1 < q.1)
    (d := d) (s := p.2) (dd := ddOf p.2 d plev first force) hyd hddd
    (ddOf_cases p.2 d plev first force hyd) hdesc
  rw [convD_cons]
  by_cases hl : ladOf p.2 d plev first force = true
  · -- 影を挟む
    have hy : p.2 = plev + 1 := by simp [ladOf] at hl; omega
    have hf : first = true := by simp [ladOf] at hl; tauto
    subst hf
    have hdd1 : ddOf p.2 d plev true force = d + 1 := by
      unfold ddOf; rw [if_pos hl]
    rw [if_pos hl]
    rw [hdd1] at hXge hYhead hArg ⊢
    simp only [List.cons_append, List.nil_append]
    rw [readD_lad hy hXge hYhead, hArg, hTail, translate]
  · -- 影を挟まない
    rw [if_neg hl]
    simp only [List.cons_append, List.nil_append]
    rw [readD_dir ?hne hXge hYhead, hArg, hTail, translate]
    case hne =>
      rintro ⟨hf, hlv, hhd⟩
      have hforce : (!ladOf p.2 d plev first force && first && (p.2 == plev)) = true := by
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true']
        exact ⟨⟨by simpa using hl, hf⟩, by simp [hlv]⟩
      rw [hforce] at hhd
      exact head_ne_shadow _ _ _ _ hYhead hhd

theorem readD_convD : ∀ (n : ℕ) (M : PairSeq), M.length ≤ n →
    ∀ (bd d plev : ℕ) (first force : Bool),
      blockok bd M → bd ≤ d → colOK M → descOK M →
      readD (convD M d plev first force) first plev = translate M := by
  intro n
  induction n with
  | zero =>
    intro M hM bd d plev first force _ _ _ _
    have : M = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [convD_nil, readD, translate]
  | succ n ih =>
    intro M hM bd d plev first force hb hbd hc hd
    match M with
    | [] => rw [convD_nil, readD, translate]
    | p :: r =>
      have hp : p.1 = bd := by simpa using hb.1 (by simp)
      obtain ⟨y, rfl⟩ : ∃ y, p = (bd, y) := ⟨p.2, by rw [← hp]⟩
      have hlA : (r.takeWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1).length ≤ n := by
        have h1 := (List.takeWhile_sublist
          (fun q : ℕ × ℕ => ((bd, y) : ℕ × ℕ).1 < q.1) (l := r)).length_le
        simp only [List.length_cons] at hM
        omega
      have hlB : (r.dropWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1).length ≤ n := by
        have h1 := List.length_dropWhile_le (fun q : ℕ × ℕ => ((bd, y) : ℕ × ℕ).1 < q.1) r
        simp only [List.length_cons] at hM
        omega
      have hbA := blockok_arg hb
      have hbB := blockok_tail hb
      have hcA : colOK (r.takeWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) := fun c hcm =>
        hc c (List.mem_cons_of_mem _ ((List.takeWhile_sublist _).subset hcm))
      have hcB : colOK (r.dropWhile fun q => ((bd, y) : ℕ × ℕ).1 < q.1) := fun c hcm =>
        hc c (List.mem_cons_of_mem _ ((List.dropWhile_sublist _).subset hcm))
      obtain ⟨hdhead, hdA, hdB⟩ := descOK_cons.1 hd
      have hyd : y ≤ d := by
        have h1 : ((bd, y) : ℕ × ℕ).2 ≤ ((bd, y) : ℕ × ℕ).1 := hc (bd, y) (by simp)
        simp only [] at h1
        omega
      have hddd : d ≤ ddOf ((bd, y) : ℕ × ℕ).2 d plev first force := le_ddOf _ _ _ _ _
      exact readD_convD_step (p := (bd, y)) hyd
        (ih _ hlA (bd + 1) _ y true _ hbA (by omega) hcA hdA)
        (ih _ hlB bd d y false false hbB hbd hcB hdB)
        hdhead

/-- 変換は読みを保つ。 -/
theorem readD_conv {M : PairSeq} (hb : blockok 0 M) (hc : colOK M) (hd : descOK M) :
    readD (conv M) true 0 = translate M :=
  readD_convD M.length M (Nat.le_refl _) 0 0 0 true false hb (Nat.le_refl 0) hc hd

/-! ## 7.5 縮約つきの変換 `convC`

`convD` の像は DBMS 標準形とは限らない（BMS 2 行標準形 ≤8 列 44653 個のうち 120 個）。
足りないのは「梯子の二役」で、規則はこう:

> 梯子を敷いた直後の後続が「段 `plev` のノードで、その引数が
> いま書いた（梯子＋本体＋兄弟）を **1 段深くしただけ**で一致」し、
> さらにそのあとに**同じ深さで段が下がる列**が来るとき、2 度目を書かない。

`convC` はシートの 264 件に **264/264** 一致し（`convD` は 245）、
像は BMS 2 行標準形 ≤8 列 44653 個すべてで DBMS 標準形になる
（`tools/dbms/rows2.py`）。読み `readC` は `readD` に「頂上から読み直す枝」を
足したもの。定理はまだ（`readC (convC M) = translate M` は Python で全数確認）。 -/

/-- ブロックを 1 段深くする。 -/
def shift1 (B : PairSeq) : PairSeq := B.map (fun c => (c.1 + 1, c.2))

/-- `l` の先頭が「深さ `dep`・段 `s` の列 + 引数 `A`」なら、その本数を返す。 -/
def unitLen (dep s : ℕ) (A : PairSeq) (l : PairSeq) : Option ℕ :=
  match l with
  | [] => none
  | q :: r =>
      if q.1 = dep ∧ q.2 = s ∧ (r.takeWhile fun x => dep < x.1) = A then
        some (A.length + 1)
      else none

/-- 引数なしの単位を `k` 個剥がした本数。 -/
def unitsLen (dep s : ℕ) : ℕ → PairSeq → Option ℕ
  | 0, _ => some 0
  | Nat.succ k, l =>
      match unitLen dep s [] l with
      | none => none
      | some n =>
          match unitsLen dep s k (l.drop n) with
          | none => none
          | some m => some (n + m)

/-- 先頭と同じ列が何本続くか。 -/
def sibRun (p : ℕ × ℕ) : PairSeq → ℕ
  | [] => 0
  | q :: r => if q = p then sibRun p r + 1 else 0

theorem sibRun_le (p : ℕ × ℕ) (l : PairSeq) : sibRun p l ≤ l.length := by
  induction l with
  | nil => simp [sibRun]
  | cons q r ih =>
    by_cases h : q = p
    · simpa [sibRun, h] using Nat.succ_le_succ ih
    · simp [sibRun, h]

/-- 縮約が発火するときに「読み直しの先」に残る列数。発火しなければ `none`。 -/
def contrLen (p : ℕ × ℕ) (B : PairSeq) (k : ℕ) (A : PairSeq) : Option (PairSeq × PairSeq) :=
  match B.drop k with
  | [] => none
  | q :: r2 =>
      if q.2 = p.2 - 1 ∧ q.1 = p.1 then
        let Aq := r2.takeWhile fun x => q.1 < x.1
        let Bq := r2.dropWhile fun x => q.1 < x.1
        match unitLen (p.1 + 1) p.2 (shift1 A) Aq with
        | none => none
        | some n0 =>
            match unitsLen (p.1 + 1) p.2 k (Aq.drop n0) with
            | none => none
            | some n1 =>
                let rest2 := Aq.drop (n0 + n1)
                if rest2 ≠ [] ∧ (rest2.headI).1 = p.1 + 1 ∧ (rest2.headI).2 < p.2 then
                  some (rest2, Bq)
                else none
      else none

/-- 縮約の枝で残る列は元より短い（停止性に使う）。 -/
theorem contrLen_lt {p : ℕ × ℕ} {B A rest2 Bq : PairSeq} {k : ℕ}
    (h : contrLen p B k A = some (rest2, Bq)) :
    rest2.length < B.length ∧ Bq.length < B.length := by
  unfold contrLen at h
  rcases hd : B.drop k with _ | ⟨q, r2⟩ <;> rw [hd] at h
  · simp at h
  · have hr2 : r2.length < B.length := by
      have hl : (B.drop k).length = B.length - k := List.length_drop
      rw [hd] at hl
      simp only [List.length_cons] at hl
      omega
    simp only [] at h
    split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, h2⟩ := h
            subst h1; subst h2
            constructor
            · have e2 : (r2.takeWhile fun x => q.1 < x.1).length ≤ r2.length :=
                (List.takeWhile_sublist _).length_le
              simp only [List.length_drop]
              omega
            · have e2 : (r2.dropWhile fun x => q.1 < x.1).length ≤ r2.length :=
                List.length_dropWhile_le _ r2
              omega
          · simp at h
    · simp at h

/-- BMS 2 行 -> DBMS 2 行（縮約つき）。 -/
def convC : PairSeq → ℕ → ℕ → Bool → Bool → PairSeq
  | [], _, _, _, _ => []
  | p :: r, d, plev, first, force =>
      if ladOf p.2 d plev first force then
        match hc : contrLen p (r.dropWhile fun q => p.1 < q.1)
            (sibRun p (r.dropWhile fun q => p.1 < q.1))
            (r.takeWhile fun q => p.1 < q.1) with
        | some (rest2, Bq) =>
            [(d, plev), (d + 1, p.2)]
              ++ convC (r.takeWhile fun q => p.1 < q.1) (d + 2) p.2 true false
              ++ List.replicate (sibRun p (r.dropWhile fun q => p.1 < q.1))
                   ((d + 1, p.2) : ℕ × ℕ)
              ++ convC rest2 (d + 1) p.2 false false
              ++ convC Bq d p.2 false false
        | none =>
            [(d, plev), (d + 1, p.2)]
              ++ convC (r.takeWhile fun q => p.1 < q.1) (d + 2) p.2 true false
              ++ convC (r.dropWhile fun q => p.1 < q.1) d p.2 false false
      else
        [(ddOf p.2 d plev first force, p.2)]
          ++ convC (r.takeWhile fun q => p.1 < q.1)
               (ddOf p.2 d plev first force + 1) p.2 true (first && (p.2 == plev))
          ++ convC (r.dropWhile fun q => p.1 < q.1) d p.2 false false
  termination_by M => M.length
  decreasing_by
  all_goals
    first
      | exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
      | exact Nat.lt_succ_of_le (List.length_dropWhile_le _ r)
      | (rename_i hc
         have h1 := (contrLen_lt hc).1
         have h2 := (contrLen_lt hc).2
         have h3 := List.length_dropWhile_le (fun q : ℕ × ℕ => p.1 < q.1) r
         simp only [List.length_cons]
         omega)

/-- 縮約つきの変換の入口。 -/
def conC (M : PairSeq) : PairSeq := convC M 0 0 true false

/-! ### 縮約つきの読み `readC`

`readD` に「梯子が二役を兼ねている枝」を足したもの。二役のときは
頂上から読み直す（読み直す列は元より必ず 1 本以上短いので整礎だが、
ここでは燃料で回す）。 -/

/-- 深さ `a` の子（引数）になる先頭部分の長さ。 -/
def argLen (a : ℕ) : PairSeq → ℕ
  | [] => 0
  | q :: r => if a < q.1 then argLen a r + 1 else 0

/-- 深さが `a` 以上で続く先頭部分の長さ。 -/
def deepLen (a : ℕ) : PairSeq → ℕ
  | [] => 0
  | q :: r => if a ≤ q.1 then deepLen a r + 1 else 0

open Three in
/-- 同じ段のノードを `n` 個、後続の向きに重ねる。 -/
def wrapN : ℕ → ℕ → Three → Three
  | 0, _, t => t
  | Nat.succ n, s, t => P s Z (wrapN n s t)

open Three in
/-- 縮約つきの読み。`readD` に「梯子が二役を兼ねている枝」を足したもの。 -/
def readC : PairSeq → Bool → ℕ → Three
  | [], _, _ => Z
  | p :: rest, first, plev =>
      if first = true ∧ p.2 = plev ∧ rest.headI = (p.1 + 1, p.2 + 1) then
        match rest with
        | [] => Z
        | top :: tail =>
            let arg := tail.takeWhile fun q => top.1 < q.1
            let after := tail.dropWhile fun q => top.1 < q.1
            let sib := after.takeWhile fun q => q = top
            let r2 := after.dropWhile fun q => q = top
            if r2 ≠ [] ∧ (r2.headI).1 = top.1 ∧ (r2.headI).2 < top.2 then
              P top.2 (readC arg true top.2)
                (wrapN sib.length top.2
                  (P p.2
                    (readC (top :: (arg ++ sib ++ (r2.takeWhile fun q => top.1 ≤ q.1)))
                      true p.2)
                    (readC (r2.dropWhile fun q => top.1 ≤ q.1) false plev)))
            else
              P top.2 (readC arg true top.2) (readC after false top.2)
      else
        P p.2 (readC (rest.takeWhile fun q => p.1 < q.1) true p.2)
              (readC (rest.dropWhile fun q => p.1 < q.1) false p.2)
  termination_by l => l.length
  decreasing_by
  all_goals
    (first
      | (simp only [List.length_cons]
         have e1 : (List.takeWhile (fun q => decide (top.1 < q.1)) tail).length
             + (List.dropWhile (fun q => decide (top.1 < q.1)) tail).length = tail.length := by
           rw [← List.length_append, List.takeWhile_append_dropWhile]
         have e2 : (List.takeWhile (fun q => decide (q = top))
               (List.dropWhile (fun q => decide (top.1 < q.1)) tail)).length
             + (List.dropWhile (fun q => decide (q = top))
               (List.dropWhile (fun q => decide (top.1 < q.1)) tail)).length
             = (List.dropWhile (fun q => decide (top.1 < q.1)) tail).length := by
           rw [← List.length_append, List.takeWhile_append_dropWhile]
         have e3 := (List.takeWhile_sublist (fun q : ℕ × ℕ => decide (top.1 ≤ q.1))
           (l := List.dropWhile (fun q => decide (q = top))
             (List.dropWhile (fun q => decide (top.1 < q.1)) tail))).length_le
         have e4 := List.length_dropWhile_le (fun q : ℕ × ℕ => decide (top.1 ≤ q.1))
           (List.dropWhile (fun q => decide (q = top))
             (List.dropWhile (fun q => decide (top.1 < q.1)) tail))
         simp only [List.length_append]
         omega)
      | (simp only [List.length_cons]
         have e1 := (List.takeWhile_sublist (fun q : ℕ × ℕ => decide (top.1 < q.1))
           (l := tail)).length_le
         have e2 := List.length_dropWhile_le (fun q : ℕ × ℕ => decide (top.1 < q.1)) tail
         omega)
      | (simp only [List.length_cons]
         have a1 := List.length_dropWhile_le (fun q : ℕ × ℕ => decide (top.1 < q.1)) tail
         have a2 := List.length_dropWhile_le (fun q : ℕ × ℕ => decide (q = top))
           (List.dropWhile (fun q => decide (top.1 < q.1)) tail)
         have a3 := List.length_dropWhile_le (fun q : ℕ × ℕ => decide (top.1 ≤ q.1))
           (List.dropWhile (fun q => decide (q = top))
             (List.dropWhile (fun q => decide (top.1 < q.1)) tail))
         omega)
      | exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
      | exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest))

/-- 縮約つきの読みの入口。 -/
def readCon (l : PairSeq) : Three := readC l true 0

/-! ### 動作確認（readC） -/

#guard readCon (conC [(0,0),(1,1),(1,0),(2,1),(2,0)]) = translate [(0,0),(1,1),(1,0),(2,1),(2,0)]
#guard readCon (conC [(0,0),(1,1),(2,2)]) = translate [(0,0),(1,1),(2,2)]
#guard readCon (conC [(0,0),(1,1),(1,1),(1,0),(2,1),(2,1),(2,0)])
     = translate [(0,0),(1,1),(1,1),(1,0),(2,1),(2,1),(2,0)]
#guard readCon (conC [(0,0),(1,1),(2,2),(1,0),(2,1),(3,2),(2,0)])
     = translate [(0,0),(1,1),(2,2),(1,0),(2,1),(3,2),(2,0)]

/-! ### 動作確認（縮約） -/

-- 縮約が起きる最小の形
#guard conC [(0,0),(1,1),(1,0),(2,1),(2,0)] = [(0,0),(1,0),(2,1),(2,0)]
#guard conv [(0,0),(1,1),(1,0),(2,1),(2,0)] = [(0,0),(1,0),(2,1),(1,0),(2,1),(2,0)]
-- 起きない形では conv と同じ
#guard conC [(0,0),(1,1),(1,0),(2,1)] = [(0,0),(1,0),(2,1),(1,0),(2,1)]
#guard conC [(0,0),(1,1),(2,2)] = [(0,0),(1,0),(2,1),(3,2)]
-- 引数が空でない縮約
#guard conC [(0,0),(1,1),(2,2),(1,0),(2,1),(3,2),(2,0)] = [(0,0),(1,0),(2,1),(3,2),(2,0)]
-- 兄弟つきの縮約
#guard conC [(0,0),(1,1),(1,1),(1,0),(2,1),(2,1),(2,0)] = [(0,0),(1,0),(2,1),(2,1),(2,0)]

/-! ## 8. 仮定は BMS 標準形なら自動で成り立つ

`blockok 0` は `Pair/Seqlex.lean` の `blockok_ST_PS`。
`colOK` は展開が行 1 を写すだけで行 0 は増えるだけなので保たれる。
`descOK` は `Pair/Cnf.lean` の `cnf`（項の標準形）からそのまま出る。 -/

theorem colOK_entry {M : PairSeq} (h : colOK M) (j : ℕ) : entry M 1 j ≤ entry M 0 j := by
  unfold entry
  simp only [if_neg (by decide : ¬ (1 : ℕ) = 0)]
  by_cases hj : j < M.length
  · rw [getD_eq_getElem' M ((0 : ℕ), (0 : ℕ)) hj]
    exact h _ (List.getElem_mem hj)
  · have he : M.getD j ((0 : ℕ), (0 : ℕ)) = (0, 0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [he]
    exact Nat.le_refl 0

theorem colOK_sub {M N : PairSeq} (h : N.Sublist M) (hc : colOK M) : colOK N :=
  fun c hcn => hc c (h.subset hcn)

theorem colOK_diagSeq (v : ℕ) : colOK (diagSeq 0 v) := by
  intro c hc
  unfold diagSeq at hc
  simp only [List.mem_map] at hc
  obtain ⟨j, -, rfl⟩ := hc
  exact Nat.le_refl j

theorem colOK_oper {M : PairSeq} {n : ℕ} (h : colOK M) : colOK (M⟦n⟧) := by
  by_cases hL : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]; exact h
  · have hPred : Pred M = M.dropLast := by unfold Pred; rw [if_neg (by omega)]
    by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
    · rw [oper_eq_pred_of_zero n hL hz, hPred]
      exact colOK_sub (M.dropLast_sublist) h
    · by_cases hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)
      · rw [oper_bad_unfold n hL hz hp]
        intro c hc
        rcases List.mem_append.1 hc with hc | hc
        · exact colOK_sub (List.take_sublist _ M) h c hc
        · simp only [List.mem_flatMap, List.mem_map] at hc
          obtain ⟨k, -, j, -, rfl⟩ := hc
          have := colOK_entry h j
          simp only []
          omega
      · rw [oper_eq_pred_of_noParent n hL hz hp, hPred]
        exact colOK_sub (M.dropLast_sublist) h

theorem colOK_ST_PS {M : PairSeq} (hM : ST_PS M) : colOK M := by
  induction hM with
  | diag v => exact colOK_diagSeq v
  | oper _ _ ih => exact colOK_oper ih

open Three in
theorem descOK_of_cnf : ∀ (n : ℕ) (M : PairSeq), M.length ≤ n → cnf (translate M) → descOK M := by
  intro n
  induction n with
  | zero =>
    intro M hM _
    have : M = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [descOK]
    trivial
  | succ n ih =>
    intro M hM hcnf
    match M with
    | [] => rw [descOK]; trivial
    | p :: r =>
      have hlA : (r.takeWhile fun q => p.1 < q.1).length ≤ n := by
        have h1 := (List.takeWhile_sublist (fun q : ℕ × ℕ => p.1 < q.1) (l := r)).length_le
        simp only [List.length_cons] at hM
        omega
      have hlB : (r.dropWhile fun q => p.1 < q.1).length ≤ n := by
        have h1 := List.length_dropWhile_le (fun q : ℕ × ℕ => p.1 < q.1) r
        simp only [List.length_cons] at hM
        omega
      rw [translate] at hcnf
      rw [descOK_cons]
      match hBe : (r.dropWhile fun q => p.1 < q.1) with
      | [] =>
        rw [hBe] at hcnf
        rw [translate] at hcnf
        refine ⟨fun hne => absurd hBe hne, ih _ hlA (cnf_P_Z.1 hcnf), ?_⟩
        rw [hBe]
        exact descOK_nil
      | q :: B' =>
        rw [hBe] at hcnf
        rw [translate] at hcnf
        obtain ⟨h1, h2, h3⟩ := cnf_P_P.1 hcnf
        refine ⟨fun _ => ?_, ih _ hlA h1, ?_⟩
        · rw [hBe]
          show q.2 ≤ p.2
          by_contra hlt
          exact h2 (olt_P_P.2 (Or.inl (by omega)))
        · rw [hBe]
          rw [← translate] at h3
          exact ih _ (by rw [← hBe]; exact hlB) h3

theorem descOK_ST_PS {M : PairSeq} (hM : ST_PS M) : descOK M :=
  descOK_of_cnf M.length M (Nat.le_refl _) (cnf_ST_PS hM)

/-- **主結果**: BMS 2 行標準形なら、変換は無条件に読みを保つ。 -/
theorem readD_conv_ST {M : PairSeq} (hM : ST_PS M) : readD (conv M) true 0 = translate M :=
  readD_conv (blockok_ST_PS hM) (colOK_ST_PS hM) (descOK_ST_PS hM)

/-! ## 9. 順序 -/

open Three in
/-- 変換は順序を保つ（項の順序 `<o` の意味で）。 -/
theorem conv_olt_iff_seqlex {M N : PairSeq} (hM : ST_PS M) (hN : ST_PS N) (hne : M ≠ N) :
    (readD (conv M) true 0 <o readD (conv N) true 0 ↔ seqlex M N) := by
  rw [readD_conv_ST hM, readD_conv_ST hN]
  exact olt_iff_seqlex (blockok_ST_PS hM) (blockok_ST_PS hN) hne

open Three in
/-- 変換は単射。 -/
theorem conv_injective {M N : PairSeq} (hM : ST_PS M) (hN : ST_PS N)
    (h : conv M = conv N) : M = N := by
  by_contra hne
  rcases seqlex_total M N with he | hs | hs
  · exact hne he
  · have := (conv_olt_iff_seqlex hM hN hne).2 hs
    rw [h] at this
    exact olt_irrefl _ this
  · have := (conv_olt_iff_seqlex hN hM (Ne.symm hne)).2 hs
    rw [h] at this
    exact olt_irrefl _ this

end DBMS
