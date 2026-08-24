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

## 縮約つきの `conC` / `readC`

`conv M` は DBMS の**標準形とは限らない**。BMS 2 行標準形 44653 個（≤8 列）のうち
**120 個**で像が非標準になる（`(0,0)(1,1)(1,0)(2,1)(2,0)` 型。DBMS 側では
梯子が二役を兼ねて縮む）。これを入れたのが `conC` / `readC`:

| | `conv` | `conC` |
|---|---|---|
| シート 264 件に一致 | 245 | **264** |
| 像が DBMS 標準形（≤8 列 44653 個） | 120 個が非標準 | **全部標準** |
| `読み (変換 M) = translate M` | **定理** | **定理** |

どちらも本ファイルで証明済み（`readD_conv_ST` / `readC_conC_ST`）。系として
`conC_olt_iff_seqlex`（順序保存）と `conC_injective`（単射）も出る。
`DbmsConv.lean` に 264 件の `conC A = E` と `readCon E = translate A` の #guard。

## 残る穴

1. **像が DBMS 標準形であること**は未証明（BMS 2 行標準形 ≤8 列 44653 個で全数確認のみ）。
2. **全射でない**。DBMS 標準形 ≤6 列（358 個）には全単射だが、7 列で 6 個外れる:

       DBMS 標準形  (0,0)(1,0)(2,1)(2,1)(2,1)(2,0)   ← 像に無い
       conC の像    (0,0)(1,0)(2,1)(2,1)(2,1)(2,1)

   後者が正しい像であることは ord の定義から確かめた
   （前者は `f(M[3])` 以上になってしまい上界にならない）。
   前者に対応する BMS 2 行標準形は 8 列までに存在しない。
   DBMS 2 行が BMS 2 行より真に細かいのか、それとも逆像が長いだけなのかは未決。

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

/-- 縮約で使い回される前置き: 本体の列 + その引数 + 兄弟のコピー。 -/
def contrPre (p : ℕ × ℕ) (k : ℕ) (A : PairSeq) : PairSeq :=
  ((p.1 + 1, p.2) :: shift1 A) ++ List.replicate k ((p.1 + 1, p.2) : ℕ × ℕ)

/-- 縮約が発火するか。発火するなら（読み直しの先, 外の後続）を返す。 -/
def contrLen (p : ℕ × ℕ) (B : PairSeq) (k : ℕ) (A : PairSeq) : Option (PairSeq × PairSeq) :=
  match B.drop k with
  | [] => none
  | q :: r2 =>
      let Aq := r2.takeWhile fun x => q.1 < x.1
      let Bq := r2.dropWhile fun x => q.1 < x.1
      let rest2 := Aq.drop (contrPre p k A).length
      if q.2 + 1 = p.2 ∧ q.1 = p.1 ∧ Aq.take (contrPre p k A).length = contrPre p k A ∧
          rest2 ≠ [] ∧ (rest2.headI).1 = p.1 + 1 ∧ (rest2.headI).2 < p.2 then
        some (rest2, Bq)
      else none

/-- `contrLen` が返す形を読み解く。 -/
theorem contrLen_spec {p : ℕ × ℕ} {B A rest2 Bq : PairSeq} {k : ℕ}
    (h : contrLen p B k A = some (rest2, Bq)) :
    ∃ q r2, B.drop k = q :: r2 ∧ q.2 + 1 = p.2 ∧ q.1 = p.1 ∧
      (r2.takeWhile fun x => q.1 < x.1) = contrPre p k A ++ rest2 ∧
      (r2.dropWhile fun x => q.1 < x.1) = Bq ∧
      rest2 ≠ [] ∧ (rest2.headI).1 = p.1 + 1 ∧ (rest2.headI).2 < p.2 := by
  unfold contrLen at h
  rcases hd : B.drop k with _ | ⟨q, r2⟩ <;> rw [hd] at h
  · simp at h
  · refine ⟨q, r2, rfl, ?_⟩
    simp only [] at h
    split at h
    · rename_i hcond
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcond
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2
      refine ⟨c1, c2, ?_, rfl, c4, c5, c6⟩
      conv_lhs => rw [← List.take_append_drop (contrPre p k A).length
        (r2.takeWhile fun x => q.1 < x.1)]
      rw [c3]
    · simp at h

/-- 縮約の枝で残る列は元より短い（停止性に使う）。 -/
theorem contrLen_lt {p : ℕ × ℕ} {B A rest2 Bq : PairSeq} {k : ℕ}
    (h : contrLen p B k A = some (rest2, Bq)) :
    rest2.length < B.length ∧ Bq.length < B.length := by
  obtain ⟨q, r2, hd, -, -, hAq, hBq, -, -, -⟩ := contrLen_spec h
  have hr2 : r2.length < B.length := by
    have hl : (B.drop k).length = B.length - k := List.length_drop
    rw [hd] at hl
    simp only [List.length_cons] at hl
    omega
  have e2 : (r2.takeWhile fun x => q.1 < x.1).length ≤ r2.length :=
    (List.takeWhile_sublist _).length_le
  have e3 : (r2.dropWhile fun x => q.1 < x.1).length ≤ r2.length :=
    List.length_dropWhile_le _ r2
  rw [hAq] at e2
  rw [hBq] at e3
  simp only [List.length_append] at e2
  omega

/-- BMS 2 行 -> DBMS 2 行（縮約つき）。 -/
def convC (M : PairSeq) (d plev : ℕ) (first force : Bool) : PairSeq :=
  match M with
  | [] => []
  | p :: r =>
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
  termination_by M.length
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
def readC (l : PairSeq) (first : Bool) (plev : ℕ) : Three :=
  match l with
  | [] => Z
  | p :: rest =>
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
  termination_by l.length
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

/-! ## 7.9 縮約つきの正しさに向けた補題 -/

@[simp] theorem convC_nil (d plev : ℕ) (first force : Bool) :
    convC [] d plev first force = [] := by rw [convC]

theorem convC_cons_nolad (p : ℕ × ℕ) (r : PairSeq) (d plev : ℕ) (first force : Bool)
    (hl : ladOf p.2 d plev first force = false) :
    convC (p :: r) d plev first force =
      (ddOf p.2 d plev first force, p.2)
        :: (convC (r.takeWhile fun q => p.1 < q.1)
              (ddOf p.2 d plev first force + 1) p.2 true (first && (p.2 == plev))
            ++ convC (r.dropWhile fun q => p.1 < q.1) d p.2 false false) := by
  rw [convC, if_neg (by rw [hl]; simp)]
  simp

theorem convC_cons_lad_none (p : ℕ × ℕ) (r : PairSeq) (d plev : ℕ) (first force : Bool)
    (hl : ladOf p.2 d plev first force = true)
    (hc : contrLen p (r.dropWhile fun q => p.1 < q.1)
            (sibRun p (r.dropWhile fun q => p.1 < q.1))
            (r.takeWhile fun q => p.1 < q.1) = none) :
    convC (p :: r) d plev first force =
      (d, plev) :: (d + 1, p.2)
        :: (convC (r.takeWhile fun q => p.1 < q.1) (d + 2) p.2 true false
            ++ convC (r.dropWhile fun q => p.1 < q.1) d p.2 false false) := by
  rw [convC, if_pos hl]
  split
  · rename_i rest2 Bq h
    rw [hc] at h
    exact absurd h (by simp)
  · rfl

theorem convC_cons_lad_some (p : ℕ × ℕ) (r : PairSeq) (d plev : ℕ) (first force : Bool)
    {rest2 Bq : PairSeq}
    (hl : ladOf p.2 d plev first force = true)
    (hc : contrLen p (r.dropWhile fun q => p.1 < q.1)
            (sibRun p (r.dropWhile fun q => p.1 < q.1))
            (r.takeWhile fun q => p.1 < q.1) = some (rest2, Bq)) :
    convC (p :: r) d plev first force =
      (d, plev) :: (d + 1, p.2)
        :: (convC (r.takeWhile fun q => p.1 < q.1) (d + 2) p.2 true false
            ++ List.replicate (sibRun p (r.dropWhile fun q => p.1 < q.1)) ((d + 1, p.2) : ℕ × ℕ)
            ++ convC rest2 (d + 1) p.2 false false
            ++ convC Bq d p.2 false false) := by
  rw [convC, if_pos hl]
  split
  · rename_i rest2' Bq' h
    rw [hc] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    rfl
  · rename_i h
    rw [hc] at h
    exact absurd h (by simp)

/-- `convC` の出す列はどれも深さ `d` 以上。 -/
theorem convC_ge : ∀ (n : ℕ) (M : PairSeq), M.length ≤ n → ∀ (d plev : ℕ) (first force : Bool),
    ∀ c ∈ convC M d plev first force, d ≤ c.1 := by
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
      have hA : (r.takeWhile fun q => p.1 < q.1).length ≤ n := by
        have := (List.takeWhile_sublist (fun q : ℕ × ℕ => p.1 < q.1) (l := r)).length_le
        simp only [List.length_cons] at hM; omega
      have hB : (r.dropWhile fun q => p.1 < q.1).length ≤ n := by
        have := List.length_dropWhile_le (fun q : ℕ × ℕ => p.1 < q.1) r
        simp only [List.length_cons] at hM; omega
      by_cases hl : ladOf p.2 d plev first force = true
      · rcases hcc : contrLen p (r.dropWhile fun q => p.1 < q.1)
            (sibRun p (r.dropWhile fun q => p.1 < q.1))
            (r.takeWhile fun q => p.1 < q.1) with _ | ⟨rest2, Bq⟩
        · rw [convC_cons_lad_none p r d plev first force hl hcc] at hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | rfl | hc
          · exact Nat.le_refl _
          · omega
          rcases List.mem_append.1 hc with h | h
          · have := ih _ hA (d + 2) p.2 true false c h; omega
          · exact ih _ hB d p.2 false false c h
        · rw [convC_cons_lad_some p r d plev first force hl hcc] at hc
          have hr2 : rest2.length ≤ n := by
            have := (contrLen_lt hcc).1; omega
          have hbq : Bq.length ≤ n := by
            have := (contrLen_lt hcc).2; omega
          simp only [List.mem_cons] at hc
          rcases hc with rfl | rfl | hc
          · exact Nat.le_refl _
          · omega
          rcases List.mem_append.1 hc with h | h
          · rcases List.mem_append.1 h with h | h
            · rcases List.mem_append.1 h with h | h
              · have := ih _ hA (d + 2) p.2 true false c h; omega
              · rw [List.eq_of_mem_replicate h]; omega
            · have := ih _ hr2 (d + 1) p.2 false false c h; omega
          · exact ih _ hbq d p.2 false false c h
      · rw [convC_cons_nolad p r d plev first force (by simpa using hl)] at hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact le_ddOf _ _ _ _ _
        rcases List.mem_append.1 hc with h | h
        · have := ih _ hA _ p.2 true _ c h
          have := le_ddOf p.2 d plev first force
          omega
        · exact ih _ hB d p.2 false false c h

theorem convC_ge' (M : PairSeq) (d plev : ℕ) (first force : Bool) :
    ∀ c ∈ convC M d plev first force, d ≤ c.1 :=
  convC_ge M.length M (Nat.le_refl _) d plev first force

theorem convC_eq_nil_iff (M : PairSeq) (d plev : ℕ) (first force : Bool) :
    convC M d plev first force = [] ↔ M = [] := by
  match M with
  | [] => simp
  | p :: r =>
    constructor
    · intro h
      by_cases hl : ladOf p.2 d plev first force = true
      · rcases hcc : contrLen p (r.dropWhile fun q => p.1 < q.1)
            (sibRun p (r.dropWhile fun q => p.1 < q.1))
            (r.takeWhile fun q => p.1 < q.1) with _ | ⟨rest2, Bq⟩
        · rw [convC_cons_lad_none p r d plev first force hl hcc] at h; simp at h
        · rw [convC_cons_lad_some p r d plev first force hl hcc] at h; simp at h
      · rw [convC_cons_nolad p r d plev first force (by simpa using hl)] at h; simp at h
    · intro h; simp at h

/-- `convC` の先頭の列。 -/
theorem convC_headI (p : ℕ × ℕ) (r : PairSeq) (d plev : ℕ) (first force : Bool) :
    (convC (p :: r) d plev first force).headI =
      (if ladOf p.2 d plev first force then (d, plev)
       else (ddOf p.2 d plev first force, p.2)) := by
  by_cases hl : ladOf p.2 d plev first force = true
  · rw [if_pos hl]
    rcases hcc : contrLen p (r.dropWhile fun q => p.1 < q.1)
        (sibRun p (r.dropWhile fun q => p.1 < q.1))
        (r.takeWhile fun q => p.1 < q.1) with _ | ⟨rest2, Bq⟩
    · rw [convC_cons_lad_none p r d plev first force hl hcc]; rfl
    · rw [convC_cons_lad_some p r d plev first force hl hcc]; rfl
  · rw [if_neg hl, convC_cons_nolad p r d plev first force (by simpa using hl)]; rfl

theorem convC_head_le (p : ℕ × ℕ) (r : PairSeq) (d plev : ℕ) (first force : Bool) :
    ((convC (p :: r) d plev first force).headI).1 ≤ ddOf p.2 d plev first force := by
  rw [convC_headI]
  by_cases h : ladOf p.2 d plev first force = true
  · rw [if_pos h]; exact le_ddOf _ _ _ _ _
  · rw [if_neg h]

@[simp] theorem shift1_nil : shift1 [] = [] := rfl

@[simp] theorem shift1_cons (c : ℕ × ℕ) (l : PairSeq) :
    shift1 (c :: l) = (c.1 + 1, c.2) :: shift1 l := rfl

@[simp] theorem shift1_length (l : PairSeq) : (shift1 l).length = l.length := by
  simp [shift1]

theorem shift1_takeWhile (a : ℕ) (l : PairSeq) :
    ((shift1 l).takeWhile fun q => a + 1 < q.1) = shift1 (l.takeWhile fun q => a < q.1) := by
  induction l with
  | nil => rfl
  | cons c r ih =>
    by_cases h : a < c.1
    · rw [shift1_cons, List.takeWhile_cons_of_pos (by simp; omega),
        List.takeWhile_cons_of_pos (by simpa using h), shift1_cons, ih]
    · rw [shift1_cons, List.takeWhile_cons_of_neg (by simp; omega),
        List.takeWhile_cons_of_neg (by simpa using h)]
      rfl

theorem shift1_dropWhile (a : ℕ) (l : PairSeq) :
    ((shift1 l).dropWhile fun q => a + 1 < q.1) = shift1 (l.dropWhile fun q => a < q.1) := by
  induction l with
  | nil => rfl
  | cons c r ih =>
    by_cases h : a < c.1
    · rw [shift1_cons, List.dropWhile_cons_of_pos (by simp; omega),
        List.dropWhile_cons_of_pos (by simpa using h), ih]
    · rw [shift1_cons, List.dropWhile_cons_of_neg (by simp; omega),
        List.dropWhile_cons_of_neg (by simpa using h), shift1_cons]

/-- 段を 1 つ深くしても読みは変わらない。 -/
theorem translate_shift1 : ∀ (n : ℕ) (B : PairSeq), B.length ≤ n →
    translate (shift1 B) = translate B := by
  intro n
  induction n with
  | zero =>
    intro B hB
    have : B = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ n ih =>
    intro B hB
    match B with
    | [] => rfl
    | p :: r =>
      have h1 : (r.takeWhile fun q => p.1 < q.1).length ≤ n := by
        have := (List.takeWhile_sublist (fun q : ℕ × ℕ => p.1 < q.1) (l := r)).length_le
        simp only [List.length_cons] at hB; omega
      have h2 : (r.dropWhile fun q => p.1 < q.1).length ≤ n := by
        have := List.length_dropWhile_le (fun q : ℕ × ℕ => p.1 < q.1) r
        simp only [List.length_cons] at hB; omega
      rw [shift1_cons, translate, translate]
      simp only []
      rw [shift1_takeWhile, shift1_dropWhile, ih _ h1, ih _ h2]

open Three in
/-- 影でないときの読み（`translate` と同じ形）。 -/
theorem readC_plain {p : ℕ × ℕ} {rest : PairSeq} {first : Bool} {plev : ℕ}
    (h : ¬ (first = true ∧ p.2 = plev ∧ rest.headI = (p.1 + 1, p.2 + 1))) :
    readC (p :: rest) first plev
      = P p.2 (readC (rest.takeWhile fun q => p.1 < q.1) true p.2)
              (readC (rest.dropWhile fun q => p.1 < q.1) false p.2) := by
  rw [readC.eq_def]
  simp only []
  rw [if_neg h]

open Three in
/-- 影のとき、`readC` は「影を捨てて頂上から」の形になる。二役かどうかで枝が分かれる。 -/
theorem readC_shadow_eq {p top : ℕ × ℕ} {tail : PairSeq} {first : Bool} {plev : ℕ}
    (hf : first = true) (hp : p.2 = plev) (htop : top = (p.1 + 1, p.2 + 1)) :
    readC (p :: top :: tail) first plev
      = (let arg := tail.takeWhile fun q => top.1 < q.1
         let after := tail.dropWhile fun q => top.1 < q.1
         let sib := after.takeWhile fun q => q = top
         let r2 := after.dropWhile fun q => q = top
         if r2 ≠ [] ∧ (r2.headI).1 = top.1 ∧ (r2.headI).2 < top.2 then
           P top.2 (readC arg true top.2)
             (wrapN sib.length top.2
               (P p.2
                 (readC (top :: (arg ++ sib ++ (r2.takeWhile fun q => top.1 ≤ q.1))) true p.2)
                 (readC (r2.dropWhile fun q => top.1 ≤ q.1) false plev)))
         else P top.2 (readC arg true top.2) (readC after false top.2)) := by
  subst hf; subst htop
  rw [readC.eq_def]
  simp only []
  rw [if_pos ⟨trivial, hp, by simp⟩]

open Three in
/-- 影のときの読み（二役でない場合）。 -/
theorem readC_shadow {p top : ℕ × ℕ} {tail : PairSeq} {first : Bool} {plev : ℕ}
    (hf : first = true) (hp : p.2 = plev) (htop : top = (p.1 + 1, p.2 + 1))
    (hd : ¬ (((tail.dropWhile fun q => top.1 < q.1).dropWhile fun q => q = top) ≠ [] ∧
          ((((tail.dropWhile fun q => top.1 < q.1).dropWhile fun q => q = top).headI).1 = top.1) ∧
          ((((tail.dropWhile fun q => top.1 < q.1).dropWhile fun q => q = top).headI).2 < top.2))) :
    readC (p :: top :: tail) first plev
      = P top.2 (readC (tail.takeWhile fun q => top.1 < q.1) true top.2)
                (readC (tail.dropWhile fun q => top.1 < q.1) false top.2) := by
  rw [readC_shadow_eq hf hp htop]
  simp only []
  rw [if_neg hd]

open Three in
/-- 影のときの読み（梯子が二役を兼ねている場合）。 -/
theorem readC_dual {p top : ℕ × ℕ} {tail : PairSeq} {first : Bool} {plev : ℕ}
    (hf : first = true) (hp : p.2 = plev) (htop : top = (p.1 + 1, p.2 + 1))
    (hd : ((tail.dropWhile fun q => top.1 < q.1).dropWhile fun q => q = top) ≠ [] ∧
          ((((tail.dropWhile fun q => top.1 < q.1).dropWhile fun q => q = top).headI).1 = top.1) ∧
          ((((tail.dropWhile fun q => top.1 < q.1).dropWhile fun q => q = top).headI).2 < top.2)) :
    readC (p :: top :: tail) first plev
      = (let arg := tail.takeWhile fun q => top.1 < q.1
         let after := tail.dropWhile fun q => top.1 < q.1
         let sib := after.takeWhile fun q => q = top
         let r2 := after.dropWhile fun q => q = top
         P top.2 (readC arg true top.2)
           (wrapN sib.length top.2
             (P p.2
               (readC (top :: (arg ++ sib ++ (r2.takeWhile fun q => top.1 ≤ q.1))) true p.2)
               (readC (r2.dropWhile fun q => top.1 ≤ q.1) false plev)))) := by
  rw [readC_shadow_eq hf hp htop]
  simp only []
  rw [if_pos hd]

/-- 先頭で止まるなら takeWhile は空、dropWhile は全部。 -/
theorem head_stop {a : ℕ} {L : PairSeq} (h : L = [] ∨ ¬ (a < (L.headI).1)) :
    (L.takeWhile fun q => a < q.1) = [] ∧ (L.dropWhile fun q => a < q.1) = L := by
  rcases h with rfl | h
  · simp
  · match L with
    | [] => simp
    | q :: L' =>
      exact ⟨List.takeWhile_cons_of_neg (by simpa using h),
             List.dropWhile_cons_of_neg (by simpa using h)⟩

@[simp] theorem sibRun_nil (p : ℕ × ℕ) : sibRun p [] = 0 := rfl

theorem take_sibRun (p : ℕ × ℕ) (B : PairSeq) :
    B.take (sibRun p B) = List.replicate (sibRun p B) p := by
  induction B with
  | nil => simp
  | cons q r ih =>
    by_cases h : q = p
    · subst h
      simp [sibRun, ih, List.replicate_succ]
    · simp [sibRun, h]

theorem sibRun_split (p : ℕ × ℕ) (B : PairSeq) :
    B = List.replicate (sibRun p B) p ++ B.drop (sibRun p B) := by
  conv_lhs => rw [← List.take_append_drop (sibRun p B) B]
  rw [take_sibRun]

open Three in
theorem translate_replicate (c : ℕ × ℕ) (L : PairSeq)
    (hL : L = [] ∨ ¬ (c.1 < (L.headI).1)) :
    ∀ k, translate (List.replicate k c ++ L) = wrapN k c.2 (translate L) := by
  intro k
  induction k with
  | zero => simp [wrapN]
  | succ k ih =>
    have hh : (List.replicate k c ++ L) = [] ∨ ¬ (c.1 < ((List.replicate k c ++ L).headI).1) := by
      cases k with
      | zero => simpa using hL
      | succ k' => right; rw [List.replicate_succ, List.cons_append]; simp
    obtain ⟨e1, e2⟩ := head_stop (a := c.1) hh
    rw [List.replicate_succ, List.cons_append, translate, e1, e2, ih, wrapN, translate]

/-- `first = false` の読みは親の段に依らない。 -/
theorem readC_plev (l : PairSeq) (plev plev' : ℕ) :
    readC l false plev = readC l false plev' := by
  match l with
  | [] => simp [readC]
  | p :: rest =>
    rw [readC.eq_def, readC.eq_def]
    simp only [Bool.false_eq_true, false_and, if_false]

open Three in
theorem readC_replicate (c : ℕ × ℕ) (Y : PairSeq)
    (hY : Y = [] ∨ ¬ (c.1 < (Y.headI).1)) :
    ∀ k (plev : ℕ), readC (List.replicate k c ++ Y) false plev = wrapN k c.2 (readC Y false c.2) := by
  intro k
  induction k with
  | zero => intro plev; simpa using readC_plev Y plev c.2
  | succ k ih =>
    intro plev
    have hh : (List.replicate k c ++ Y) = [] ∨ ¬ (c.1 < ((List.replicate k c ++ Y).headI).1) := by
      cases k with
      | zero => simpa using hY
      | succ k' => right; rw [List.replicate_succ, List.cons_append]; simp
    obtain ⟨e1, e2⟩ := head_stop (a := c.1) hh
    rw [List.replicate_succ, List.cons_append, readC.eq_def]
    simp only [Bool.false_eq_true, false_and, if_false]
    rw [e1, e2, ih, wrapN]
    simp [readC]

/-- 同じ列を `k` 本並べたあとに `L` が続くとき、`convC` は同じ列を `k` 本出す。 -/
theorem convC_replicate (c : ℕ × ℕ) (L : PairSeq) (d : ℕ)
    (hdd : ddOf c.2 d c.2 false false = d)
    (hL : L = [] ∨ ¬ (c.1 < (L.headI).1)) :
    ∀ k, convC (List.replicate k c ++ L) d c.2 false false
        = List.replicate k ((d, c.2) : ℕ × ℕ) ++ convC L d c.2 false false := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hh : (List.replicate k c ++ L) = [] ∨ ¬ (c.1 < ((List.replicate k c ++ L).headI).1) := by
      cases k with
      | zero => simpa using hL
      | succ k' => right; rw [List.replicate_succ, List.cons_append]; simp
    obtain ⟨e1, e2⟩ := head_stop (a := c.1) hh
    rw [List.replicate_succ, List.cons_append,
      convC_cons_nolad c _ d c.2 false false (by simp [ladOf])]
    simp only [hdd, e1, e2, convC_nil, List.nil_append, ih, List.replicate_succ,
      List.cons_append]

/-- 同じ列を `k` 本剥がしても `descOK` は残る。 -/
theorem descOK_replicate (c : ℕ × ℕ) (L : PairSeq)
    (hL : L = [] ∨ ¬ (c.1 < (L.headI).1)) :
    ∀ k, descOK (List.replicate k c ++ L) → descOK L := by
  intro k
  induction k with
  | zero => intro h; simpa using h
  | succ k ih =>
    intro h
    have hh : (List.replicate k c ++ L) = [] ∨ ¬ (c.1 < ((List.replicate k c ++ L).headI).1) := by
      cases k with
      | zero => simpa using hL
      | succ k' => right; rw [List.replicate_succ, List.cons_append]; simp
    obtain ⟨-, e2⟩ := head_stop (a := c.1) hh
    rw [List.replicate_succ, List.cons_append] at h
    have := (descOK_cons.1 h).2.2
    rw [e2] at this
    exact ih this

/-- 同じ列を `k` 本剥がしても `blockok` は残る。 -/
theorem blockok_replicate (d y : ℕ) (L : PairSeq)
    (hL : L = [] ∨ ¬ (d < (L.headI).1)) :
    ∀ k, blockok d (List.replicate k ((d, y) : ℕ × ℕ) ++ L) → blockok d L := by
  intro k
  induction k with
  | zero => intro h; simpa using h
  | succ k ih =>
    intro h
    have hh : (List.replicate k ((d, y) : ℕ × ℕ) ++ L) = [] ∨
        ¬ (d < ((List.replicate k ((d, y) : ℕ × ℕ) ++ L).headI).1) := by
      cases k with
      | zero => simpa using hL
      | succ k' => right; rw [List.replicate_succ, List.cons_append]; simp
    obtain ⟨-, e2⟩ := head_stop (a := d) hh
    rw [List.replicate_succ, List.cons_append] at h
    have h2 := blockok_tail h
    rw [e2] at h2
    exact ih h2

theorem steps1_drop : ∀ (n : ℕ) {L : PairSeq}, steps1 L → steps1 (L.drop n) := by
  intro n
  induction n with
  | zero => intro L h; simpa using h
  | succ n ih =>
    intro L h
    match L with
    | [] => simp
    | p :: r => simpa using ih (steps1_tail h)

theorem blockok_drop {d n : ℕ} {L : PairSeq} (h : blockok d L)
    (hh : L.drop n ≠ [] → ((L.drop n).headI).1 = d) : blockok d (L.drop n) :=
  ⟨hh, fun c hc => h.2.1 c ((List.drop_sublist n L).subset hc), steps1_drop n h.2.2⟩

open Three in
/-- 縮約で使い回される前置きの読み。BMS 側の「2 度目」がこの形になる。 -/
theorem translate_contrPre (p : ℕ × ℕ) (k : ℕ) (A rest2 : PairSeq)
    (hA : ∀ c ∈ A, p.1 < c.1)
    (hr : rest2 = [] ∨ ¬ (p.1 + 1 < (rest2.headI).1)) :
    translate (contrPre p k A ++ rest2)
      = P p.2 (translate A) (wrapN k p.2 (translate rest2)) := by
  have hsh : ∀ c ∈ shift1 A, p.1 + 1 < c.1 := by
    intro c hc
    simp only [shift1, List.mem_map] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    have := hA c' hc'
    simp only []
    omega
  have hrest : (List.replicate k ((p.1 + 1, p.2) : ℕ × ℕ) ++ rest2) = [] ∨
      ¬ (p.1 + 1 < ((List.replicate k ((p.1 + 1, p.2) : ℕ × ℕ) ++ rest2).headI).1) := by
    cases k with
    | zero => simpa using hr
    | succ k' => right; rw [List.replicate_succ, List.cons_append]; simp
  have he : contrPre p k A ++ rest2
      = (p.1 + 1, p.2) :: (shift1 A ++ (List.replicate k ((p.1 + 1, p.2) : ℕ × ℕ) ++ rest2)) := by
    simp [contrPre]
  obtain ⟨e1, e2⟩ := split_append (dd := p.1 + 1) hsh hrest
  rw [he, translate]
  simp only []
  rw [e1, e2, translate_shift1 A.length A (Nat.le_refl _),
    translate_replicate ((p.1 + 1, p.2) : ℕ × ℕ) rest2 (by simpa using hr) k]

/-! ### 縮約が起きないときは、読みも二役の枝に入らない

`convC L d plev false false` の先頭は `(ddOf s d plev false false, s)`（`s = L.headI.2`）。
`s ≤ plev ≤ d` なので、深さが `d+1` になるのは `s = plev = d` のときだけで、
そのとき段はちょうど `plev`。つまり「深さ `d+1` で段が `plev` 未満」の列は
先頭には決して来ない。影の兄弟（`(d+1, plev)`）を剥がした先も同じで、
剥がした直後は引数ブロック（深さ `d+2` 以上）か、次の後続の先頭になる。 -/

/-- 二役の枝の判定。 -/
def dipAt (d plev : ℕ) (W : PairSeq) : Prop :=
  W ≠ [] ∧ (W.headI).1 = d + 1 ∧ (W.headI).2 < plev

theorem headI_mem' {l : PairSeq} (h : l ≠ []) : l.headI ∈ l := by
  match l with
  | [] => exact absurd rfl h
  | q :: r => simp

/-- 先頭が `top` でなければ `dropWhile` はそこで止まる。 -/
theorem dropWhile_stop {top : ℕ × ℕ} {W : PairSeq} (hne : W ≠ [])
    (h : W.headI ≠ top) : (W.dropWhile fun q => q = top) = W := by
  match W with
  | [] => exact absurd rfl hne
  | q :: W' => exact List.dropWhile_cons_of_neg (by simpa using h)

/-- 深い接頭辞が付いていれば、影を剥がしても深いままなので二役にならない。 -/
theorem nodip_of_deep {d plev : ℕ} {X Y : PairSeq} (hne : X ≠ [])
    (hdeep : d + 1 < (X.headI).1) :
    ¬ dipAt d plev ((X ++ Y).dropWhile fun q => q = (d + 1, plev)) := by
  have hnx : X.headI ≠ ((d + 1, plev) : ℕ × ℕ) := by
    intro he
    rw [he] at hdeep
    simp only [] at hdeep
    omega
  have hhd : (X ++ Y).headI = X.headI := headI_append_left hne
  have hne2 : (X ++ Y) ≠ [] := by
    intro he
    exact hne (List.append_eq_nil_iff.1 he).1
  rw [dropWhile_stop hne2 (by rw [hhd]; exact hnx)]
  rintro ⟨-, h2, -⟩
  rw [hhd] at h2
  omega

theorem convC_nodip : ∀ (n : ℕ) (L : PairSeq), L.length ≤ n → ∀ (d plev : ℕ), plev ≤ d →
    descOK L → (L ≠ [] → (L.headI).2 ≤ plev) →
    ¬ dipAt d plev ((convC L d plev false false).dropWhile fun q => q = (d + 1, plev)) := by
  intro n
  induction n with
  | zero =>
    intro L hL d plev _ _ _
    have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rintro ⟨h, -, -⟩
    exact h (by simp)
  | succ n ih =>
    intro L hL d plev hpd hd hhead
    match L with
    | [] => rintro ⟨h, -, -⟩; exact h (by simp)
    | p :: r =>
      have hs : p.2 ≤ plev := by simpa using hhead (by simp)
      have hnl : ladOf p.2 d plev false false = false := by simp [ladOf]
      have hB : (r.dropWhile fun q => p.1 < q.1).length ≤ n := by
        have := List.length_dropWhile_le (fun q : ℕ × ℕ => p.1 < q.1) r
        simp only [List.length_cons] at hL; omega
      obtain ⟨hdh, hdA, hdB⟩ := descOK_cons.1 hd
      set A := r.takeWhile (fun q => p.1 < q.1) with hAdef
      set B := r.dropWhile (fun q => p.1 < q.1) with hBdef
      set dd := ddOf p.2 d plev false false with hdd
      set X := convC A (dd + 1) p.2 true (false && (p.2 == plev)) with hX
      set Y := convC B d p.2 false false with hY
      rw [convC_cons_nolad p r d plev false false hnl]
      simp only [← hdd, ← hAdef, ← hBdef, ← hX, ← hY]
      by_cases hcase : dd = d + 1
      · -- 先頭は `(d+1, p.2)`。このとき `p.2 = plev = d`
        have hpp : p.2 = plev := by
          rw [hdd] at hcase
          unfold ddOf at hcase
          rw [if_neg (by rw [hnl]; simp)] at hcase
          split at hcase
          · omega
          · omega
        rw [List.dropWhile_cons_of_pos (by simp [hcase, hpp])]
        by_cases hAe : X = []
        · rw [hAe, List.nil_append]
          have hYe : Y = convC B d plev false false := by rw [hY, hpp]
          rw [hYe]
          refine ih B hB d plev hpd hdB (fun hne => ?_)
          have h1 := hdh hne
          omega
        · refine nodip_of_deep hAe ?_
          have h1 := convC_ge' A (dd + 1) p.2 true (false && (p.2 == plev)) _
            (headI_mem' (l := X) hAe)
          omega
      · -- 先頭の深さは `d+1` ではないので、そこで止まる
        rw [List.dropWhile_cons_of_neg (by
          simp only [decide_eq_true_eq]
          intro he
          exact hcase (congrArg Prod.fst he))]
        rintro ⟨-, h2, -⟩
        exact hcase (by simpa using h2)

/-- 同じ列を `k` 本並べたあとが違う列なら、`takeWhile`/`dropWhile` はそこで切れる。 -/
theorem takeDrop_replicate (c : ℕ × ℕ) (L : PairSeq) (hL : L.headI ≠ c) :
    ∀ k, ((List.replicate k c ++ L).takeWhile fun x => x = c) = List.replicate k c ∧
      ((List.replicate k c ++ L).dropWhile fun x => x = c) = L := by
  intro k
  induction k with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    cases hLe : L with
    | nil => simp
    | cons a L' =>
      rw [hLe] at hL
      simp only [List.headI_cons] at hL
      exact ⟨List.takeWhile_cons_of_neg (by simpa using hL),
        List.dropWhile_cons_of_neg (by simpa using hL)⟩
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append,
      List.takeWhile_cons_of_pos (by simp), List.dropWhile_cons_of_pos (by simp)]
    exact ⟨by rw [ih.1], ih.2⟩

/-- 深さでの切り分け（`≤` 版）。 -/
theorem split_append_le {X Y : PairSeq} {dd : ℕ}
    (hX : ∀ c ∈ X, dd ≤ c.1) (hY : Y = [] ∨ ¬ (dd ≤ (Y.headI).1)) :
    ((X ++ Y).takeWhile fun q => dd ≤ q.1) = X ∧
      ((X ++ Y).dropWhile fun q => dd ≤ q.1) = Y := by
  have hYt : (Y.takeWhile fun q => dd ≤ q.1) = [] ∧ (Y.dropWhile fun q => dd ≤ q.1) = Y := by
    rcases hY with rfl | h
    · simp
    · match Y with
      | [] => simp
      | q :: Y' =>
        exact ⟨List.takeWhile_cons_of_neg (by simpa using h),
          List.dropWhile_cons_of_neg (by simpa using h)⟩
  refine ⟨?_, ?_⟩
  · rw [takeWhile_append_all (by simpa using hX), hYt.1, List.append_nil]
  · rw [dropWhile_append_all (by simpa using hX), hYt.2]

/-- `contrLen` が返す `rest2` / `Bq` は元の後続ブロックの部分列。 -/
theorem contrLen_sublists {p : ℕ × ℕ} {B A rest2 Bq : PairSeq} {k : ℕ}
    (h : contrLen p B k A = some (rest2, Bq)) :
    rest2.Sublist B ∧ Bq.Sublist B := by
  obtain ⟨q, r2, hd, -, -, hAq, hBq, -, -, -⟩ := contrLen_spec h
  have hdrop : (q :: r2).Sublist B := hd ▸ List.drop_sublist k B
  have hr2 : r2.Sublist B := (List.sublist_cons_self q r2).trans hdrop
  constructor
  · have h1 : rest2.Sublist (contrPre p k A ++ rest2) := (contrPre p k A).sublist_append_right rest2
    have h2 : (contrPre p k A ++ rest2).Sublist r2 := hAq ▸ List.takeWhile_sublist _
    exact (h1.trans h2).trans hr2
  · exact (hBq ▸ List.dropWhile_sublist (l := r2) _).trans hr2

/-! ### 縮約つきの主定理

    readC (convC M d plev first force) first plev = translate M

仮定は `convD` のときと同じ（`blockok` / `bd ≤ d` / `colOK` / `descOK`）。 -/

/-- 影を挟まないとき、出力の 2 列目は影の形にならない。 -/
theorem convC_head_ne_shadow {A B : PairSeq} {dd d plev v : ℕ} {force : Bool}
    (hdd : d ≤ dd) (hB : B = [] ∨ ¬ ((B.headI).2 = v + 1)) :
    (convC A (dd + 1) v true true ++ convC B d plev force false).headI ≠ (dd + 1, v + 1) := by
  cases A with
  | cons q A' =>
    have hXne : convC (q :: A') (dd + 1) v true true ≠ [] := by
      simp only [ne_eq, convC_eq_nil_iff]; simp
    rw [headI_append_left hXne, convC_headI]
    by_cases hl : ladOf q.2 (dd + 1) v true true = true
    · rw [if_pos hl]
      intro he
      have h2 := congrArg Prod.snd he
      simp only [] at h2
      omega
    · rw [if_neg hl]
      intro he
      have h1 : q.2 = v + 1 := congrArg Prod.snd he
      exact hl (by simp [ladOf, h1])
  | nil =>
    rw [convC_nil, List.nil_append]
    cases B with
    | nil => rw [convC_nil]; intro he; exact absurd (congrArg Prod.snd he) (by simp)
    | cons q B' =>
      rw [convC_headI]
      by_cases hl : ladOf q.2 d plev force false = true
      · rw [if_pos hl]
        intro he
        have h2 : d = dd + 1 := congrArg Prod.fst he
        omega
      · rw [if_neg hl]
        intro he
        have h1 : q.2 = v + 1 := congrArg Prod.snd he
        rcases hB with h | h
        · simp at h
        · simp only [List.headI_cons] at h; exact h h1

theorem readC_convC : ∀ (n : ℕ) (M : PairSeq), M.length ≤ n →
    ∀ (bd d plev : ℕ) (first force : Bool),
      blockok bd M → bd ≤ d → colOK M → descOK M →
      readC (convC M d plev first force) first plev = translate M := by
  intro n
  induction n with
  | zero =>
    intro M hM bd d plev first force _ _ _ _
    have : M = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [convC_nil, readC, translate]
  | succ n ih =>
    intro M hM bd d plev first force hb hbd hc hd
    match M with
    | [] => rw [convC_nil, readC, translate]
    | p :: r =>
      have hp : p.1 = bd := by simpa using hb.1 (by simp)
      obtain ⟨y, rfl⟩ : ∃ y, p = (bd, y) := ⟨p.2, by rw [← hp]⟩
      set A := r.takeWhile (fun q => ((bd, y) : ℕ × ℕ).1 < q.1) with hAdef
      set B := r.dropWhile (fun q => ((bd, y) : ℕ × ℕ).1 < q.1) with hBdef
      have hlA : A.length ≤ n := by
        rw [hAdef]
        have h1 := (List.takeWhile_sublist
          (fun q : ℕ × ℕ => ((bd, y) : ℕ × ℕ).1 < q.1) (l := r)).length_le
        simp only [List.length_cons] at hM
        omega
      have hlB : B.length ≤ n := by
        rw [hBdef]
        have h1 := List.length_dropWhile_le (fun q : ℕ × ℕ => ((bd, y) : ℕ × ℕ).1 < q.1) r
        simp only [List.length_cons] at hM
        omega
      have hbA : blockok (bd + 1) A := by rw [hAdef]; exact blockok_arg hb
      have hbB : blockok bd B := by rw [hBdef]; exact blockok_tail hb
      have hcA : colOK A := fun c hcm => by
        rw [hAdef] at hcm
        exact hc c (List.mem_cons_of_mem _ ((List.takeWhile_sublist _).subset hcm))
      have hcB : colOK B := fun c hcm => by
        rw [hBdef] at hcm
        exact hc c (List.mem_cons_of_mem _ ((List.dropWhile_sublist _).subset hcm))
      obtain ⟨hdh, hdA, hdB⟩ := descOK_cons.1 hd
      rw [← hAdef] at hdA
      rw [← hBdef] at hdh hdB
      have hyd : y ≤ d := by
        have h1 : ((bd, y) : ℕ × ℕ).2 ≤ ((bd, y) : ℕ × ℕ).1 := hc (bd, y) (by simp)
        simp only [] at h1
        omega
      set dd := ddOf y d plev first force with hdd
      have hddd : d ≤ dd := le_ddOf _ _ _ _ _
      -- 後続側の像の先頭は深さ `dd` 以下
      have hYshallow : convC B d y false false = [] ∨
          ((convC B d y false false).headI).1 ≤ dd := by
        cases hBe : B with
        | nil => left; rw [convC_nil]
        | cons q B' =>
          right
          have h1 := convC_head_le q B' d y false false
          have hq2 : q.2 ≤ y := by
            have h0 := hdh (by rw [hBe]; simp)
            rw [hBe] at h0
            simpa using h0
          have h2 : ddOf q.2 d y false false ≤ dd := by
            have hnl : ladOf q.2 d y false false = false := by simp [ladOf]
            unfold ddOf
            rw [if_neg (by rw [hnl]; simp)]
            by_cases hcase : 0 < q.2 ∧ d ≤ q.2
            · rw [if_pos hcase]
              have hyy : y = d := by omega
              have : dd = d + 1 := by
                rw [hdd]
                unfold ddOf
                by_cases hl : ladOf y d plev first force = true
                · rw [if_pos hl]
                · rw [if_neg hl, if_pos ⟨by omega, by omega⟩]; omega
              omega
            · rw [if_neg hcase]; omega
          omega
      have iA : ∀ (dA : ℕ) (fo : Bool), bd + 1 ≤ dA →
          readC (convC A dA y true fo) true y = translate A :=
        fun dA fo h => ih A hlA (bd + 1) dA y true fo hbA h hcA hdA
      have iB : readC (convC B d y false false) false y = translate B :=
        ih B hlB bd d y false false hbB hbd hcB hdB
      by_cases hl : ladOf y d plev first force = true
      · -- 影を挟む。`ladOf` から段は親の +1、`first` は真
        have hyp : y = plev + 1 := by simp [ladOf] at hl; omega
        have hf : first = true := by simp [ladOf] at hl; tauto
        have hdd1 : dd = d + 1 := by rw [hdd]; unfold ddOf; rw [if_pos hl]
        subst hf
        rcases hcc : contrLen (bd, y) B (sibRun (bd, y) B) A with _ | ⟨rest2, Bq⟩
        · -- 縮約なし
          rw [convC_cons_lad_none (bd, y) r d plev true force hl (by rw [← hAdef, ← hBdef]; exact hcc)]
          simp only [← hAdef, ← hBdef]
          have hXge : ∀ c ∈ convC A (d + 2) y true false, d + 1 < c.1 := by
            intro c hcm
            have := convC_ge' A (d + 2) y true false c hcm
            omega
          have hYh : convC B d y false false = [] ∨
              ¬ (d + 1 < ((convC B d y false false).headI).1) := by
            rcases hYshallow with h | h
            · exact Or.inl h
            · exact Or.inr (by omega)
          obtain ⟨e1, e2⟩ := split_append hXge hYh
          rw [readC_shadow (p := ((d, plev) : ℕ × ℕ)) (top := ((d + 1, y) : ℕ × ℕ))
            rfl rfl (by simp [hyp]) ?hnd]
          · simp only []
            rw [e1, e2, iA (d + 2) false (by omega), iB, translate]
          · case hnd =>
            simp only []
            rw [e2]
            exact convC_nodip B.length B (Nat.le_refl _) d y hyd hdB
              (fun hne => hdh hne)
        · -- 縮約あり
          rw [convC_cons_lad_some (bd, y) r d plev true force hl (by rw [← hAdef, ← hBdef]; exact hcc)]
          simp only [← hAdef, ← hBdef, List.append_assoc]
          obtain ⟨q, r2', hdq, hq2, hq1, hAq, hBq, hr2ne, hr2d, hr2l⟩ := contrLen_spec hcc
          set k := sibRun ((bd, y) : ℕ × ℕ) B with hk
          set X := convC A (d + 2) y true false with hX
          set Y := convC rest2 (d + 1) y false false with hY
          set Z := convC Bq d y false false with hZ
          -- B の分解
          have hBsplit : B = List.replicate k ((bd, y) : ℕ × ℕ) ++ (q :: r2') := by
            conv_lhs => rw [sibRun_split ((bd, y) : ℕ × ℕ) B]
            rw [← hk, hdq]
          -- rest2 / Bq の性質
          have hlr2 : rest2.length ≤ n := by
            have := (contrLen_lt hcc).1; omega
          have hlbq : Bq.length ≤ n := by
            have := (contrLen_lt hcc).2; omega
          have hcr2 : colOK rest2 := fun c hcm => hcB c ((contrLen_sublists hcc).1.subset hcm)
          have hcbq : colOK Bq := fun c hcm => hcB c ((contrLen_sublists hcc).2.subset hcm)
          -- ブロック規律と descOK を B から下ろす
          have hqcons : blockok bd (q :: r2') ∧ descOK (q :: r2') := by
            constructor
            · refine blockok_replicate bd y (q :: r2') (Or.inr ?_) k ?_
              · simp only [List.headI_cons]; omega
              · rw [← hBsplit]; exact hbB
            · refine descOK_replicate ((bd, y) : ℕ × ℕ) (q :: r2') (Or.inr ?_) k ?_
              · simp only [List.headI_cons]; omega
              · rw [← hBsplit]; exact hdB
          obtain ⟨hbq, hdq2⟩ := hqcons
          have hqe : q = (bd, q.2) := by
            simp only [] at hq1
            rw [← hq1]
          have hbCP : blockok (bd + 1) (contrPre ((bd, y) : ℕ × ℕ) k A ++ rest2) := by
            have h1 := blockok_arg (d := bd) (y := q.2) (r := r2') (by rw [← hqe]; exact hbq)
            simp only [] at h1 hq1
            rw [← hq1, hAq] at h1
            rw [hq1] at h1
            exact h1
          obtain ⟨hdCPh, hdCPa, hdCP⟩ := descOK_cons.1 (by
            have h1 := (descOK_cons.1
              (show descOK ((bd, q.2) :: r2') by rw [← hqe]; exact hdq2)).2.1
            simp only [] at h1 hq1
            rw [← hq1, hAq] at h1
            exact h1 : descOK (contrPre ((bd, y) : ℕ × ℕ) k A ++ rest2))
          -- rest2 の blockok / descOK
          have hAdeep : ∀ c ∈ shift1 A, bd + 1 < c.1 := by
            intro c hcm
            simp only [shift1, List.mem_map] at hcm
            obtain ⟨c', hc', rfl⟩ := hcm
            have h1 : bd < c'.1 := by
              have := List.mem_takeWhile_imp (p := fun q : ℕ × ℕ => decide (((bd, y) : ℕ × ℕ).1 < q.1))
                (by rw [hAdef] at hc'; exact hc')
              simpa using this
            simp only []
            omega
          have hRr : (List.replicate k ((bd + 1, y) : ℕ × ℕ) ++ rest2) = [] ∨
              ¬ (bd + 1 < ((List.replicate k ((bd + 1, y) : ℕ × ℕ) ++ rest2).headI).1) := by
            cases k with
            | zero => right; simp only [List.replicate_zero, List.nil_append]; omega
            | succ k' => right; rw [List.replicate_succ, List.cons_append]; simp
          have hCPe : contrPre ((bd, y) : ℕ × ℕ) k A ++ rest2
              = (bd + 1, y) :: (shift1 A ++ (List.replicate k ((bd + 1, y) : ℕ × ℕ) ++ rest2)) := by
            simp [contrPre]
          obtain ⟨eCP1, eCP2⟩ := split_append (dd := bd + 1) hAdeep hRr
          have hbr2 : blockok (bd + 1) rest2 := by
            refine blockok_replicate (bd + 1) y rest2 (Or.inr (by omega)) k ?_
            rw [hCPe] at hbCP
            have h1 := blockok_tail (d := bd + 1) (y := y) hbCP
            simp only [] at h1
            rw [eCP2] at h1
            exact h1
          have hdCPfull : descOK ((bd + 1, y) ::
              (shift1 A ++ (List.replicate k ((bd + 1, y) : ℕ × ℕ) ++ rest2))) := by
            rw [← hCPe]
            exact descOK_cons.2 ⟨hdCPh, hdCPa, hdCP⟩
          have hdr2 : descOK rest2 := by
            refine descOK_replicate ((bd + 1, y) : ℕ × ℕ) rest2 (Or.inr (by simp only []; omega)) k ?_
            have h1 := (descOK_cons.1 hdCPfull).2.2
            simp only [] at h1
            rw [eCP2] at h1
            exact h1
          have hdbq : descOK Bq := by
            rw [← hBq]
            have h1 := (descOK_cons.1
              (show descOK ((bd, q.2) :: r2') by rw [← hqe]; exact hdq2)).2.2
            simp only [] at h1 hq1
            rw [← hq1] at h1
            exact h1
          have hbbq : blockok bd Bq := by
            rw [← hBq]
            have h1 := blockok_tail (d := bd) (y := q.2) (by rw [← hqe]; exact hbq)
            simp only [] at h1 hq1
            rw [← hq1] at h1 ⊢
            exact h1
          -- 帰納法の仮定
          have iR : readC Y false y = translate rest2 :=
            ih rest2 hlr2 (bd + 1) (d + 1) y false false hbr2 (by omega) hcr2 hdr2
          have iQ : readC Z false y = translate Bq :=
            ih Bq hlbq bd d y false false hbbq hbd hcbq hdbq
          -- 出力の各部分の深さ
          have hYne : Y ≠ [] := by rw [hY, ne_eq, convC_eq_nil_iff]; exact hr2ne
          have hYhd : Y.headI = (d + 1, (rest2.headI).2) := by
            cases hre : rest2 with
            | nil => exact absurd hre hr2ne
            | cons c rest2' =>
              rw [hY, hre, convC_headI]
              have hcl : ladOf c.2 (d + 1) y false false = false := by simp [ladOf]
              rw [if_neg (by rw [hcl]; simp)]
              have hcy : c.2 < y := by rw [hre] at hr2l; simpa using hr2l
              have : ddOf c.2 (d + 1) y false false = d + 1 := by
                unfold ddOf
                rw [if_neg (by rw [hcl]; simp), if_neg (by intro hh; omega)]
              rw [this]
              simp
          have hYlev : (Y.headI).2 < y := by rw [hYhd]; simpa using hr2l
          have hYge : ∀ c ∈ Y, d + 1 ≤ c.1 := convC_ge' rest2 (d + 1) y false false
          have hZsh : Z = [] ∨ ((Z.headI).1 ≤ d ∧ ¬ (Z.headI = ((d + 1, y) : ℕ × ℕ))) := by
            cases hbe : Bq with
            | nil => left; rw [hZ, hbe, convC_nil]
            | cons c Bq' =>
              right
              have hcy : c.2 ≤ q.2 := by
                have h0 := (descOK_cons.1
                  (show descOK ((bd, q.2) :: r2') by rw [← hqe]; exact hdq2)).1
                simp only [] at h0 hq1
                rw [← hq1, hBq, hbe] at h0
                simpa using h0 (by simp)
              have hcd : c.2 < d := by omega
              have hcl : ladOf c.2 d y false false = false := by simp [ladOf]
              have hde : ddOf c.2 d y false false = d := by
                unfold ddOf
                rw [if_neg (by rw [hcl]; simp), if_neg (by intro hh; omega)]
              have : Z.headI = (d, c.2) := by
                rw [hZ, hbe, convC_headI, if_neg (by rw [hcl]; simp), hde]
              rw [this]
              exact ⟨Nat.le_refl d, by intro he; have := congrArg Prod.fst he; omega⟩
          -- 読みの分解
          have hXge : ∀ c ∈ X, d + 1 < c.1 := by
            intro c hcm
            have := convC_ge' A (d + 2) y true false c hcm
            omega
          have hRest : (List.replicate k ((d + 1, y) : ℕ × ℕ) ++ (Y ++ Z)) = [] ∨
              ¬ (d + 1 < ((List.replicate k ((d + 1, y) : ℕ × ℕ) ++ (Y ++ Z)).headI).1) := by
            cases k with
            | zero =>
              right
              simp only [List.replicate_zero, List.nil_append]
              rw [headI_append_left hYne, hYhd]
              omega
            | succ k' => right; rw [List.replicate_succ, List.cons_append]; simp
          obtain ⟨eT1, eT2⟩ := split_append hXge hRest
          have hYZne : (Y ++ Z) ≠ [] := by
            intro he; exact hYne (List.append_eq_nil_iff.1 he).1
          have hYZhd : (Y ++ Z).headI = Y.headI := headI_append_left hYne
          have hsib := takeDrop_replicate ((d + 1, y) : ℕ × ℕ) (Y ++ Z) (by
            rw [hYZhd]
            intro he
            rw [he] at hYlev
            simp only [] at hYlev
            omega) k
          -- 二役の条件
          have hdual : dipAt d y ((Y ++ Z)) := by
            refine ⟨hYZne, ?_, ?_⟩
            · rw [hYZhd, hYhd]
            · rw [hYZhd]; exact hYlev
          have hYZge : ∀ c ∈ Y, d + 1 ≤ c.1 := hYge
          have hZh : Z = [] ∨ ¬ (d + 1 ≤ ((Z.headI).1)) := by
            rcases hZsh with h | ⟨h, -⟩
            · exact Or.inl h
            · exact Or.inr (by omega)
          obtain ⟨eD1, eD2⟩ := split_append_le hYZge hZh
          -- 読み（外側）
          rw [readC_dual (p := ((d, plev) : ℕ × ℕ)) (top := ((d + 1, y) : ℕ × ℕ))
            rfl rfl (by simp [hyp])
            (by
              simp only []
              rw [eT2, hsib.2]
              exact hdual)]
          simp only []
          rw [eT1, eT2, hsib.1, hsib.2, eD1, eD2]
          simp only [List.append_assoc, List.length_replicate]
          -- 読み（内側）: 影ではないので素直に割れる
          have hinner : readC (((d + 1, y) : ℕ × ℕ) ::
                (X ++ (List.replicate k ((d + 1, y) : ℕ × ℕ) ++ Y))) true plev
              = Three.P y (readC X true y) (wrapN k y (readC Y false y)) := by
            have hRest2 : (List.replicate k ((d + 1, y) : ℕ × ℕ) ++ Y) = [] ∨
                ¬ (d + 1 < ((List.replicate k ((d + 1, y) : ℕ × ℕ) ++ Y).headI).1) := by
              cases k with
              | zero =>
                right
                simp only [List.replicate_zero, List.nil_append, hYhd]
                omega
              | succ k' => right; rw [List.replicate_succ, List.cons_append]; simp
            obtain ⟨eI1, eI2⟩ := split_append hXge hRest2
            rw [readC_plain (p := ((d + 1, y) : ℕ × ℕ)) (first := true) (plev := plev)
              (by rintro ⟨-, h2, -⟩; simp only [] at h2; omega)]
            simp only []
            rw [eI1, eI2]
            rw [readC_replicate ((d + 1, y) : ℕ × ℕ) Y (Or.inr (by rw [hYhd]; simp)) k y]
          rw [hinner, iA (d + 2) false (by omega), iR,
            readC_plev Z plev y, iQ]
          -- BMS 側
          have hAdeep2 : ∀ c ∈ A, bd < c.1 := by
            intro c hcm
            have := List.mem_takeWhile_imp
              (p := fun q : ℕ × ℕ => decide (((bd, y) : ℕ × ℕ).1 < q.1))
              (by rw [hAdef] at hcm; exact hcm)
            simpa using this
          have hTB : translate B = wrapN k y (translate (q :: r2')) := by
            rw [hBsplit]
            exact translate_replicate ((bd, y) : ℕ × ℕ) (q :: r2')
              (Or.inr (by simp only [List.headI_cons]; omega)) k
          have hTq : translate (q :: r2')
              = Three.P q.2 (translate (contrPre ((bd, y) : ℕ × ℕ) k A ++ rest2))
                  (translate Bq) := by
            conv_lhs => rw [hqe]
            rw [translate]
            simp only []
            simp only [] at hq1
            rw [← hq1, hAq, hBq]
            simp only [hq1]
          have hTCP : translate (contrPre ((bd, y) : ℕ × ℕ) k A ++ rest2)
              = Three.P y (translate A) (wrapN k y (translate rest2)) :=
            translate_contrPre ((bd, y) : ℕ × ℕ) k A rest2 hAdeep2
              (Or.inr (by simp only []; omega))
          rw [translate]
          simp only []
          rw [← hAdef, ← hBdef, hTB, hTq, hTCP]
          have hqp : q.2 = plev := by omega
          rw [hqp]
      · -- 影を挟まない
        have hdd0 : dd = ddOf y d plev first force := hdd
        rw [convC_cons_nolad (bd, y) r d plev first force (by simpa using hl)]
        simp only [← hAdef, ← hBdef, ← hdd0]
        have hXge : ∀ c ∈ convC A (dd + 1) y true (first && (y == plev)),
            dd < c.1 := by
          intro c hcm
          have := convC_ge' A (dd + 1) y true (first && (y == plev)) c hcm
          omega
        have hYh : convC B d y false false = [] ∨
            ¬ (dd < ((convC B d y false false).headI).1) := by
          rcases hYshallow with h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
        obtain ⟨e1, e2⟩ := split_append hXge hYh
        rw [readC_plain ?hne]
        · simp only []
          rw [e1, e2, iA (dd + 1) _ (by omega), iB, translate]
        · rintro ⟨hf, hlv, hhd⟩
          simp only [] at hlv hhd
          have hforce : (first && (y == plev)) = true := by
            rw [Bool.and_eq_true]
            exact ⟨hf, by simp [hlv]⟩
          rw [hforce] at hhd
          refine convC_head_ne_shadow (A := A) (B := B) (dd := dd) (d := d) (v := y) hddd ?_ hhd
          cases hBe : B with
          | nil => exact Or.inl rfl
          | cons q B' =>
            right
            have h0 := hdh (by rw [hBe]; simp)
            rw [hBe] at h0
            simp only [List.headI_cons] at h0 ⊢
            omega

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

/-- **主結果（縮約なし）**: BMS 2 行標準形なら、変換は無条件に読みを保つ。 -/
theorem readD_conv_ST {M : PairSeq} (hM : ST_PS M) : readD (conv M) true 0 = translate M :=
  readD_conv (blockok_ST_PS hM) (colOK_ST_PS hM) (descOK_ST_PS hM)

/-- 縮約つきの変換も読みを保つ。 -/
theorem readC_conC {M : PairSeq} (hb : blockok 0 M) (hc : colOK M) (hd : descOK M) :
    readCon (conC M) = translate M :=
  readC_convC M.length M (Nat.le_refl _) 0 0 0 true false hb (Nat.le_refl 0) hc hd

/-- **主結果（縮約つき）**: BMS 2 行標準形なら、`conC` は無条件に読みを保つ。 -/
theorem readC_conC_ST {M : PairSeq} (hM : ST_PS M) : readCon (conC M) = translate M :=
  readC_conC (blockok_ST_PS hM) (colOK_ST_PS hM) (descOK_ST_PS hM)

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

open Three in
/-- 縮約つきの変換も順序を保つ。 -/
theorem conC_olt_iff_seqlex {M N : PairSeq} (hM : ST_PS M) (hN : ST_PS N) (hne : M ≠ N) :
    (readCon (conC M) <o readCon (conC N) ↔ seqlex M N) := by
  rw [readC_conC_ST hM, readC_conC_ST hN]
  exact olt_iff_seqlex (blockok_ST_PS hM) (blockok_ST_PS hN) hne

open Three in
/-- 縮約つきの変換も単射。 -/
theorem conC_injective {M N : PairSeq} (hM : ST_PS M) (hN : ST_PS N)
    (h : conC M = conC N) : M = N := by
  by_contra hne
  rcases seqlex_total M N with he | hs | hs
  · exact hne he
  · have := (conC_olt_iff_seqlex hM hN hne).2 hs
    rw [h] at this
    exact olt_irrefl _ this
  · have := (conC_olt_iff_seqlex hN hM (Ne.symm hne)).2 hs
    rw [h] at this
    exact olt_irrefl _ this

end DBMS
