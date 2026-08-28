/-
3 行 DBMS の器（骨組み）。

BMS 側（`Trio.lean` の `ST_TS`, `oper`）はそのまま使う。DBMS は**展開規則が
BMS と完全に同一**で、違うのは標準形の対角だけ、というのが 2 行（`Dbms.lean`）
と同じ設計である。

    対角 diag[x][y]   BMS: x               DBMS: max(x - y, 0)

いま対象にしているのは z < 2 の断片なので、BMS 側の対角は z を 1 で頭打ちした
`diagSeqT 0 v = ((j, j, min j 1))_{j=0..v}` である。その像を実測すると

    b2d3 (0,0,0)(1,1,1)                     = (0,0,0)(1,0,0)(2,1,0)(3,2,1)
    b2d3 (0,0,0)(1,1,1)(2,2,1)              = (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,3,1)
    b2d3 (0,0,0)(1,1,1)(2,2,1)(3,3,1)       = (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,3,1)(5,4,1)

（`tools/dbms/rows3.py` の `b2d3`, v = 0..20 で確認）。つまり DBMS 側の対角も
**z を 1 で頭打ちした** `((j, j-1, min (j-2) 1))_{j=0..v}` である。素の
`(j, j-1, j-2)` は z ≥ 2 に出てしまうので、この断片の対角にはならない。

頭打ち対角が「本物の DBMS 対角の一手展開」であることも実測ずみ
（`core.expand`）:

    D5 = (0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,3,2)      … 5 列の素の DBMS 対角
    D5⟦n⟧ = ddiagSeqT (n + 2)                     (n ≥ 1)

BMS 側で `diagSeqT 0 v` が 3 列のトリオ対角の一手展開なのと同じ形である。
`core.isstd(ddiagSeqT v, 'DBMS')` も v = 0..9 で真。

## この器が固定するもの

* `ST_D3` : 3 行 DBMS の標準形（対角 + 展開の 2 構成子）。
* `ReindexT1` : 2 行の `ReindexD`（`DbmsStd.lean:1557`）の 3 行版。
  **性質 R（相手が `A⟦n'⟧` であること）は 3 行では偽**（`tools/dbms/NOTES.md`
  「性質 R（ReindexD）は 3 行で偽」）。降下が本当に要求しているのは
  「相手が BMS 標準形 `B` であること」だけなので、そこまで緩めてある。
* `ST_D3_descend` / `ST_D3_conv3` : `DbmsStd.lean:1578-1613` の写経。
  `A⟦n'⟧` を `B` に置き換えると `oper_mono` の行が仮定 `translate (A⟦n⟧) ≤o
  translate B` に吸収されて消える。

`conv3`（BMS -> DBMS の変換器、Python では `tools/dbms/rows3.py` の `b2d3`）は
§1-§7 では**関数変数として抽象化**してある。Python 側が保証すべき命題は
`ReindexT1` と `ConvDiagT3` の 2 つだけになる。

## §8 以降（2026-08-27 に足した分）

`conv3` の Lean 実装 `Conv3.conv3` / `Conv3.b2d3` を書いた（§8）。**縮約こみ**、
つまり `rows3.py` の `conv3` 設計 **v13** まるごとの写経である（2026-08-28 に
v13 の 2 条項 `wchain` / `sibL`+`sib_anchbefore` を足して追いつかせた）。
Python との突き合わせ（`tools/dbms/lean_v13_check.py`。Lean に `#eval` させた
像を書き出して Python の像と行ごとに diff する）:

    <=6 列の BMS 3 行 z<2 標準形 **8387 個を全数**        食い違い 0（115 秒）
    7 列（68895 個）のうち **v12 と像が違う 290 個ぜんぶ**
      ＋ **縮約が発火する 294 個ぜんぶ** ＋ 無作為 5000 個  食い違い 0（43 秒）

この file の `#guard` はその抜き取り（v13 で像が変わる <=6 列の 12 個は全部載せた）。

そのうえで `ConvDiagT3 Conv3.b2d3` を**証明した**（§9, §10）。
残るのは `ReindexT1` ただ 1 つ（`ST_D3_b2d3`）。
-/
import Core
import Decrease
import Seqlex
import Wset
import Final
import Cofidx

namespace TRIO

open Three
open Classical

/-! ## 0. `≤o` の小道具（2 行側の `DbmsStd.lean:53-63` の TRIO 版） -/

theorem ole_refl (x : Three) : x ≤o x := Or.inr rfl

theorem ole_trans {x y z : Three} (hxy : x ≤o y) (hyz : y ≤o z) : x ≤o z := by
  rcases hxy with h | rfl
  · exact Or.inl (olt_ole_trans h hyz)
  · exact hyz

theorem ole_olt_trans {x y z : Three} (hxy : x ≤o y) (hyz : y <o z) : x <o z := by
  rcases hxy with h | rfl
  · exact olt_trans h hyz
  · exact hyz

/-! ## 1. 3 行 DBMS の対角と標準形 -/

/-- DBMS の 3 行対角の第 `j` 列 `(j, j-1, min (j-2) 1)`（ℕ の切り捨て引き算）。
z を 1 で頭打ちしてあるのは、いま扱っているのが z < 2 の断片だから。 -/
def ddcolT (j : ℕ) : ℕ × ℕ × ℕ := (j, j - 1, min (j - 2) 1)

/-- DBMS の 3 行対角 `(0,0,0)(1,0,0)(2,1,0)(3,2,1)(4,3,1)…(v,v-1,1)`。 -/
def ddiagSeqT (v : ℕ) : TrioSeq := (List.range (v + 1)).map ddcolT

example : ddiagSeqT 0 = [(0, 0, 0)] := by decide
example : ddiagSeqT 6 =
    [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,1), (6,5,1)] := by decide

/-- 3 行 DBMS の標準形: 対角から展開 `M⟦n⟧`（`n ≥ 1`）で到達できるもの。
展開 `oper` は BMS と同一のもの（`Trio.lean`）を使う。 -/
inductive ST_D3 : TrioSeq → Prop where
  | diag (v : ℕ) : ST_D3 (ddiagSeqT v)
  | oper {M : TrioSeq} {n : ℕ} : ST_D3 M → 1 ≤ n → ST_D3 (M⟦n⟧)

/-! ### 1.1 `行 2 <= 行 1` は DBMS 側でも不変量（課題 L6）

BMS 側の同じ命題は `lean/L6Inv.lean` の `TRIO.L6.r21_ST_TS`。`Dbms3.lean` は
`lakefile.toml` の `roots` に入っていないので `L6Inv` を import できず、
**展開の枝だけ写している**（`Wset.zle1_oper` / `L6.r21_oper` と同じ骨）。

効き目は BMS 側と同じ: `Wset.no_hasParent_two_of_row1_zero` が使う
「永久孤児」`(x,0,1)`（行 1 = 0 かつ 行 2 > 0）が**標準形には現れない**。

実測（生成器の制約を使わず展開閉包を直に作ったもの）: DBMS 対角 `v = 0..7` から
`n ∈ {1,2,3}` で 6 段展開した 2923 個で `行 2 > 行 1` の柱 **0 個**。 -/

/-- 行 2 は行 1 を超えない（`Wset.zle1` より強い）。 -/
def r21D (M : TrioSeq) : Prop := ∀ p ∈ M, p.2.2 ≤ p.2.1

/-- DBMS の対角も満たす（`ddcolT j = (j, j-1, min (j-2) 1)`）。 -/
theorem r21D_ddiagSeqT (v : ℕ) : r21D (ddiagSeqT v) := by
  intro p hp
  unfold ddiagSeqT at hp
  rw [List.mem_map] at hp
  obtain ⟨j, -, rfl⟩ := hp
  unfold ddcolT
  dsimp only
  omega

/-- 展開で保たれる（`oper` は行 1 に非負を足し、行 2 は逐語コピーする）。 -/
theorem r21D_oper {B : TrioSeq} {n : ℕ} (h : r21D B) : r21D (B⟦n⟧) := by
  by_cases hL : B.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]; exact h
  · by_cases hp : hasParent B (srow B (B.length - 1)) (B.length - 1)
    · have hpos : 0 < entry B 0 (B.length - 1) := by
        by_contra hh
        exact no_hasParent_of_row0_zero (by omega) hp
      have hz : ¬ (entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
          entry B 2 (B.length - 1) = 0) := by
        rintro ⟨h1, -, -⟩; omega
      rw [oper_gcopies n hL hz hp]
      intro p hp'
      rcases List.mem_append.mp hp' with hmem | hmem
      · exact h p (List.mem_of_mem_take hmem)
      · unfold gcopies at hmem
        rw [List.mem_flatMap] at hmem
        obtain ⟨k, -, hmem2⟩ := hmem
        unfold gcopy at hmem2
        rw [List.mem_map] at hmem2
        obtain ⟨j, hj, rfl⟩ := hmem2
        rw [List.mem_range'] at hj
        have hjlt : j < B.length := by omega
        have := h _ (Wset.entry_pair_mem hjlt)
        dsimp only at this ⊢
        omega
    · have hB : B⟦n⟧ = Pred B := by
        by_cases hz : entry B 0 (B.length - 1) = 0 ∧ entry B 1 (B.length - 1) = 0 ∧
            entry B 2 (B.length - 1) = 0
        · exact oper_eq_pred_of_zero n hL hz
        · exact oper_eq_pred_of_noParent n hL hz hp
      rw [hB]
      unfold Pred
      split
      · exact h
      · exact fun p hp' => h p (List.dropLast_subset _ hp')

/-- **`行 2 <= 行 1` は DBMS 3 行 `z<2` 標準形の不変量。** -/
theorem r21D_ST_D3 {M : TrioSeq} (h : ST_D3 M) : r21D M := by
  induction h with
  | diag v => exact r21D_ddiagSeqT v
  | oper _ _ ih => exact r21D_oper ih

/-- 系: DBMS 標準形にも「永久孤児」`(x,0,1)` は現れない。 -/
theorem no_permanent_orphan_ST_D3 {M : TrioSeq} (h : ST_D3 M) :
    ∀ p ∈ M, p.2.1 = 0 → p.2.2 = 0 :=
  fun p hp h1 => Nat.le_zero.mp (h1 ▸ r21D_ST_D3 h p hp)

/-! ## 2. 変換器に課す 2 つの命題

`conv3 : TrioSeq → TrioSeq` は「BMS 3 行標準形 -> DBMS 3 行行列」の変換器。
Lean の実装はまだ無いので関数変数のまま置く。 -/

/-- **対角の像**（帰納法の底）。実測（`tools/dbms/rows3.py` の `b2d3`）:

    conv3 (diagSeqT 0 0) = ddiagSeqT 0
    conv3 (diagSeqT 0 v) = ddiagSeqT (v + 2)     (v ≥ 1)

像は入力より 2 列長い。2 行では 1 列長かった（`conC_diagSeq`）。 -/
def ConvDiagT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ v : ℕ, conv3 (diagSeqT 0 v) = if v = 0 then ddiagSeqT 0 else ddiagSeqT (v + 2)

/-- **ReindexT1** — 2 行の `ReindexD` の 3 行版。

`A` が BMS 3 行標準形で長さ 2 以上、`n ≥ 1` のとき、DBMS の添字 `m ≥ 1` と
**ある BMS 標準形 `B`** があって

    translate (A⟦n⟧) ≤o translate B     … 基本列に追い越されない（上）
    translate B <o translate A          … ちゃんと降りている（下）
    (conv3 A)⟦m⟧ = conv3 B              … 像は展開で閉じている

2 行版は `B = A⟦n'⟧`（`n ≤ n'`）だったが、**3 行ではそれが偽**である
（`tools/dbms/NOTES.md`「性質 R（ReindexD）は 3 行で偽（2026-08-27, 確定）」。
反例 `M = (0,0,0)(1,1,1)(2,1,0)(3,0,0)` は `f(M)⟦m⟧` と `f(M⟦n⟧)` が末尾 1 列
の行 1 で永久にすれ違う）。その反例でも `B_m = (0,0,0)(1,1,1)(2,1,0)^m
(1,1,0)(2,2,1)(3,2,0)^m` を取れば `ReindexT1` は満たされる（m = 1..6 で確認）。

`ST_D3_descend` が `ReindexD` を使う 2 か所のうち、DBMS 側の等号は落とせないが
BMS 側の `n ≤ n'` は `≤o` に翻訳されてからしか使われない。だから相手は
`A⟦n'⟧` である必要が無い、というのがこの緩和の根拠。 -/
def ReindexT1 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {A : TrioSeq}, ST_TS A → 1 < A.length → ∀ n : ℕ, 1 ≤ n →
    ∃ (m : ℕ) (B : TrioSeq), 1 ≤ m ∧ ST_TS B ∧
      translate (A⟦n⟧) ≤o translate B ∧
      translate B <o translate A ∧
      (conv3 A)⟦m⟧ = conv3 B

/-- `ConvDiagT3` から帰納法の底が出る。 -/
theorem ST_D3_conv3_diag {conv3 : TrioSeq → TrioSeq} (hd : ConvDiagT3 conv3) (v : ℕ) :
    ST_D3 (conv3 (diagSeqT 0 v)) := by
  rw [hd v]
  by_cases h : v = 0
  · simp only [h, if_true]; exact ST_D3.diag 0
  · simp only [if_neg h]; exact ST_D3.diag (v + 2)

/-! ## 3. 長さ 1 の標準形は最小（`DbmsStd.lean:68` の TRIO 版） -/

/-- `[(0,0,0)]` より真に小さい BMS 3 行標準形はない。 -/
theorem not_olt_len_one_T {M A : TrioSeq} (hM : ST_TS M) (hA : A.length ≤ 1)
    (hAst : ST_TS A) (h : translate M <o translate A) : False := by
  have h1 : A = [(0, 0, 0)] := Wset.stts_len_one hAst (by
    have := stps_len_pos hAst; omega)
  subst h1
  have hA0 : translate [((0 : ℕ), (0 : ℕ), (0 : ℕ))] = P 0 0 Z Z := by
    rw [translate]; simp
  obtain ⟨p, R, rfl⟩ := List.exists_cons_of_ne_nil (Wset.stts_ne_nil hM)
  rw [hA0, translate] at h
  rcases olt_P_P.mp h with h | ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩
  · omega
  · omega
  · exact not_olt_Z _ h
  · exact not_olt_Z _ h

/-! ## 4. 対角は標準形の中で共終（`DbmsStd.lean:87` の TRIO 版） -/

/-- どの BMS 3 行標準形も、ある z 頭打ち対角以下。 -/
theorem diag_cofinal_T {M : TrioSeq} (hM : ST_TS M) :
    ∃ v, translate M ≤o translate (diagSeqT 0 v) := by
  induction hM with
  | diag v => exact ⟨v, ole_refl _⟩
  | @oper N n hN hn ih =>
      obtain ⟨v, hv⟩ := ih
      by_cases hL : 1 < N.length
      · exact ⟨v, ole_trans (Or.inl (m_step_decreases hL hn)) hv⟩
      · have hs : N⟦n⟧ = N := oper_eq_self_of_short n (by omega)
        rw [hs]; exact ⟨v, hv⟩

/-! ## 5. 降下（`DbmsStd.lean:1578` の写経） -/

/-- 降下の本体: 標準形の像 `conv3 A` が DBMS 標準形なら、`A` 以下の
BMS 標準形の像もすべて DBMS 標準形。

`A` についての整礎帰納法。`wf` は `Final.lean` の `wf_olt_ST_TS_holds`
（`TowerGraft2` と `TowerExp` の 2 核が残っている）でも、それを閉じた後の
無条件版でも良いように、仮定として受け取る。

2 行版との差は 1 行だけ: `oper_mono hnn` と `ole_trans hMn hmono` の 2 行が、
`ReindexT1` が直に渡してくる `translate (A⟦n⟧) ≤o translate B` に吸収されて
`ole_trans hMn hAnB` の 1 行になる。 -/
theorem ST_D3_descend
    (wf : WellFounded
      (fun a b : TrioSeq => ST_TS a ∧ ST_TS b ∧ translate a <o translate b))
    {conv3 : TrioSeq → TrioSeq} (H : ReindexT1 conv3) :
    ∀ A : TrioSeq, ST_TS A → ST_D3 (conv3 A) →
      ∀ M : TrioSeq, ST_TS M → translate M ≤o translate A → ST_D3 (conv3 M) := by
  intro A
  induction A using wf.induction with
  | _ A ih =>
    intro hA hSD M hM hle
    rcases hle with hlt | heq
    · -- `translate M <o translate A`: 一段降ろす
      have hL : 1 < A.length := by
        by_contra hL
        exact not_olt_len_one_T hM (by omega) hA hlt
      obtain ⟨n, hn, hMn⟩ := trio_cofinality hA hM hlt
      obtain ⟨m, B, hm, hB, hAnB, hBA, heqC⟩ := H hA hL n hn
      have hSD' : ST_D3 (conv3 B) := by
        rw [← heqC]; exact ST_D3.oper hSD hm
      exact ih B ⟨hB, hA, hBA⟩ hB hSD' M hM (ole_trans hMn hAnB)
    · -- `translate M = translate A`: `M = A`
      have hMA : M = A := by
        by_contra hne
        rcases seqlex_total M A with he | hs | hs
        · exact hne he
        · exact olt_irrefl _ (heq ▸ (olt_ST_iff_seqlex hM hA hne).2 hs)
        · exact olt_irrefl _ (heq ▸ (olt_ST_iff_seqlex hA hM (Ne.symm hne)).2 hs)
      rw [hMA]; exact hSD

/-! ## 5.5 課題 L36: **整礎性を DBMS 側に載せ替える**

`ST_D3_descend` は **BMS の整礎性**（`Final.lean` の残核 `TowerGraft2` / `TowerExp`）を
仮定している。つまり**変換の道が、証明したいものを仮定している**。これを切る。

`wf` が使われるのは `ST_D3_descend` の 1 か所だけで、再帰の根拠は
`translate B <o translate A`（BMS の順序）である。`B` は
`(conv3 A)⟦m⟧ = conv3 B` を満たすので、**DBMS 側では `conv3 B` が `conv3 A` の
基本列の元**である。そこで整礎性を **DBMS の `seqlex`** で取り、
`InvImage` で `A` の帰納に載せ替える。

★ **副産物**: 再帰の根拠の 3 つ目 `seqlex (conv3 B) (conv3 A)` は
`ImgBlockT3` ＋ `ImgLenT3` から**無料で出る**（`seqlex_oper`）ので、
**`OrderReindexT3` の第 2 成分（`seqlex (conv3 B) (conv3 A) → translate B <o translate A`）
が仮定から消える**。

⚠ `translateD` も DBMS 版 `m_step_decreases` も `trio_cofinality` の DBMS 版も
**要らない**（`seqlex` で取るので下がることは `seqlex_oper` が言う）。
`heq` の枝は `wf` を使っていないので**そのまま**である。 -/

/-- **DBMS 3 行 (z<2) の整礎性**（`seqlex` 版）。BMS 側の
`fun a b => ST_TS a ∧ ST_TS b ∧ translate a <o translate b` の DBMS 版。 -/
def RD3 : TrioSeq → TrioSeq → Prop :=
  fun x y => ST_D3 x ∧ ST_D3 y ∧ seqlex x y

/-- `ReindexT1` の DBMS 版。`translate B <o translate A`（BMS の順序）を
**像側の `seqlex`** に取り替えたもの。 -/
def ReindexT1D (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {A : TrioSeq}, ST_TS A → 1 < A.length → ∀ n : ℕ, 1 ≤ n →
    ∃ (m : ℕ) (B : TrioSeq), 1 ≤ m ∧ ST_TS B ∧
      translate (A⟦n⟧) ≤o translate B ∧
      seqlex (conv3 B) (conv3 A) ∧
      (conv3 A)⟦m⟧ = conv3 B

/-- **★★ 降下を DBMS の整礎性で回す版**（`ST_D3_descend` の写し）。 -/
theorem ST_D3_descend_D (wfD : WellFounded RD3)
    {conv3 : TrioSeq → TrioSeq} (H : ReindexT1D conv3) :
    ∀ A : TrioSeq, ST_TS A → ST_D3 (conv3 A) →
      ∀ M : TrioSeq, ST_TS M → translate M ≤o translate A → ST_D3 (conv3 M) := by
  intro A
  induction A using (InvImage.wf conv3 wfD).induction with
  | _ A ih =>
    intro hA hSD M hM hle
    rcases hle with hlt | heq
    · have hL : 1 < A.length := by
        by_contra hL
        exact not_olt_len_one_T hM (by omega) hA hlt
      obtain ⟨n, hn, hMn⟩ := trio_cofinality hA hM hlt
      obtain ⟨m, B, hm, hB, hAnB, hsq, heqC⟩ := H hA hL n hn
      have hSD' : ST_D3 (conv3 B) := by
        rw [← heqC]; exact ST_D3.oper hSD hm
      exact ih B ⟨hSD', hSD, hsq⟩ hB hSD' M hM (ole_trans hMn hAnB)
    · have hMA : M = A := by
        by_contra hne
        rcases seqlex_total M A with he | hs | hs
        · exact hne he
        · exact olt_irrefl _ (heq ▸ (olt_ST_iff_seqlex hM hA hne).2 hs)
        · exact olt_irrefl _ (heq ▸ (olt_ST_iff_seqlex hA hM (Ne.symm hne)).2 hs)
      rw [hMA]; exact hSD

/-- **★★★ 像は DBMS 標準形（DBMS の整礎性から）。BMS の残核を使わない。** -/
theorem ST_D3_conv3_D (wfD : WellFounded RD3)
    {conv3 : TrioSeq → TrioSeq} (H : ReindexT1D conv3) (hd : ConvDiagT3 conv3)
    {M : TrioSeq} (hM : ST_TS M) : ST_D3 (conv3 M) := by
  obtain ⟨v, hv⟩ := diag_cofinal_T hM
  exact ST_D3_descend_D wfD H (diagSeqT 0 v) (ST_TS.diag v)
    (ST_D3_conv3_diag hd v) M hM hv

/-! ## 5.6 課題 L38: **DBMS の停止性から BMS の停止性へ**

`ReindexT1D` は `(conv3 B_i)⟦m⟧ = conv3 B_{i+1}` を**等式で**くれるので、
DBMS 側の列は**定義から**展開列になる。⟹ **`conv3` の順序は 1 度も登場しない。**

無限降下列を作らなくても、**`Acc` の入れ子**で直に書ける:

    `Acc RD3 (conv3 A)` についての帰納で `Acc R A` を出す
      `R a A`（＝ `translate a <o translate A`）が与えられたら
        `trio_cofinality` で `n`、`ReindexT1D` で `B` を取る
        `RD3 (conv3 B) (conv3 A)` は `ReindexT1D` の 3 つ目と `ST_D3.oper` で出る
        帰納法の仮定から `Acc R B`
        `translate a ≤o translate B` なので `Acc.inv` か `a = B` で `Acc R a` ∎ -/

/-- **★ `Acc RD3 (conv3 A)` から `Acc` を BMS 側に移す。** -/
theorem acc_olt_of_accD {conv3 : TrioSeq → TrioSeq} (H : ReindexT1D conv3) :
    ∀ C : TrioSeq, Acc RD3 C → ∀ A : TrioSeq, ST_TS A → ST_D3 (conv3 A) →
      conv3 A = C →
      Acc (fun a b : TrioSeq => ST_TS a ∧ ST_TS b ∧ translate a <o translate b) A := by
  intro C hC
  induction hC with
  | intro C _ ih =>
    intro A hA hSD hCA
    refine Acc.intro _ ?_
    intro a ha
    obtain ⟨haS, -, hlt⟩ := ha
    have hL : 1 < A.length := by
      by_contra hL
      exact not_olt_len_one_T haS (by omega) hA hlt
    obtain ⟨n, hn, han⟩ := trio_cofinality hA haS hlt
    obtain ⟨m, B, hm, hB, hAnB, hsq, heqC⟩ := H hA hL n hn
    have hSD' : ST_D3 (conv3 B) := by rw [← heqC]; exact ST_D3.oper hSD hm
    have hAccB : Acc (fun a b : TrioSeq =>
        ST_TS a ∧ ST_TS b ∧ translate a <o translate b) B :=
      ih (conv3 B) (by rw [← hCA]; exact ⟨hSD', hSD, hsq⟩) B hB hSD' rfl
    rcases ole_trans han hAnB with hab | hab
    · exact hAccB.inv ⟨haS, hB, hab⟩
    · have haB : a = B := by
        by_contra hne
        rcases seqlex_total a B with he | hs | hs
        · exact hne he
        · exact olt_irrefl _ (hab ▸ (olt_ST_iff_seqlex haS hB hne).2 hs)
        · exact olt_irrefl _ (hab ▸ (olt_ST_iff_seqlex hB haS (Ne.symm hne)).2 hs)
      rw [haB]; exact hAccB

/-- **★★★ DBMS 3 行 (z<2) の整礎性 ⟹ BMS 3 行 (z<2) の整礎性。**

`Final.wf_Rnf_of_wf_TS` ＋ `Reduction.step_terminates` と繋げば
**BMS 3 行 (z<2) の停止性**（`WellFounded stepRel`）になる。
`Dbms3.lean` は `lakefile.toml` の `roots` に無いので、その 2 段は
`Final.lean` の側で繋ぐこと。 -/
theorem wf_olt_ST_TS_of_dbms (wfD : WellFounded RD3)
    {conv3 : TrioSeq → TrioSeq} (H : ReindexT1D conv3) (hd : ConvDiagT3 conv3) :
    WellFounded
      (fun a b : TrioSeq => ST_TS a ∧ ST_TS b ∧ translate a <o translate b) := by
  refine ⟨fun A => ?_⟩
  by_cases hA : ST_TS A
  · exact acc_olt_of_accD H (conv3 A) (wfD.apply _) A hA
      (ST_D3_conv3_D wfD H hd hA) rfl
  · exact Acc.intro _ (fun a h => absurd h.2.1 hA)

/-- **★★★★ DBMS 3 行 (z<2) の停止性 ⟹ BMS 3 行 (z<2) の停止性。**

`Final.wf_Rnf_of_wf_TS` ＋ `Reduction.step_terminates` で繋いだ形。
**残核 `TowerGraft2` / `TowerExp` を使わない。** -/
theorem TRIO_terminates_of_dbms_wf (wfD : WellFounded RD3)
    {conv3 : TrioSeq → TrioSeq} (H : ReindexT1D conv3) (hd : ConvDiagT3 conv3) :
    WellFounded stepRel :=
  step_terminates (wf_Rnf_of_wf_TS (wf_olt_ST_TS_of_dbms wfD H hd))

/-- 同じものを「無限展開列は無い」の形で。 -/
theorem no_infinite_expansion_of_dbms_wf (wfD : WellFounded RD3)
    {conv3 : TrioSeq → TrioSeq} (H : ReindexT1D conv3) (hd : ConvDiagT3 conv3) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion (wf_Rnf_of_wf_TS (wf_olt_ST_TS_of_dbms wfD H hd))

/-! ### 課題 L41: `RD3` を**像に制限**すると `ST_D3` がまるごと落ちる

`acc_olt_of_accD` が `ST_D3 (conv3 A)` を運んでいたのは、**`RD3` の第 1・第 2 成分を
埋めるためだけ**だった。`RD3` を「`conv3` の像の上の `seqlex`」に取り替えると、
その 2 成分は `⟨B, hB, rfl⟩` / `⟨A, hA, rfl⟩` で**自明に**埋まる。

    落ちるもの   `ST_D3_conv3_D`（したがって `ST_D3_descend_D`）、`ConvDiagT3`、
                 `ST_D3` の機構ぜんぶ
    残るもの     `ReindexT1D` ただ 1 本

そして**非全射の穴が消える**: `conv3` は全射でない（`<=8` 列で 1171/27932 ＝ 4.2%、
率は列数とともに増える）ので `WellFounded RD3` は BMS の停止性より**形式的に強い**が、
`WellFounded (RD3img conv3)` は像の上だけなので**その代償を払わない**。

⚠ ただし `RD3img` の整礎性は、`Inj3` を通せば `ST_TS` 上の関係
`M ≺ N ⟺ seqlex (conv3 M) (conv3 N)` の整礎性と同じで、
**BMS の停止性より易しい保証は無い**（`OrderT3` が偽なので `seqlex M N` とは
別の関係だが、強さが違うとは限らない）。値打ちは「前提が真に弱い」ことと
「`ST_D3` の機構が停止性の道から外れる」ことにある。 -/
def RD3img (conv3 : TrioSeq → TrioSeq) : TrioSeq → TrioSeq → Prop :=
  fun x y => (∃ M, ST_TS M ∧ x = conv3 M) ∧ (∃ N, ST_TS N ∧ y = conv3 N) ∧ seqlex x y

/-- **★ `Acc (RD3img conv3) (conv3 A)` から `Acc` を BMS 側に移す**（課題 L41）。
`acc_olt_of_accD` から `ST_D3` の 2 行を落としただけ。 -/
theorem acc_olt_of_accImg {conv3 : TrioSeq → TrioSeq} (H : ReindexT1D conv3) :
    ∀ C : TrioSeq, Acc (RD3img conv3) C → ∀ A : TrioSeq, ST_TS A →
      conv3 A = C →
      Acc (fun a b : TrioSeq => ST_TS a ∧ ST_TS b ∧ translate a <o translate b) A := by
  intro C hC
  induction hC with
  | intro C _ ih =>
    intro A hA hCA
    refine Acc.intro _ ?_
    intro a ha
    obtain ⟨haS, -, hlt⟩ := ha
    have hL : 1 < A.length := by
      by_contra hL
      exact not_olt_len_one_T haS (by omega) hA hlt
    obtain ⟨n, hn, han⟩ := trio_cofinality hA haS hlt
    obtain ⟨m, B, hm, hB, hAnB, hsq, heqC⟩ := H hA hL n hn
    have hAccB : Acc (fun a b : TrioSeq =>
        ST_TS a ∧ ST_TS b ∧ translate a <o translate b) B :=
      ih (conv3 B) (by rw [← hCA]; exact ⟨⟨B, hB, rfl⟩, ⟨A, hA, rfl⟩, hsq⟩) B hB rfl
    rcases ole_trans han hAnB with hab | hab
    · exact hAccB.inv ⟨haS, hB, hab⟩
    · have haB : a = B := by
        by_contra hne
        rcases seqlex_total a B with he | hs | hs
        · exact hne he
        · exact olt_irrefl _ (hab ▸ (olt_ST_iff_seqlex haS hB hne).2 hs)
        · exact olt_irrefl _ (hab ▸ (olt_ST_iff_seqlex hB haS (Ne.symm hne)).2 hs)
      rw [haB]; exact hAccB

/-- **★★ 像の整礎性 ⟹ BMS の整礎性**（`ConvDiagT3` も `ST_D3` も要らない）。 -/
theorem wf_olt_ST_TS_of_img {conv3 : TrioSeq → TrioSeq}
    (wf : WellFounded (RD3img conv3)) (H : ReindexT1D conv3) :
    WellFounded
      (fun a b : TrioSeq => ST_TS a ∧ ST_TS b ∧ translate a <o translate b) := by
  refine ⟨fun A => ?_⟩
  by_cases hA : ST_TS A
  · exact acc_olt_of_accImg H (conv3 A) (wf.apply _) A hA rfl
  · exact Acc.intro _ (fun a h => absurd h.2.1 hA)

/-- **★★★★ 像の整礎性 ⟹ BMS 3 行 (z<2) の停止性**（課題 L41）。
仮定は **`ReindexT1D` ただ 1 本**。`ST_D3` / `ConvDiagT3` / 残核すべて不要。 -/
theorem TRIO_terminates_of_img_wf {conv3 : TrioSeq → TrioSeq}
    (wf : WellFounded (RD3img conv3)) (H : ReindexT1D conv3) : WellFounded stepRel :=
  step_terminates (wf_Rnf_of_wf_TS (wf_olt_ST_TS_of_img wf H))

/-- 同じものを「無限展開列は無い」の形で。 -/
theorem no_infinite_expansion_of_img_wf {conv3 : TrioSeq → TrioSeq}
    (wf : WellFounded (RD3img conv3)) (H : ReindexT1D conv3) :
    ¬ ∃ S : ℕ → TrioSeq, (∀ i, ST_TS (S i)) ∧ ∀ i, step (S i) (S (i + 1)) :=
  no_infinite_expansion (wf_Rnf_of_wf_TS (wf_olt_ST_TS_of_img wf H))

/-- **課題 L38 は L41 の系**: `WellFounded RD3 → WellFounded (RD3img conv3)`。
逆は言えない（`conv3` は全射でないので `RD3` のほうが真に強い）。 -/
theorem wf_img_of_wfD (wfD : WellFounded RD3) {conv3 : TrioSeq → TrioSeq}
    (H : ReindexT1D conv3) (hd : ConvDiagT3 conv3) :
    WellFounded (RD3img conv3) := by
  have hsub : Subrelation (RD3img conv3) RD3 := by
    intro x y h
    obtain ⟨⟨M, hM, hx⟩, ⟨N, hN, hy⟩, hsq⟩ := h
    refine ⟨?_, ?_, hsq⟩
    · rw [hx]; exact ST_D3_conv3_D wfD H hd hM
    · rw [hy]; exact ST_D3_conv3_D wfD H hd hN
  exact hsub.wf wfD

/-! ## 6. 主定理 -/

/-- **像は DBMS の 3 行標準形**（`ReindexT1` と `ConvDiagT3` を仮定）。 -/
theorem ST_D3_conv3
    (wf : WellFounded
      (fun a b : TrioSeq => ST_TS a ∧ ST_TS b ∧ translate a <o translate b))
    {conv3 : TrioSeq → TrioSeq} (H : ReindexT1 conv3) (hd : ConvDiagT3 conv3)
    {M : TrioSeq} (hM : ST_TS M) : ST_D3 (conv3 M) := by
  obtain ⟨v, hv⟩ := diag_cofinal_T hM
  exact ST_D3_descend wf H (diagSeqT 0 v) (ST_TS.diag v) (ST_D3_conv3_diag hd v) M hM hv

/-! ## 7. いまの仮定をぜんぶ並べた形 -/

/-- 3 行の器を、現時点で残っている仮定を全部明示して組み立てたもの。

* `h2`, `he` … BMS 側の整礎性に残る 2 核（`Final.lean` の
  `wf_olt_ST_TS_holds`）。3 行 BMS の停止性そのものの残核で、
  DBMS とは無関係。
* `H`  … `ReindexT1`（変換器の像が展開で閉じ、順序でも挟まれる）。
* `hd` … `ConvDiagT3`（対角の像が DBMS 対角）。

`H` と `hd` の 2 つが、Python 側（`tools/dbms/rows3.py` の `b2d3`）が
保証すべきものの全部である。 -/
theorem ST_D3_conv3_holds (h2 : Wset.TowerGraft2) (he : Wset.TowerExp)
    {conv3 : TrioSeq → TrioSeq} (H : ReindexT1 conv3) (hd : ConvDiagT3 conv3)
    {M : TrioSeq} (hM : ST_TS M) : ST_D3 (conv3 M) :=
  ST_D3_conv3 (wf_olt_ST_TS_holds h2 he) H hd hM


/-! ## 8. 変換器 `conv3` の Lean 実装

`tools/dbms/rows3.py` の `conv3`（設計 v11）の写経。**縮約こみ**である。

Python の `conv3` は状態 `st` を**破壊的に**持ち回るので、Lean では
`TrioSeq × St` を返して線形に渡す。`cA` を先に走らせて、その状態で `cU`,
`cR`, `cB` を走らせる、という順序が Python の副作用の順序に対応する。

縮約には `conv3` と `conv_resid` の**相互再帰**が要る。`conv_resid` は残余の
先頭ブロックを丸ごと `conv3` に渡すので列数が減らないことがあり、素朴な
「列数」では停止しない。尺度を `conv3 -> 2 * M.length`,
`convResid -> 2 * rest.length + 1` に取ると 1 本の ℕ で足りる:

    conv3 M    -> conv3 A/U/Bq     列数が真に減る          2a   < 2m
    conv3 M    -> convResid rest2  列数が真に減る          2r+1 < 2m
    convResid  -> conv3 head       列数は減らなくてよい    2h   < 2r+1
    convResid  -> convResid tail   列数が真に減る          2t+1 < 2r+1

`A`/`B` は `takeWhile`/`dropWhile` のままだが、縮約の断片（`U`, `Aq`, `Bq`,
`rest2`）は `take`/`drop` と長さ `deepGe` で作ってある。そうすると長さの上界が
`List.length_take` / `List.length_drop` だけで出て、`decreasing_by` が
`omega` 一発で閉じる。

**Python との突き合わせ**: <=6 列の標準形 8387 個を全数 `#guard` して食い違い 0
（149 秒）。7 列は「縮約が発火する 294 個ぜんぶ ＋ 無作為 5000 個」で 0（74 秒）。
下にはそのうちの一部（<=6 列で縮約が発火するもの全部と、6/7 列の抜き取り）を
残してある。

縮約が発火するのは稀で、<=7 列 77282 個のうち 338 個（0.44%）だけ
（`rows3.b2d3n` の第 2 成分 `nc` で数えた: 5 列 5 / 6 列 39 / 7 列 294）。 -/

namespace Conv3

/-- 列。 -/
abbrev Col := ℕ × ℕ × ℕ

/-- 段の表 `L` の 1 項
`(深い側の行 1, その行 2, force1, 浅い側の行 1, 兄弟だけが使える深い側)`。

第 5 項は v13 の `sibL`（`rows3.py` の `L` の第 5 要素）。行 1 の影を立てた柱が
**兄弟にだけ**渡す深い側である。Python では第 5 要素が「無い」4 つ組があって、
そのとき `base_sd = e[0]` と読む約束なので、Lean では「無い」を
**第 5 項 = 第 1 項**で表す。 -/
abbrev Lent := ℕ × ℕ × Bool × ℕ × ℕ

/-- 引数に渡す表 `LA` を作るときの潰し（Python の `tuple(t[:4] for t in LA)`）。
第 5 項を第 1 項に戻す＝「兄弟の深い側は子には渡さない」。 -/
def lentTrunc (t : Lent) : Lent := (t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.1)

/-- 線形に持ち回る状態（Python の辞書 `st`）。 -/
structure St where
  /-- 祖先の鎖（深さ -> (行 1, 行 2)）。 -/
  ST : List (ℕ × ℕ)
  /-- 直前の分岐列の選択。`0` 浅い / `1` 深い / `2` まだ無い（Python の `None`）。 -/
  prev : ℕ
  /-- もとの深さ -> 像の深さ。 -/
  dmap : List ℕ
  /-- もとの行列まるごと。 -/
  Mo : TrioSeq
  /-- 縮約が発火した回数。 -/
  nc : ℕ
  /-- v12 `mark` 用の記録（もとの添字 -> 「決める直前の段」）。
  値の符号は `0` 浅い / `1` 深い / `2` まだ無い（Python の `None`）/
  `3` 選択肢が無い（Python の `'tie'`）。引けなければ `4`（Python の `'none'`）。
  **像には効かない**（読むのは `leavesMark` だけ）。名前が `rec` だと自動生成の
  再帰子 `St.rec` とぶつかるので `rc`。 -/
  rc : List (ℕ × ℕ)
deriving Repr, DecidableEq

/-- `Lat L k`: 段の表の第 `k` 項。表の外は 1 段ずつ伸ばして読む。 -/
def Lat (L : List Lent) (k : ℕ) : Lent :=
  match L[k]? with
  | some e => e
  | none =>
      match L.getLast? with
      | none => (0, 0, false, 0, 0)
      | some a =>
          (a.1 + (k + 1 - L.length), a.2.1, false, a.2.2.2.1 + (k + 1 - L.length),
            a.1 + (k + 1 - L.length))

/-- `padL L v`: 長さ `v` まで `Lat` で埋めてから切る。 -/
def padL (L : List Lent) (v : ℕ) : List Lent :=
  if L.length < v then (List.range v).map (fun k => Lat L k) else L.take v

/-- 深さ `x` に行 1 が `w` の柱を置けるか。 -/
def okPlace (ST : List (ℕ × ℕ)) (x w : ℕ) : Bool :=
  if w = 0 then true
  else if x ≤ w then false
  else
    match (ST.take x).reverse.find? (fun e => decide (e.1 < w)) with
    | some e => e.1 == w - 1
    | none => false

/-- `fit` の本体（燃料つき）。 -/
def fitAux (ST : List (ℕ × ℕ)) (w : ℕ) : ℕ → ℕ → Option ℕ
  | _, 0 => none
  | x, (k + 1) => if okPlace ST x w then some x else fitAux ST w (x + 1) k

/-- 深さ `d` 以上で行 1 が `w` になれる最小の深さ。 -/
def fit (ST : List (ℕ × ℕ)) (d w : ℕ) : Option ℕ :=
  fitAux ST w d (ST.length + 1 - d)

/-- 分岐列 `(a,1,0)`（`a ≥ 2`）。浅い／深いを選ぶのはこの型だけ。 -/
def isBranch (c : Col) : Bool := c.2.1 == 1 && c.2.2 == 0 && decide (2 ≤ c.1)

/-- 次の列がこの加算ユニットを閉じるか。 -/
def closesUnit : Option Col → Bool
  | none => true
  | some c => decide (c.1 ≤ 1) && c.2.2 == 0

/-- 「x w」の柱 `(k,0,0)`（`k ≥ 1`）。 -/
def isWCol : Option Col → Bool
  | none => false
  | some c => c.2.1 == 0 && decide (1 ≤ c.1)

/-- `par0` の本体（`q = x-1` から下へ）。 -/
def par0Aux (m : TrioSeq) (w : ℕ) : ℕ → Option ℕ
  | 0 => none
  | (q + 1) => if (m.getD q (0,0,0)).1 < w then some q else par0Aux m w q

/-- 柱 `x` の行 0 の親の添字。 -/
def par0 (m : TrioSeq) (x : ℕ) : Option ℕ := par0Aux m (m.getD x (0,0,0)).1 x

/-- `x` の直前のアンカーの添字（無ければ 0）。 -/
def hiB (m : TrioSeq) : ℕ → ℕ
  | 0 => 0
  | (q + 1) =>
      let c := m.getD q (0,0,0)
      if c.1 = c.2.1 ∧ 1 ≤ c.1 then q else hiB m q

/-- `x` の属するブロックに行 2 を使う柱があるか（W_(w^2) 系の目印）。 -/
def hiBlock (m : TrioSeq) (x : ℕ) : Bool :=
  ((List.range x).drop (hiB m x + 1)).any
    (fun z => decide (0 < (m.getD z (0,0,0)).2.2))

/-! ### v14 h1（課題 H1）: 「写しの頭」を行列から直に読む述語

BMS の展開は「悪い部分を**上昇させて**写す」。上昇は行 0 に効くので、もとの根
`(0,0,0)` は写しの中で `(k,0,0)` に、アンカー `(1,1,0)` は `(k,1,0)` に化ける。
だから `(k,0,0)` の親の鎖をたどって根まで届けば、その柱は**写しの頭**である。
どれも `Mo` と添字だけで決まるので**写しに同変**（`st` を持ち回らない）。

もとの行列（写しの頭が 1 つも無いもの）では `termTop` は「根とアンカー」、
`closesTop` は `closesUnit`、`hiBlock2` は `hiBlock` にそのまま戻る。
だから**シートは 1 行も動かない**（`tools/dbms/H1-NOTES.md` §11）。 -/

/-- `termTop` の本体（燃料つき。`par0` は添字を真に減らすので `j + 1` で足りる）。 -/
def termTopAux (Mo : TrioSeq) : ℕ → ℕ → Bool
  | _, 0 => false
  | j, (f + 1) =>
      let c := Mo.getD j (0, 0, 0)
      if c.1 = 0 ∨ c = ((1, 1, 0) : Col) then true
      else if c.2.2 ≠ 0 then false
      else
        match par0 Mo j with
        | none => false
        | some q =>
            let pc := Mo.getD q (0, 0, 0)
            if c.2.1 = 0 then termTopAux Mo q f          -- 根の写し `(k,0,0)`
            else if c.2.1 = 1 then
              -- アンカーの写し `(k,1,0)`。親が根そのものか、根の写しのときだけ。
              decide (pc.1 = 0) || (decide (pc.2.1 = 0 ∧ pc.2.2 = 0) && termTopAux Mo q f)
            else false

/-- 柱 `j` が「行 1 の加算項の頭」か（`rows3.py` の `term_top`）。
もとの行列では 根 `(0,*,*)` と アンカー `(1,1,0)` の 2 つ。 -/
def termTop (Mo : TrioSeq) (j : ℕ) : Bool := termTopAux Mo j (j + 1)

/-- 柱 `j` が**写しの頭**か（`rows3.py` の `copy_head`）。
`(k,0,0)` `k ≥ 1` で、行 0 の親が「行 1 の加算項の頭」。 -/
def copyHead (Mo : TrioSeq) (j : ℕ) : Bool :=
  let c := Mo.getD j (0, 0, 0)
  if c.2.1 = 0 ∧ c.2.2 = 0 ∧ 1 ≤ c.1 then
    match par0 Mo j with
    | none => false
    | some q => termTop Mo q
  else false

/-- 柱 `j` が「いまの写しの根の直下」か（`rows3.py` の `top_level`）。 -/
def topLevel (Mo : TrioSeq) (j : ℕ) : Bool :=
  match par0 Mo j with
  | none => true
  | some q => decide ((Mo.getD q (0, 0, 0)).1 = 0) || copyHead Mo q

/-- `off` より前にアンカー `(1,1,0)` が 1 本でもあるか（`rows3.py` の `anch_before`）。 -/
def anchBefore (Mo : TrioSeq) (off : ℕ) : Bool :=
  (List.range off).any (fun j => Mo.getD j (0, 0, 0) == ((1, 1, 0) : Col))

/-- 写しの中まで届く `closesUnit`（`rows3.py` の `closes_top`）。
写しの中ではアンカーが `(k,1,0)` に化けるので `nxt.1 ≤ 1` が当たらない。
「次の柱が**いまの写しの根の直下**に戻る」と読み替える。 -/
def closesTop (Mo : TrioSeq) (off : ℕ) : Option Col → Bool
  | none => true
  | some c =>
      if c.2.2 ≠ 0 then false
      else if c.1 ≤ 1 then true
      else
        let j := off + 1
        if j < Mo.length ∧ Mo.getD j (0, 0, 0) = c then topLevel Mo j else false

/-- `hiBlock` の起点を「写しの頭の次の柱」まで進める（`rows3.py` の `hi_block2`）。
写しの頭が 1 つも無ければ `hiB` と完全に同じ。 -/
def hiB2 (m : TrioSeq) (x : ℕ) : ℕ :=
  (List.range x).foldl (fun b q => if b < q + 1 ∧ copyHead m q then q + 1 else b) (hiB m x)

/-- `hiBlock` の写し補正（`rows3.py` の `hi_block2`）。 -/
def hiBlock2 (m : TrioSeq) (x : ℕ) : Bool :=
  ((List.range x).drop (hiB2 m x + 1)).any
    (fun z => decide (0 < (m.getD z (0,0,0)).2.2))

/-- `prev = 0` でも分岐列を深く綴るか（`rows3.py` の `p0deep_ok`）。

    深い ⟺ nxt.1 ≥ p.1  または（自分より前にアンカーが 1 本も無く nxt.2.1 ≥ 1）

教師データ（シート 1354 行 ＋ ImgClosedT の目標）の `prev = 0` の枝 9399 本で
誤り 30 本、うち「深すぎ」＝いま正しい柱を壊す向きは **0 本**。 -/
def p0deepOk (Mo : TrioSeq) (off : ℕ) (p : Col) : Option Col → Bool
  | none => false
  | some c => decide (p.1 ≤ c.1) || (decide (1 ≤ c.2.1) && !anchBefore Mo off)

/-- `isRepeat` の本体（周期 `L = k+1` を下へ）。 -/
def isRepeatAux (m : TrioSeq) (x : ℕ) : ℕ → Bool
  | 0 => false
  | (k + 1) =>
      let l := k + 1
      ((m.drop (x + 1 - 2 * l)).take l == (m.drop (x + 1 - l)).take l)
        || isRepeatAux m x k

/-- `m[..x]` の末尾が、その直前の同じ長さの区間の逐語コピーか。 -/
def isRepeat (m : TrioSeq) (x : ℕ) : Bool := isRepeatAux m x ((x + 1) / 2)

/-- `(a,2,1)(a,2,0)(a,1,0)` の直後が `(1,1,1)` なら段を上げずに閉じる。
**v14 で使うのをやめた**（NOTES §課題 G3）。`conv3` からは呼ばれない。 -/
def closesHiUnit (c : Col) (nxt pv pv2 : Option Col) (hi rep : Bool) : Bool :=
  hi && !rep && nxt == some (1, 1, 1) && pv == some (c.1, 2, 0)
    && pv2 == some (c.1, 2, 1)

/-- `wchainHead` の本体（添字を `off` から 1 つずつ下げる。燃料 = その添字）。 -/
def wchainHeadAux (m : TrioSeq) (off : ℕ) : ℕ → Option ℕ
  | 0 => none
  | (j + 1) =>
      let c := m.getD j (0, 0, 0)
      if isWCol (some c) then
        -- v14 h1: 鎖の頭が「写しの頭」なら、根 `(0,*,*)` に当たったのと同じ
        -- （鎖はそこで切れる。写しの頭を「x w」の柱と読むのが誤りだった）。
        (if copyHead m j then none
         else if ((List.range (off + 1)).drop (j + 1)).all
              (fun t => decide (c.1 < (m.getD t (0, 0, 0)).1)) then some j else none)
      else if c.1 = 0 then none
      else wchainHeadAux m off j

/-- v13 `wchain`（`rows3.py` の `wchain_head`）。`off` から後ろへ「x w」の柱
`(k,0,0)` をさがす。ただし**その柱から `off` までの柱がぜんぶ行 0 > k**
（＝その柱の子孫）でなければならない。行 0 が 0 の柱（新しい加算項の頭）に
当たったら諦める。

直前 1 本だけを見る `after_w` を、写しの頭まで届くように広げたもの。 -/
def wchainHead (m : TrioSeq) (off : ℕ) : Option ℕ := wchainHeadAux m off off

/-- v13 `sib_anchbefore`（`rows3.py` の `sib_ok`）。兄弟から渡された深い側
`base_sd` を使ってよいのは、この柱より前にアンカー `(1,1,0)` が 1 本も無い
ときだけ。アンカーは行 1 の新しい加算ユニットの頭なので、「行 1 の最初の
ユニットの中でだけ、影の深さは兄弟に効く」という読み方になる。 -/
def sibOk (m : TrioSeq) (off : ℕ) : Bool :=
  !((List.range off).any (fun j => m.getD j (0, 0, 0) == ((1, 1, 0) : Col)))

/-! ### 縮約の道具（`rows3.py` の `units_split` / `copy_shift` / `contrPre`） -/

/-- v12 `mark`: 記録 `st.rec` を引く。無ければ `4`（Python の `'none'`）。 -/
def recAt (rc : List (ℕ × ℕ)) (i : ℕ) : ℕ :=
  match rc.find? (fun e => e.1 == i) with
  | some e => e.2
  | none => 4

/-- v12 `mark`（`rows3.py` の `leaves_mark_local`）。残余なしの縮約は
「写しを飲んだ印が像に残る」ときだけ許す。印が残らないと `M` と
`M ++ (1,1,0) ++ 写し` が同じ像に潰れる（＝単射性の破れ）。

縮約は「写しを書かない代わりに、本体の末尾の分岐列を番兵 `NOTLAST` で深く綴る」
ことだけで写しを記録する。ところが本体の末尾がもともと深く綴られていると、
深くしても像は 1 ビットも変わらず、写しが像から消える。印が残る条件は局所に書ける:

    印が残る <=> 決める直前の段 prev != 0 かつ `after_w` が発火しない

`ob` は本体 `[p] ++ A ++ U` の最後の柱のもとの添字、`code` はそこで記録された
「決める直前の段」（`recAt`）。`0` 浅い / `3` 選択肢が無い / `4` 記録なし の
どれかなら印は残らない。

v14 では `closes_hi_unit`（旗 `chu`）を落としたので、Python にあるその枝は
つねに偽であり、ここには現れない。 -/
def leavesMark (Mo : TrioSeq) (ob code : ℕ) : Bool :=
  if code = 0 ∨ code = 3 ∨ code = 4 then false
  else
    let pv : Option Col := if 1 ≤ ob then some (Mo.getD (ob - 1) (0, 0, 0)) else none
    let onx : Option Col :=
      if ob + 1 < Mo.length then some (Mo.getD (ob + 1) (0, 0, 0)) else none
    !(decide (code = 1) && isWCol pv && closesUnit onx)

/-- アンカー（新しい加算ユニットの頭）。 -/
def ANCHOR : Col := (1, 1, 0)

/-- 「後ろにユニットを閉じない列がある」を表す番兵。 -/
def NOTLAST : Col := (2, 2, 0)

/-- 行 0 が `a` より深い先頭部分の長さ。 -/
def deepLen (a : ℕ) : TrioSeq → ℕ
  | [] => 0
  | q :: r => if a < q.1 then deepLen a r + 1 else 0

/-- `units_split` の切れ目（燃料つき）。 -/
def unitsLenAux (p0 : ℕ) (qlab : ℕ × ℕ) (B : TrioSeq) : ℕ → ℕ → ℕ
  | k, 0 => k
  | k, (f + 1) =>
      if k < B.length then
        let c := B.getD k (0, 0, 0)
        if c.1 ≠ p0 then k
        else if (c.2.1, c.2.2) = qlab then k
        else unitsLenAux p0 qlab B (k + 1 + deepLen p0 (B.drop (k + 1))) f
      else k

/-- `B` の先頭から「深さ `p0` の柱＋その引数ブロック」を、段の対が `qlab` に
等しい柱に出会うまで取ったときの長さ。 -/
def unitsLen (p0 : ℕ) (qlab : ℕ × ℕ) (B : TrioSeq) : ℕ :=
  unitsLenAux p0 qlab B 0 B.length

/-- 写し（深さ +1、行 1 は条件つきで +e）。分岐列の浅い／深いは同じ状態機械で
1 本ずつ決め直す。 -/
def copyShift : TrioSeq → ℕ → ℕ → ℕ → Option Col → TrioSeq
  | [], _, _, _, _ => []
  | c :: rest, e, ps0, prev0, nxtAfter =>
      let nxt : Option Col := match rest with | q :: _ => some q | [] => nxtAfter
      let prev1 := if c = ANCHOR then 0 else prev0
      let sh := (prev1 == 0) || closesUnit nxt
      let dl :=
        if isBranch c then (if sh then 0 else (if ps0 < c.2.1 then e else 0))
        else (if ps0 < c.2.1 then e else 0)
      let prev2 := if isBranch c then (if sh then 0 else 1) else prev1
      (c.1 + 1, c.2.1 + dl, c.2.2) :: copyShift rest e ps0 prev2 nxtAfter

/-- 写しの先頭（`[p] ++ A ++ U` の写し）。 -/
def contrPre (p : Col) (U A : TrioSeq) (e ps0 prev0 : ℕ) (nxtAfter : Option Col) : TrioSeq :=
  copyShift (p :: (A ++ U)) e ps0 prev0 nxtAfter

/-- もとの深さ `k` が像で何段目になるか。 -/
def dmapAt (dm : List ℕ) (k : ℕ) : ℕ :=
  if dm = [] then k
  else if k < dm.length then dm.getD k 0
  else (dm.getLastD 0) + (k - dm.length + 1)

/-- 対の**辞書式**の `≥`（Python のタプル比較。Mathlib の `Prod` の順序は
成分ごとなので、そのままでは使えない）。 -/
def lexGe (a b : ℕ × ℕ) : Bool := decide (b.1 < a.1) || (decide (a.1 = b.1) && decide (b.2 ≤ a.2))

/-- 行 0 が `a` 以上で続く先頭部分の長さ。 -/
def deepGe (a : ℕ) : TrioSeq → ℕ
  | [] => 0
  | q :: r => if a ≤ q.1 then deepGe a r + 1 else 0

/-- 縮約の候補を 1 つの `e` について探す。見つかれば `(kU, kpre, na)`
（写しの長さ、写しの先頭の長さ、写しの「次の列」）。`rows3.py` の `lad0` の枝。 -/
def contrOne (p : Col) (A B : TrioSeq) (ps : ℕ × ℕ) (v s2 prev0 e : ℕ) :
    Option (ℕ × ℕ × Col) :=
  let qlab : ℕ × ℕ := (ps.1 + e, ps.2)
  let kU := unitsLen p.1 qlab B
  match B.drop kU with
  | [] => none
  | q :: r2 =>
      if (q.2.1, q.2.2) ≠ qlab ∨ q.1 ≠ p.1 then none
      else
        let U := B.take kU
        let Aq := r2.take (deepGe (q.1 + 1) r2)
        let blk := p :: (A ++ U)
        let tryNa : Col → Option (TrioSeq × Col) := fun na =>
          let pre := contrPre p U A e ps.1 prev0 (some na)
          if Aq.take pre.length = pre then some (pre, na) else none
        match (match tryNa q with | some x => some x | none => tryNa NOTLAST) with
        | none => none
        | some (pre, na) =>
            let lastB := blk.getLastD (0, 0, 0)
            let lastP := pre.getLastD (0, 0, 0)
            let deepEnd := isBranch lastB && decide (lastB.2.1 < lastP.2.1)
            let rest2 := Aq.drop pre.length
            match rest2 with
            | [] => if e ≠ 0 ∧ deepEnd = true then some (kU, pre.length, na) else none
            | c :: _ =>
                if c.1 < p.1 + 1 then none
                else if c.1 = p.1 + 1 ∧ lexGe (c.2.1, c.2.2) (v + e, s2) = true ∧ e = 0 then
                  none
                else some (kU, pre.length, na)

/-- `e = 0` を先に、だめなら `e = 1` を試す。返り値は `(e, kU, kpre, na)`。 -/
def contrFind (p : Col) (A B : TrioSeq) (ps : ℕ × ℕ) (v s2 prev0 : ℕ) :
    Option (ℕ × ℕ × ℕ × Col) :=
  match contrOne p A B ps v s2 prev0 0 with
  | some (kU, kp, na) => some (0, kU, kp, na)
  | none =>
      match contrOne p A B ps v s2 prev0 1 with
      | some (kU, kp, na) => some (1, kU, kp, na)
      | none => none

/-- 兄弟が無ければ縮約は起きない。 -/
@[simp] theorem contrOne_nil (p : Col) (A : TrioSeq) (ps : ℕ × ℕ) (v s2 prev0 e : ℕ) :
    contrOne p A [] ps v s2 prev0 e = none := by
  simp [contrOne]

@[simp] theorem contrFind_nil (p : Col) (A : TrioSeq) (ps : ℕ × ℕ) (v s2 prev0 : ℕ) :
    contrFind p A [] ps v s2 prev0 = none := by
  simp [contrFind]

mutual

/-- BMS 3 行 (z<2) -> DBMS 3 行。`rows3.py` の `conv3`（設計 v13）の写経。

Python の `conv3` は状態 `st` を**破壊的に**持ち回るので、Lean では
`TrioSeq × St` を返して線形に渡す。`cA` を先に走らせて、その状態で `cU`,
`cR`, `cB` を走らせる、という順序が Python の副作用の順序に対応する。

停止性の尺度は `2 * M.length`（`convResid` は `2 * rest.length + 1`）。
`convResid` は残余の先頭ブロックを丸ごと `conv3` に渡すので列数が減らない
ことがあり、それを「同じ列数なら `conv3` のほうが小さい」で受ける。 -/
def conv3 (M : TrioSeq) (d : ℕ) (L : List Lent) (F : List Bool)
    (ps pw : ℕ × ℕ) (first force : Bool) (st : St) (nx : Option Col) (off : ℕ) :
    TrioSeq × St :=
  match M with
  | [] => ([], st)
  | p :: r =>
    let v := p.2.1
    let s2 := p.2.2
    let A := r.takeWhile (fun q => decide (p.1 < q.1))
    let B := r.dropWhile (fun q => decide (p.1 < q.1))
    let ent := Lat L (v - 1)
    let base_d := if v = 0 then 0 else ent.1 + 1
    let base_s := if v = 0 then 0 else ent.2.2.2.1 + 1
    -- v13 sibL: 兄弟だけが使える深い側（第 5 項）。無いときは第 1 項＝`base_d`。
    let base_sd := if v = 0 then 0 else ent.2.2.2.2 + 1
    let pl2 := if v = 0 then 0 else ent.2.1
    let force1 := if v = 0 then false else ent.2.2.1
    let first1 := F.getD v true
    -- v12 `newterm`（課題 E2）: 行 0 が 0 の柱 `(0,*,*)` は**新しい加算項**の頭。
    -- ユニットが変わるのだから、直前の分岐列の選択は次の項に持ち越さない
    -- （持ち越すと `A ++ A` の 2 つ目の写しが浅く綴られ、`f` が和について
    -- 加法的でなくなる）。`2` が Python の `None` にあたる。
    -- v14 `wterm` ＋ `wterm_anchbefore`（課題 G3）: 根に直付けの「x w」の柱
    -- `(k,0,0)` も新しい加算項の頭。ただし前にアンカー `(1,1,0)` が 1 本でも
    -- あれば効かせない（`sib_anchbefore` と同じ伝染止め）。
    let prev0 : ℕ :=
      if p.1 = 0 then 2
      else if isWCol (some p) && (par0 st.Mo off == some 0) && !anchBefore st.Mo off then 2
      else st.prev
    let bp : ℕ × ℕ :=
      if isBranch p then
        -- v13 sibL: 深い側の候補は、兄弟から渡ってきた `base_sd` を使ってよければ
        -- それ。門は「浅い側 != 深い側の候補」で開く（`base_d` ではなく `deep`）。
        let deep := if (base_sd != base_d) && sibOk st.Mo off then base_sd else base_d
        if base_s != deep then
          let nxt : Option Col := match r with | q :: _ => some q | [] => nx
          let Mo := st.Mo
          let pv : Option Col := if 1 ≤ off then some (Mo.getD (off - 1) (0,0,0)) else none
          let onx : Option Col :=
            if off + 1 < Mo.length then some (Mo.getD (off + 1) (0,0,0)) else none
          -- v14 h1（課題 H1）: `hiBlock` の起点を写しの頭の次まで進める。
          let hi := hiBlock2 Mo off
          -- v14 h1: `closesUnit` を写しの中まで届く `closesTop` に読み替え、
          -- `prev = 0` の枝を「行列から直に読む述語」`p0deepOk` で決め直す。
          let sh0 :=
            if closesTop Mo off nxt then true
            else if (prev0 == 0) && !closesUnit nxt then !(p0deepOk Mo off p nxt)
            else (prev0 == 0) || closesUnit nxt
          let sh1 :=
            if (prev0 == 1) && isWCol pv && closesUnit onx then
              let pnt := decide (0 < off) && (par0 Mo (off - 1) == some 0)
              !(hi && !pnt)
            else if (prev0 == 1) && closesUnit onx then
              -- v13 wchain: `after_w` の窓を「この写しの頭まで」広げる。
              -- 判定式は `after_w` と同じで、親を見る柱だけ `(k,0,0)` 本人にする。
              -- `after_w` が発火するときはそちらが優先（この `else if`）。
              match wchainHead Mo off with
              | some j => !(hi && !(par0 Mo j == some 0))
              | none => sh0
            else sh0
          -- v14: `closesHiUnit` は落とした（`rows3.V14['chu'] = False`）。
          -- 浅い綴りと縮約の深い綴りが両立せず、双子の像が本体を追い越していた
          -- （NOTES §課題 G3）。シート行 1532 はその誤りのほう。
          let sh := sh1
          if sh then (base_s, 0) else (deep, 1)
        else (deep, prev0)
      else (base_d, prev0)
    let base := bp.1
    let lad1 := first1 && (s2 == pl2 + 1) && (decide (base ≤ s2) || force1)
    let e1 := if lad1 then base + 1 else (if 0 < s2 ∧ base ≤ s2 then s2 + 1 else base)
    let e2 := s2
    let h1 := if lad1 then base else e1
    let lad0 := first && (v == ps.1 + 1) && (decide (d ≤ h1) || force)
    let ST1 := if lad0 then st.ST.take d ++ [(pw.1, pw.2)] else st.ST
    let dd0 := if lad0 then d + 1 else (fit st.ST d h1).getD (max d st.ST.length)
    let ST2 := if lad1 then ST1.take dd0 ++ [(base, pl2)] else ST1
    let dd1 := if lad1 then dd0 + 1 else dd0
    let dd2 := if okPlace ST2 dd1 e1 then dd1 else (fit ST2 dd1 e1).getD dd1
    let cols : TrioSeq :=
      (if lad0 then [(d, pw.1, pw.2)] else []) ++
        (if lad1 then [(dd0, base, pl2)] else []) ++ [(dd2, e1, e2)]
    -- v12 `mark`: 分岐列の「決める直前の段」を記録する（像には効かない）。
    -- 門が開かなかった柱（`base_s == deep`）は `3`（Python の `'tie'`）。
    let recNew : List (ℕ × ℕ) :=
      if isBranch p then
        let deep := if (base_sd != base_d) && sibOk st.Mo off then base_sd else base_d
        if base_s != deep then (off, prev0) :: st.rc else (off, 3) :: st.rc
      else st.rc
    let st1 : St :=
      { ST := ST2.take dd2 ++ [(e1, e2)], prev := bp.2,
        dmap := st.dmap.take p.1 ++ [dd2], Mo := st.Mo, nc := st.nc, rc := recNew }
    let fc := (!lad1) && first1 && (s2 == pl2)
    let f0 := (!lad0) && first && (v == ps.1) && (s2 == ps.2)
    let Lb :=
      if (e1 == base + 1) && decide (1 ≤ v) then
        padL L (v - 1) ++ [(base, pl2, false, (Lat L (v - 1)).2.2.2.1, base)]
      else L
    -- v13 sibL: 第 5 項は**子には渡さない**（渡すとアンカーを素通りして
    -- 次の加算ユニットまで深い綴りが届く）。Python の `t[:4]` に対応。
    let LA := (padL Lb v).map lentTrunc ++ [(e1, s2, fc, e1, e1)]
    let FA := F.take v ++ [false]
    -- v12 `mark`（課題 E1）: `contrFind` が返した候補を、残余なしのときだけ
    -- 「写しを飲んだ印が像に残るか」で選り分ける。Python は `for e in (0,1)` の
    -- 中で `continue` するが、`mark` が見られるのは `rest2 == []` かつ `e == 1`
    -- のとき（＝ループの最後）だけなので、**後から候補を捨てる形と同値**である。
    -- だから `contrOne` を `conv3` と相互再帰にする必要はない。
    let cfm : Option (ℕ × ℕ × ℕ × Col) :=
      if lad0 then
        match contrFind p A B ps v s2 bp.2 with
        | none => none
        | some (e, kU, kp, na) =>
          let U := B.take kU
          let q := (B.drop kU).headD (0, 0, 0)
          let r2 := (B.drop kU).tail
          let Aq := r2.take (deepGe (q.1 + 1) r2)
          let rest2 := Aq.drop kp
          if rest2.isEmpty then
            let rA0 := conv3 A (dd2 + 1) LA FA (v, s2) (e1, e2) true false st1
                         (match U with | u :: _ => some u | [] => some na) (off + 1)
            let rU0 := conv3 U (d + 1) L FA (v, s2) (e1, e2) false false rA0.2 (some na)
                         (off + 1 + A.length)
            let ob := off + A.length + U.length
            if leavesMark st.Mo ob (recAt rU0.2.rc ob) then some (e, kU, kp, na) else none
          else some (e, kU, kp, na)
      else none
    match cfm with
    | some (e, kU, kp, na) =>
        let U := B.take kU
        let q := (B.drop kU).headD (0, 0, 0)
        let r2 := (B.drop kU).tail
        let Aq := r2.take (deepGe (q.1 + 1) r2)
        let Bq := r2.drop (deepGe (q.1 + 1) r2)
        let rest2 := Aq.drop kp
        let oU := off + 1 + A.length
        let oq := oU + U.length
        let Lr :=
          padL L v ++ [if e = 0 then (e1, s2, fc, e1, e1) else (base, pl2, fc, base, base)]
        let rA := conv3 A (dd2 + 1) LA FA (v, s2) (e1, e2) true false st1
                    (match U with | u :: _ => some u | [] => some na) (off + 1)
        let rU := conv3 U (d + 1) L FA (v, s2) (e1, e2) false false rA.2 (some na) oU
        let rd := if rest2 = [] ∨ (rest2.headD (0,0,0)).1 = p.1 + 1 then d + 1 + e
                  else dmapAt rU.2.dmap ((rest2.headD (0,0,0)).1 - 1)
        let rR := convResid rest2 rd Lr (v, s2) (e1, e2) rU.2
                    (match Bq with | b :: _ => some b | [] => nx) (oq + 1 + kp)
        let rB := conv3 Bq d L FA (v, s2) (e1, e2) false false rR.2 nx (oq + 1 + Aq.length)
        (cols ++ rA.1 ++ rU.1 ++ rR.1 ++ rB.1,
          { rB.2 with nc := rB.2.nc + 1 })
    | none =>
        -- v13 sibL: 行 1 の影を立てたら、そのあとの**兄弟**にも「深い側」を渡す
        -- （表の第 `v-1` 項の第 5 項に `base` を書く）。
        let LS :=
          if (e1 == base + 1) && decide (1 ≤ v) then
            let eo := Lat L (v - 1)
            padL L (v - 1) ++ [(eo.1, eo.2.1, eo.2.2.1, eo.2.2.2.1, base)] ++ L.drop v
          else L
        let rA := conv3 A (dd2 + 1) LA FA (v, s2) (e1, e2) true f0 st1
                    (match B with | q :: _ => some q | [] => nx) (off + 1)
        let rB := conv3 B d LS FA (v, s2) (e1, e2) false false rA.2 nx (off + 1 + A.length)
        (cols ++ rA.1 ++ rB.1, rB.2)
  termination_by 2 * M.length
  decreasing_by
    all_goals
      simp only [List.length_cons, List.length_take, List.length_drop, List.length_tail]
      have h1 : (r.takeWhile (fun q : ℕ × ℕ × ℕ => decide (p.1 < q.1))).length ≤ r.length :=
        (List.takeWhile_sublist _).length_le
      have h2 : (r.dropWhile (fun q : ℕ × ℕ × ℕ => decide (p.1 < q.1))).length ≤ r.length :=
        List.length_dropWhile_le _ r
      omega

/-- 縮約の残余を「もとの深さを保った森」として読む（`rows3.py` の `conv_resid`）。 -/
def convResid (rest : TrioSeq) (rd : ℕ) (Lr : List Lent) (ps pw : ℕ × ℕ)
    (st : St) (nx : Option Col) (off : ℕ) : TrioSeq × St :=
  match rest with
  | [] => ([], st)
  | c :: rs =>
      let i := 1 + deepGe c.1 rs
      let head := (c :: rs).take i
      let tail := (c :: rs).drop i
      let rh := conv3 head rd Lr (List.replicate 12 false) ps pw false false st
                  (match tail with | t :: _ => some t | [] => nx) off
      if tail.isEmpty then rh
      else
        let rt := convResid tail (rd - (c.1 - (tail.headD (0,0,0)).1)) Lr ps pw rh.2 nx (off + i)
        (rh.1 ++ rt.1, rt.2)
  termination_by 2 * rest.length + 1
  decreasing_by
    all_goals
      simp only [List.length_cons, List.length_take, List.length_drop]
      omega

end

/-- 変換の入口（Python の `b2d3`）。 -/
def b2d3 (M : TrioSeq) : TrioSeq :=
  (conv3 M 0 [] [] (0, 0) (0, 0) true false ⟨[], 2, [], M, 0, []⟩ none 0).1


/-! ### Python (`rows3.b2d3`) との突き合わせ。まず <=5 列から。 -/

#guard Conv3.b2d3 [(0,0,0)] = [(0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,0)] = [(0,0,0), (1,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,0), (2,1,0), (3,0,0), (1,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,1,0), (4,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (2,1,1), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,2,1), (4,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,2,1), (3,2,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,3,1), (5,3,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,0), (1,1,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,2,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,3,0), (5,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,0,0), (4,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,0,0), (6,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,1,1), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,2,1), (5,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (2,1,0), (1,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (0,0,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (0,0,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,1,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,1,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,2,0), (1,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,3,0), (3,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,1,1), (3,2,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,2,1), (5,3,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (0,0,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (0,0,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,0), (2,2,0), (1,1,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,0), (2,1,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (0,0,0), (1,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (0,0,0), (1,0,0), (2,1,0), (3,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,0), (2,1,0), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,1,0), (3,1,0), (3,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,0), (2,0,0), (1,0,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,0,0), (1,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,1,1), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,2,1), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (0,0,0), (1,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (0,0,0), (1,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,2,1), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,3,1), (4,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,1,1), (3,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,2,1), (5,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (0,0,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (0,0,0), (1,0,0)]


/-! **縮約が発火する** <=5 列の 5 個ぜんぶ、6 列の抜き取り、7 列の抜き取り。 -/

#guard Conv3.b2d3 [(0,0,0), (1,1,0), (1,0,0), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,0,0), (2,1,1), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,0), (2,2,1), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,0), (2,2,1), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,0), (2,2,1), (2,2,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,0), (2,2,1), (2,2,0), (3,3,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,0), (4,3,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,0), (2,2,1), (2,0,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,0,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,0), (2,2,1), (2,2,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,0), (4,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,0), (2,2,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,1,0), (3,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,0), (2,2,1), (2,2,0), (1,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,0), (1,0,0), (2,1,0), (2,0,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (2,0,0), (3,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,2,1), (2,1,1), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,3,1), (4,2,1), (5,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,2,0), (3,1,1), (4,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,3,0), (5,2,1), (6,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,0), (4,1,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (6,1,0), (5,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,1,1), (2,1,0), (3,2,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (3,2,1), (4,2,0), (5,3,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,1), (3,1,0), (1,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (6,2,1), (5,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,2,1), (2,0,0), (1,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,3,1), (4,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,1,1), (4,1,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,2,1), (6,2,0), (5,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,1,0), (2,2,1), (2,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,2,0), (4,3,1), (4,2,1)]

/-! 7 列の抜き取り。 -/

#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,0), (4,3,0), (2,1,1), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,0), (6,4,0), (4,2,1), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,0), (4,4,1), (5,5,0), (3,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,0), (6,5,1), (7,6,0), (5,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,0), (4,2,1), (5,3,0), (1,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,0), (6,3,1), (7,4,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,1), (4,3,1), (4,1,0), (5,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,1), (6,4,1), (6,2,0), (7,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,1,0), (2,2,0), (1,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,2,0), (4,3,0), (2,1,0), (3,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,0,0), (4,1,0), (2,1,1), (1,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,0,0), (6,1,0), (4,2,1), (3,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,1), (4,4,0), (3,2,1), (4,3,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,1), (6,5,0), (5,3,1), (6,4,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,1), (3,1,1), (4,0,0), (2,2,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,1), (5,2,1), (6,0,0), (4,3,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,0,0), (4,1,1), (4,1,0), (5,2,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,0,0), (6,1,0), (7,2,1), (7,2,0), (8,3,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,1,0), (3,0,0), (1,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,2,0), (5,0,0), (2,1,0), (3,0,0)]


/-! **v13 の 2 条項が効く** <=6 列の 12 個ぜんぶ（v12 の像と違うもの全部）。
`(0,0,0)(1,1,1)(2,1,0)(2,0,0)(3,1,1)(4,1,0)` が `wchain` の争点で、
末尾が `(6,2,1)(7,2,0)` になる（v12 は `(7,1,0)` で 1 段浅かった）。 -/

#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,1), (3,1,0), (1,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (6,2,1), (6,2,0), (3,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (6,2,1), (6,2,0), (4,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,1), (3,1,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (6,2,1), (6,2,0), (5,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,1), (3,1,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (6,2,1), (6,2,0), (6,2,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,1), (3,1,0), (4,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (6,2,1), (6,2,0), (7,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,1), (3,1,0), (4,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (6,2,1), (6,2,0), (7,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,1), (3,1,0), (4,2,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (6,2,1), (6,2,0), (7,3,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,1), (3,1,0), (4,2,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (6,2,1), (6,2,0), (7,3,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (2,0,0), (3,1,1), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,0,0), (5,1,0), (6,2,1), (6,2,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (2,0,0), (3,1,1), (4,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,0,0), (5,1,0), (6,2,1), (7,2,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,0,0), (4,1,1), (4,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,0,0), (6,1,0), (7,2,1), (7,2,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,0,0), (4,1,1), (5,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,0,0), (6,1,0), (7,2,1), (8,2,0)]

/-! 7 列で v13 が v12 と違う 290 個からの抜き取り。 -/

#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (3,2,0), (4,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,1), (3,1,0), (3,0,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (6,2,1), (6,2,0), (5,0,0), (4,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,1), (3,1,0), (4,1,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (6,2,1), (6,2,0), (7,1,0), (6,2,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,1), (3,1,1), (3,1,0), (1,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (6,2,1), (6,2,1), (6,2,0), (3,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (2,0,0), (3,1,1), (3,1,1), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,0,0), (5,1,0), (6,2,1), (6,2,1), (6,2,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,0,0), (4,1,1), (5,1,0), (5,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,0,0), (6,1,0), (7,2,1), (8,2,0), (8,2,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (2,0,0), (3,1,1), (3,1,0), (4,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,0,0), (5,1,0), (6,2,1), (6,2,0), (7,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,1,0), (4,0,0), (5,1,1), (5,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,2,0), (6,0,0), (7,1,0), (8,2,1), (8,2,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,0,0), (4,1,1), (4,1,0), (4,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,0,0), (6,1,0), (7,2,1), (7,2,0), (6,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,0,0), (3,1,1), (4,1,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,0,0), (5,1,0), (6,2,1), (7,2,0), (6,2,0)]

/-! **v14 h1 で像が変わる 7 列の 18 個ぜんぶ**（課題 H1 の 5 条項が効くところ）。

`copy_head` を軸にした 5 条項（`termTop` / `copyHead` / `topLevel` / `closesTop` /
`hiBlock2` / `wchainHead` / `p0deepOk`）は、写しの頭が 1 本も無い行列では元の
定義に戻るので **<=6 列では像が 1 つも変わらない**（8387 個で実測）。7 列で
初めて 18 個が変わる。どれも「写しの中の分岐列を 1 段深く綴る」向きである。 -/


#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]

/-! **v14 h1 で像が変わる 8 列の 352 個ぜんぶ**。

7 列の 18 個に「柱を 1 本足したもの」がほとんどだが、`#guard` は今回の変更点を
全部押さえるために全数入れてある（`lean/L1-NOTES.md` §6）。 -/


#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (3,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (3,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (3,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (3,1,0), (4,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (3,0,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (3,2,0), (4,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (1,1,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (3,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (3,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (3,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (3,1,0), (4,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (3,0,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,0), (4,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (1,0,0), (2,1,1), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (1,0,0), (2,1,1), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,0,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,0,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (6,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,0,0), (3,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (5,1,0), (6,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (3,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (3,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (3,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (3,1,0), (4,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (3,0,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (3,2,0), (4,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (3,0,0), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (3,0,0), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,1,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,1,1), (1,1,0), (2,0,0), (3,1,1), (4,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (3,2,1), (2,1,0), (3,0,0), (4,1,0), (5,2,1), (6,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (2,0,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (2,0,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (2,0,0), (1,1,0), (2,0,0), (3,1,1), (4,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,0,0), (2,1,0), (3,0,0), (4,1,0), (5,2,1), (6,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (2,1,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (2,1,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,0,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,0,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,0,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,0,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,0,0), (1,1,0), (2,0,0), (3,1,1), (4,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,0,0), (2,1,0), (3,0,0), (4,1,0), (5,2,1), (6,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,1,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,1,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,1,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,1,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,2,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,2,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,2,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,2,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,2,0), (1,1,0), (2,0,0), (3,1,1), (4,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,3,0), (2,1,0), (3,0,0), (4,1,0), (5,2,1), (6,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,2,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,3,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,2,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,3,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,2,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,2,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (3,2,1), (1,1,0), (2,0,0), (3,1,1), (4,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,3,1), (2,1,0), (3,0,0), (4,1,0), (5,2,1), (6,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (3,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (3,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (3,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (3,1,0), (4,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (3,0,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (3,2,0), (4,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,0,0), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,0,0), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0), (3,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0), (3,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0), (3,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0), (3,1,0), (4,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (3,2,0), (4,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (3,2,0), (4,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (3,2,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (3,2,0), (4,3,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (3,2,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (3,2,0), (4,3,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (3,0,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (4,0,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (4,0,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,0,0), (4,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (4,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (4,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,1,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (2,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,1,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (2,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,1,0), (2,0,0), (3,1,1), (4,1,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (2,1,0), (3,0,0), (4,1,0), (5,2,1), (6,1,0), (4,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,1,0), (2,0,0), (3,1,1), (4,1,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (2,1,0), (3,0,0), (4,1,0), (5,2,1), (6,1,0), (4,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,1,0), (2,0,0), (3,1,1), (4,1,0), (4,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (2,1,0), (3,0,0), (4,1,0), (5,2,1), (6,2,0), (6,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,1,0), (2,0,0), (3,1,1), (4,1,0), (5,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (2,1,0), (3,0,0), (4,1,0), (5,2,1), (6,2,0), (7,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,1,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (1,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (2,0,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (2,0,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (2,1,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (2,1,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,0,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,0,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,0,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,0,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,1,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,1,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,1,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,1,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,1,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,1), (3,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (3,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (3,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (3,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (3,1,0), (4,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (2,1,0), (3,0,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (3,2,0), (4,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,0,0), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,0,0), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0), (3,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0), (3,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0), (3,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0), (3,1,0), (4,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (3,2,0), (4,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (3,2,0), (4,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (3,2,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (3,2,0), (4,3,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (3,2,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (3,2,0), (4,3,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (3,0,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (4,0,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (4,0,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,0,0), (4,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (4,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (4,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,1), (4,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,0,0), (2,1,1), (3,1,1), (4,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,1,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (2,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,1,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (2,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,1,0), (2,0,0), (3,1,1), (4,1,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (2,1,0), (3,0,0), (4,1,0), (5,2,1), (6,1,0), (4,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,1,0), (2,0,0), (3,1,1), (4,1,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (2,1,0), (3,0,0), (4,1,0), (5,2,1), (6,1,0), (4,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,1,0), (2,0,0), (3,1,1), (4,1,0), (4,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (2,1,0), (3,0,0), (4,1,0), (5,2,1), (6,2,0), (6,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,1,0), (2,0,0), (3,1,1), (4,1,0), (5,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (2,1,0), (3,0,0), (4,1,0), (5,2,1), (6,2,0), (7,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,1,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (1,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (2,0,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (2,0,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (2,1,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (2,1,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (2,2,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (2,2,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,0,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,0,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,0,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,0,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,1,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,1,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,1,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,1,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,1,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,2,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,2,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,2,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,2,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,3,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,4,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,3,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,4,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,3,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,4,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,3,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,4,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,3,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,4,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,3,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,4,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,3,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,4,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,0), (3,3,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,4,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (3,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (3,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0), (3,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0), (3,1,0), (4,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (2,1,0), (3,0,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (3,2,0), (4,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,0,0), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,0,0), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,0,0), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0), (3,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0), (3,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0), (3,1,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0), (3,1,0), (4,2,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (0,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0), (0,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (1,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0), (1,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (3,2,0), (4,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (3,2,0), (4,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (3,2,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (3,2,0), (4,3,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0), (3,2,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (3,2,0), (4,3,1)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (3,0,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (4,0,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,0,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (4,0,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,0,0), (4,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (4,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (4,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,2,0), (5,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,1), (4,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,1,1), (4,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,2,1), (5,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,2,0), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,2,0), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,2,0), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,2,0), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,2,0), (4,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,0,0), (2,1,1), (3,2,0), (4,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,3,0), (5,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,1,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (2,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,1,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (2,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,1,0), (2,0,0), (3,1,1), (4,1,0), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (2,1,0), (3,0,0), (4,1,0), (5,2,1), (6,1,0), (4,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,1,0), (2,0,0), (3,1,1), (4,1,0), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (2,1,0), (3,0,0), (4,1,0), (5,2,1), (6,1,0), (4,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,1,0), (2,0,0), (3,1,1), (4,1,0), (4,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (2,1,0), (3,0,0), (4,1,0), (5,2,1), (6,2,0), (6,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,1,0), (2,0,0), (3,1,1), (4,1,0), (5,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (2,1,0), (3,0,0), (4,1,0), (5,2,1), (6,2,0), (7,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,1,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (1,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (3,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,0,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,0,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,0,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,1,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,1,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,2,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,2,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,2,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,2,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,2,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (2,2,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (4,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,0,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,0,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,0,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,0,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,0,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,1,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,1,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,1,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,1,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,1,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,1,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,1,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,1,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,2,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,1,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,1,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,2,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,2,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,2,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,3,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,2,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,2,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,3,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,2,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,3,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,2,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,3,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,2,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,2,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,3,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,0), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,0), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,0), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,0), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,0), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,1), (1,0,0), (2,1,1), (2,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,1), (1,0,0), (2,1,1), (2,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,1), (1,0,0), (2,1,0), (3,2,1), (2,1,0), (2,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,1), (1,0,0), (2,1,1), (3,1,0), (2,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,2,1), (3,3,1), (1,0,0), (2,1,1), (3,1,0), (2,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,1), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (2,1,0)]

/-! **v14 `wterm` が狙った 4 個**（課題 G3 が名指しした <=8 列の非標準 3 個と
その 7 列の接頭辞）。`wterm` の枝はここで発火するが、h1 が入った今の綴りでは
**旗を落としても像は変わらない**（<=8 列で 0 個）。それでも変更点なので置く。 -/


#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (3,2,1), (3,0,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (3,2,0), (4,3,1), (4,0,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (3,2,1), (3,1,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (3,2,0), (4,3,1), (4,1,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (3,2,1), (3,2,0)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (3,2,0), (4,3,1), (4,3,0)]
#guard Conv3.b2d3 [(0,0,0), (1,1,1), (2,1,0), (1,0,0), (2,1,1), (2,1,0), (3,2,1)] = [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,1,0), (1,0,0), (2,1,0), (3,2,1), (3,2,0), (4,3,1)]

end Conv3


/-! ## 9. 対角の像 `ConvDiagT3`

対角 `diagSeqT 0 v = (0,0,0)(1,1,1)(2,2,1)…(v,v,1)` は

* 兄弟がまったく無い（どの列も直前の列の引数）ので `B = []`、
* `is_branch` の分岐列 `(a,1,0)` が 1 本も無いので状態 `prev` を読まない、
* 兄弟が無いので縮約（`contrFind`）も発火しない（`contrFind_nil`）

一番素直な入力である。先頭 2 列 `(0,0,0)(1,1,1)` だけが特別（ここで行 0 と
行 1 の梯子が同時に立って 1 列が 3 列になる）で、3 列目から先は
「1 列が 1 列」の規則正しい尾になる。 -/

namespace Conv3

/-- 対角の尾: `(a,a,1)(a+1,a+1,1)…` を `m` 本。 -/
def Dt (a m : ℕ) : TrioSeq := (List.range' a m).map (fun i => (i, i, 1))

/-- その像: `(a,a-1,1)(a+1,a,1)…` を `m` 本。 -/
def Ot (a m : ℕ) : TrioSeq := (List.range' a m).map (fun i => (i, i - 1, 1))

@[simp] theorem Dt_zero (a : ℕ) : Dt a 0 = [] := rfl
@[simp] theorem Ot_zero (a : ℕ) : Ot a 0 = [] := rfl

theorem Dt_succ (a m : ℕ) : Dt a (m + 1) = (a, a, 1) :: Dt (a + 1) m := by
  simp [Dt, List.range'_succ]

theorem Ot_succ (a m : ℕ) : Ot a (m + 1) = (a, a - 1, 1) :: Ot (a + 1) m := by
  simp [Ot, List.range'_succ]

/-- 尾の第 `k+2` 列を読む直前の祖先の鎖。長さは `k+4`。 -/
def STd : ℕ → List (ℕ × ℕ)
  | 0 => [(0, 0), (0, 0), (1, 0), (2, 1)]
  | (k + 1) => STd k ++ [(k + 3, 1)]

/-- 尾の第 `k+2` 列を読む直前の段の表。長さは `k+2`。 -/
def Ld : ℕ → List Lent
  | 0 => [(1, 0, false, 0, 1), (2, 1, false, 2, 2)]
  | (k + 1) => Ld k ++ [(k + 3, 1, true, k + 3, k + 3)]

theorem STd_len (k : ℕ) : (STd k).length = k + 4 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [STd, ih]

theorem Ld_len (k : ℕ) : (Ld k).length = k + 2 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Ld, ih]

/-- 対角の表は最初から「潰した形」（第 5 項 = 第 1 項）なので、`LA` を作る
ときの `lentTrunc` は何もしない。 -/
theorem Ld_trunc (k : ℕ) : (Ld k).map lentTrunc = Ld k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Ld, ih, lentTrunc]

theorem STd_take (k : ℕ) : (STd k).take (k + 4) = STd k := by
  have h := STd_len k
  exact List.take_of_length_le (by omega)

theorem Ld_take (k : ℕ) : (Ld k).take (k + 2) = Ld k := by
  have h := Ld_len k
  exact List.take_of_length_le (by omega)

theorem STd_rev (k : ℕ) : ∃ R, (STd k).reverse = (k + 2, 1) :: R := by
  cases k with
  | zero => exact ⟨[(1, 0), (0, 0), (0, 0)], rfl⟩
  | succ k => exact ⟨(STd k).reverse, by simp [STd]⟩


theorem okPlace_STd (k : ℕ) : okPlace (STd k) (k + 4) (k + 3) = true := by
  obtain ⟨R, hR⟩ := STd_rev k
  unfold okPlace
  rw [if_neg (by omega), if_neg (by omega), STd_take, hR]
  simp

theorem fit_STd (k : ℕ) : fit (STd k) (k + 4) (k + 3) = some (k + 4) := by
  have hl : (STd k).length + 1 - (k + 4) = 1 := by rw [STd_len]; omega
  unfold fit
  rw [hl]
  simp only [fitAux]
  rw [if_pos (okPlace_STd k)]

/-- `Ld k` の最終項の Bool（`k = 0` だけ `false`）。実際には使われない
（`lad1` の第 2 条項 `s2 = pl2 + 1` が先に落ちるので `force1` は読まれない）。 -/
def bLd (k : ℕ) : Bool := decide (k ≠ 0)

theorem Lat_Ld (k : ℕ) : Lat (Ld k) (k + 1) = (k + 2, 1, bLd k, k + 2, k + 2) := by
  cases k with
  | zero => decide
  | succ k =>
      have hlen : (Ld k).length = k + 2 := Ld_len k
      have h : ((Ld k) ++ [((k + 3 : ℕ), (1 : ℕ), true, (k + 3 : ℕ), (k + 3 : ℕ))])[k + 2]?
          = some (k + 3, 1, true, k + 3, k + 3) := by
        have := List.getElem?_concat_length (l := Ld k)
          (a := ((k + 3 : ℕ), (1 : ℕ), true, (k + 3 : ℕ), (k + 3 : ℕ)))
        rwa [hlen] at this
      show Lat (Ld k ++ [((k + 3 : ℕ), (1 : ℕ), true, (k + 3 : ℕ), (k + 3 : ℕ))]) (k + 2) = _
      unfold Lat
      rw [h]
      simp [bLd]

theorem padL_Ld (k : ℕ) : padL (Ld k) (k + 2) = Ld k := by
  unfold padL
  rw [if_neg (by rw [Ld_len]; omega), Ld_take]

theorem getD_rep (n : ℕ) : (List.replicate n false).getD n true = true := by
  simp [List.getD]

theorem take_rep (n : ℕ) :
    (List.replicate n false).take n ++ [false] = List.replicate (n + 1) false := by
  rw [List.take_of_length_le (by simp)]
  simp [List.replicate_succ']

theorem rep_app (n : ℕ) :
    List.replicate n false ++ [false] = List.replicate (n + 1) false := by
  simp [List.replicate_succ']


theorem Dt_takeWhile : ∀ (m a b : ℕ), a < b →
    (Dt b m).takeWhile (fun q : ℕ × ℕ × ℕ => decide (a < q.1)) = Dt b m := by
  intro m
  induction m with
  | zero => intro a b _; rfl
  | succ m ih =>
      intro a b hab
      rw [Dt_succ, List.takeWhile_cons_of_pos (by simpa using hab), ih a (b + 1) (by omega)]

theorem Dt_dropWhile : ∀ (m a b : ℕ), a < b →
    (Dt b m).dropWhile (fun q : ℕ × ℕ × ℕ => decide (a < q.1)) = [] := by
  intro m
  induction m with
  | zero => intro a b _; rfl
  | succ m ih =>
      intro a b hab
      rw [Dt_succ, List.dropWhile_cons_of_pos (by simpa using hab), ih a (b + 1) (by omega)]


@[simp] theorem conv3_nil (d : ℕ) (L : List Lent) (F : List Bool) (ps pw : ℕ × ℕ)
    (first force : Bool) (st : St) (nx : Option Col) (off : ℕ) :
    conv3 [] d L F ps pw first force st nx off = ([], st) := by
  rw [conv3.eq_def]

theorem STd_succ (k : ℕ) : STd (k + 1) = STd k ++ [(k + 3, 1)] := rfl

theorem Ld_succ (k : ℕ) : Ld (k + 1) = Ld k ++ [(k + 3, 1, true, k + 3, k + 3)] := rfl

set_option maxHeartbeats 1000000 in
/-- 尾の 1 歩: 第 `k+2` 列 `(k+2,k+2,1)` は像の 1 列 `(k+4,k+3,1)` になり、
状態の祖先の鎖は `STd k -> STd (k+1)` に伸びる。行 0 の梯子 `lad0` は
`d = k+4 > h1 = k+3` で落ち、行 1 の梯子 `lad1` は `s2 = 1 != pl2+1 = 2` で落ちる。 -/
theorem conv3_tail_step (m k : ℕ) (st : St) (nx : Option Col) (off : ℕ)
    (h : st.ST = STd k) :
    conv3 (Dt (k + 2) (m + 1)) (k + 4) (Ld k) (List.replicate (k + 2) false)
      (k + 1, 1) (k + 2, 1) true false st nx off
    = ((k + 4, k + 3, 1) ::
        (conv3 (Dt (k + 3) m) (k + 5) (Ld (k + 1)) (List.replicate (k + 3) false)
          (k + 2, 1) (k + 3, 1) true false
          ⟨STd (k + 1), st.prev, st.dmap.take (k + 2) ++ [k + 4], st.Mo, st.nc, st.rc⟩
          nx (off + 1)).1,
       (conv3 (Dt (k + 3) m) (k + 5) (Ld (k + 1)) (List.replicate (k + 3) false)
          (k + 2, 1) (k + 3, 1) true false
          ⟨STd (k + 1), st.prev, st.dmap.take (k + 2) ++ [k + 4], st.Mo, st.nc, st.rc⟩
          nx (off + 1)).2) := by
  have hk1 : k + 2 - 1 = k + 1 := by omega
  have hk0 : ¬(k + 2 = 0) := by omega
  have h3 : k + 2 + 1 = k + 3 := by omega
  have h5 : k + 4 + 1 = k + 5 := by omega
  have hbeq : ((k + 1 : ℕ) == k) = false := by simp
  have hib : isBranch ((k : ℕ) + 2, (k : ℕ) + 2, (1 : ℕ)) = false := by simp [isBranch]
  rw [Dt_succ, conv3.eq_def]
  simp only [hk1, if_neg hk0, hib, Lat_Ld, Bool.false_eq_true, if_false,
    Dt_takeWhile m (k + 2) (k + 3) (by omega), Dt_dropWhile m (k + 2) (k + 3) (by omega),
    h]
  simp [padL_Ld, Ld_trunc, rep_app, STd_take, fit_STd, okPlace_STd, STd_len, STd_succ,
    Ld_succ, hbeq, h3, h5, isWCol]


/-- 尾ぜんぶ: `(k+2,k+2,1)…` を `m` 本読むと像は `(k+4,k+3,1)…` の `m` 本。 -/
theorem conv3_tail (m : ℕ) : ∀ (k : ℕ) (st : St) (nx : Option Col) (off : ℕ),
    st.ST = STd k →
    (conv3 (Dt (k + 2) m) (k + 4) (Ld k) (List.replicate (k + 2) false)
      (k + 1, 1) (k + 2, 1) true false st nx off).1 = Ot (k + 4) m := by
  induction m with
  | zero => intro k st nx off _; simp
  | succ m ih =>
      intro k st nx off h
      rw [conv3_tail_step m k st nx off h]
      have e1 : k + 1 + 4 = k + 5 := by omega
      have e2 : k + 1 + 2 = k + 3 := by omega
      have e3 : k + 1 + 1 = k + 2 := by omega
      have := ih (k + 1) ⟨STd (k + 1), st.prev, st.dmap.take (k + 2) ++ [k + 4], st.Mo, st.nc, st.rc⟩
        nx (off + 1) rfl
      simp only [e1, e2, e3] at this
      rw [this, Ot_succ]
      simp

/-- 先頭の列 `(0,0,0)`。梯子は 2 つとも落ち、像は `(0,0,0)` 1 列。
根は `p.1 = 0` なので v12 `newterm` が発火し、状態の `prev` は `2`（＝Python の
`None`）に落ちる。 -/
theorem conv3_lvl0 (v : ℕ) (st : St) (nx : Option Col) (off : ℕ) (h : st.ST = []) :
    (conv3 ((0, 0, 0) :: Dt 1 v) 0 [] [] (0, 0) (0, 0) true false st nx off).1
    = (0, 0, 0) :: (conv3 (Dt 1 v) 1 [(0, 0, true, 0, 0)] [false] (0, 0) (0, 0) true true
        ⟨[(0, 0)], 2, st.dmap.take 0 ++ [0], st.Mo, st.nc, st.rc⟩ nx (off + 1)).1 := by
  rw [conv3.eq_def]
  simp [Dt_takeWhile v 0 1 (by omega), Dt_dropWhile v 0 1 (by omega), h,
    okPlace, fit, fitAux, padL, isBranch]

/-- 2 列目 `(1,1,1)`。行 0 と行 1 の梯子が同時に立ち、1 列が 3 列になる。
ここで祖先の鎖が `STd 0 = (0,0)(0,0)(1,0)(2,1)`、段の表が `Ld 0` になる。 -/
theorem conv3_lvl1 (m : ℕ) (st : St) (nx : Option Col) (off : ℕ) (h : st.ST = [(0, 0)]) :
    (conv3 (Dt 1 (m + 1)) 1 [(0, 0, true, 0, 0)] [false] (0, 0) (0, 0) true true st nx off).1
    = (1, 0, 0) :: (2, 1, 0) :: (3, 2, 1) ::
      (conv3 (Dt 2 m) 4 (Ld 0) (List.replicate 2 false) (1, 1) (2, 1) true false
        ⟨STd 0, st.prev, st.dmap.take 1 ++ [3], st.Mo, st.nc, st.rc⟩ nx (off + 1)).1 := by
  rw [Dt_succ, conv3.eq_def]
  simp [Dt_takeWhile m 1 2 (by omega), Dt_dropWhile m 1 2 (by omega), h,
    okPlace, Lat, padL, STd, Ld, isBranch, isWCol, contrFind_nil, lentTrunc]


theorem conv3_tail0 (m : ℕ) (st : St) (nx : Option Col) (off : ℕ) (h : st.ST = STd 0) :
    (conv3 (Dt 2 m) 4 (Ld 0) (List.replicate 2 false) (1, 1) (2, 1) true false st nx off).1
      = Ot 4 m := by
  simpa using conv3_tail m 0 st nx off h

theorem mapDiag : ∀ (n a : ℕ), 1 ≤ a →
    (List.range' a n).map (fun j : ℕ => (j, j, min j 1)) = Dt a n := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
      intro a ha
      rw [List.range'_succ, List.map_cons, ih (a + 1) (by omega), Dt_succ]
      simp [Nat.min_eq_right ha]

theorem mapDD : ∀ (n a : ℕ), 3 ≤ a → (List.range' a n).map ddcolT = Ot a n := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
      intro a ha
      rw [List.range'_succ, List.map_cons, ih (a + 1) (by omega), Ot_succ]
      simp [ddcolT, Nat.min_eq_right (show 1 ≤ a - 2 by omega)]

theorem diagSeqT_cons (v : ℕ) : diagSeqT 0 v = (0, 0, 0) :: Dt 1 v := by
  simp [diagSeqT, List.range'_succ, mapDiag v 1 (le_refl 1)]

theorem ddiagSeqT_split (n : ℕ) :
    ddiagSeqT (n + 3) = (0, 0, 0) :: (1, 0, 0) :: (2, 1, 0) :: (3, 2, 1) :: Ot 4 n := by
  simp [ddiagSeqT, List.range_eq_range', List.range'_succ, ddcolT,
    mapDD n 4 (by omega)]

/-- **対角の像**（`ConvDiagT3` の本体）。 -/
theorem b2d3_diagSeqT (v : ℕ) :
    b2d3 (diagSeqT 0 v) = if v = 0 then ddiagSeqT 0 else ddiagSeqT (v + 2) := by
  unfold b2d3
  rw [diagSeqT_cons, conv3_lvl0 v _ none 0 rfl]
  cases v with
  | zero => simp [ddiagSeqT, ddcolT]
  | succ n =>
      rw [if_neg (by omega), conv3_lvl1 n _ none 1 rfl, conv3_tail0 n _ none 2 rfl,
        show n + 1 + 2 = n + 3 from by omega, ddiagSeqT_split n]

end Conv3

/-! ## 10. `ConvDiagT3` は Lean の `Conv3.b2d3` について証明ずみ -/

/-- **`ConvDiagT3` の証明**。`Dbms3.lean` が変換器に課していた 2 命題のうち、
対角の側はこれで閉じた。 -/
theorem ConvDiagT3_b2d3 : ConvDiagT3 Conv3.b2d3 := Conv3.b2d3_diagSeqT

/-- 残るのは `ReindexT1` ただ 1 つ、という形にまとめたもの。

`Conv3.b2d3` は Python の `rows3.b2d3`（縮約つき v13）の写経なので、
`ReindexT1 Conv3.b2d3` は Python 側で測っている性質そのものである。
いまの v13 はこれをまだ満たしていない（`tools/dbms/NOTES.md` の
「ImgClosedT の測定」: <=5 列で 4 個の反例が確定）。 -/
theorem ST_D3_b2d3 (h2 : Wset.TowerGraft2) (he : Wset.TowerExp)
    (H : ReindexT1 Conv3.b2d3) {M : TrioSeq} (hM : ST_TS M) : ST_D3 (Conv3.b2d3 M) :=
  ST_D3_conv3_holds h2 he H ConvDiagT3_b2d3 hM

/-! 対角の像を実際に計算して確かめる（`tools/dbms/rows3.py` の `b2d3` と一致）。 -/
#guard Conv3.b2d3 (diagSeqT 0 0) = ddiagSeqT 0
#guard Conv3.b2d3 (diagSeqT 0 1) = ddiagSeqT 3
#guard Conv3.b2d3 (diagSeqT 0 2) = ddiagSeqT 4
#guard Conv3.b2d3 (diagSeqT 0 5) = ddiagSeqT 7
#guard Conv3.b2d3 (diagSeqT 0 9) = ddiagSeqT 11


/-! ## 11. `ReindexT1` の分解（課題 F4）

`ReindexT1` は「像が展開で閉じている」＋「順序が保たれる」＋「挟み撃ち」の
3 つに割れる。**3 つとも `conv3` だけの構文的命題**（順序数も読み `read3` も
出てこない）ので、そのまま Python で全数採点できる。

    ImgClosedT3 : 任意の A, m>=1 に ある BMS 標準形 B で (conv3 A)<m> = conv3 B
    OrderT3     : translate M <o translate N  <->  seqlex (conv3 M) (conv3 N)
    SandwichT3  : conv3 (A<n>) <=seqlex (conv3 A)<n+1>   （上, C2@1）
                  (conv3 A)<n> <=seqlex conv3 (A<n+1>)   （下, C1@1）

`ReindexT1` が要求する `B` の位置 `A<n> ≤o B <o A` は、この挟み撃ちの
上下 2 本からちょうど出る（`ReindexT1_of_sandwich`）。

`SandwichL` が担っているのは「`conv3 B = (conv3 A)⟦n+1⟧` が `conv3 A` より
真に小さい」ことだけである。それは像が `blockok 0`（行 0 が 0 から始まり隣接
段差 1 以下）で 2 列以上なら **`seqlex_oper` で証明できる**ので、`SandwichL`
そのものを仮定しない版 `ReindexT1_of_block` が取れる。そちらで Python が
保証すべきものは

    ImgClosedT3 ＋ OrderT3 ＋ SandwichU ＋ 像の衛生（blockok と長さ）

だけになる。さらに `ImgClosedT3` は `ImgCofinalT3`（**いくらでも大きい `m`** で
逆像がある）まで弱められる（§11.3 の `ReindexT1_of_cofinal`）。**`SandwichL` 自体は像の衛生からは出ない**（`seqlex_oper` が言うのは
`(conv3 A)⟦n⟧ <seqlex conv3 A` であって、右辺が `conv3 (A⟦n+1⟧)` の版ではない）。
`conv3` v12 は `SandwichL` を <=6 列 41930 対のうち 352 対（<=7 列 386405 対の
うち 4696 対）で破っているので、実用上も `ReindexT1_of_block` の側を採るべきで
ある。`SandwichU` のほうは <=6 列で破れ 0（<=7 列で 8）。 -/

/-- 列辞書式の「以下」。 -/
def sle3 (M N : TrioSeq) : Prop := M = N ∨ seqlex M N

theorem seqlex_irrefl (M : TrioSeq) : ¬ seqlex M M := by
  induction M with
  | nil => simp
  | cons p M ih =>
    rw [seqlex_cons_cons]
    rintro (h | ⟨-, h⟩)
    · exact absurd h (by simp [collt])
    · exact ih h

theorem ne_of_seqlex {M N : TrioSeq} (h : seqlex M N) : M ≠ N := by
  rintro rfl
  exact seqlex_irrefl _ h

/-- **DBMS 側の展開は列辞書式を下げる。** 標準形性はいらない（`blockok` だけ）。
`m_step_decreases`（`Decrease.lean:578`）と `olt_iff_seqlex`（`Seqlex.lean:408`）の
組み合わせ。これが `SandwichL` の中身である。 -/
theorem seqlex_oper {C : TrioSeq} {m : ℕ} (hb : blockok 0 C) (hL : 1 < C.length)
    (hm : 1 ≤ m) : seqlex (C⟦m⟧) C := by
  have h1 : translate (C⟦m⟧) <o translate C := m_step_decreases hL hm
  have hne : C⟦m⟧ ≠ C := by
    intro h
    rw [h] at h1
    exact olt_irrefl _ h1
  exact (olt_iff_seqlex (blockok_oper hb hm) hb hne).1 h1

/-! ### 11.1 3 つの命題 -/

/-- **像は展開で閉じている**。`tools/dbms/imgfast.py` が測っている命題そのもの。
いまの `conv3` v12 では <=5 列で 26 個・<=6 列で 294 個の A が反例
（`python3 imgfast.py fast 5 / fast 6`）。

下の分解が実際に使うのは `m = n + 1`、つまり **`m ≥ 2` だけ**である。ただし実測
（<=5 列 x m<=3 の 3051 対）では破れは m=2 が 25 対・m=3 が 26 対で **m=1 の破れは
0 件**なので、`1 ≤ m` を `2 ≤ m` に弱めても反例は 1 件も減らない。 -/
def ImgClosedT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {A : TrioSeq}, ST_TS A → 1 < A.length → ∀ m : ℕ, 1 ≤ m →
    ∃ B : TrioSeq, ST_TS B ∧ (conv3 A)⟦m⟧ = conv3 B

/-- **順序保存**。2 行の `conC_olt_iff_seqlex`（`Dbms.lean:2791`）の 3 行版だが、
右辺が **DBMS 側の** 列辞書式であるところが違う（2 行版は BMS 側の `seqlex M N`
で止めてある）。標準形の上では `translate` が `seqlex` への順序同型
（`olt_ST_iff_seqlex`）なので、これは「`conv3` が列辞書式の順序埋め込み」と同値:

    seqlex M N  <->  seqlex (conv3 M) (conv3 N)

この形なら順序数を一切通さずに Python で採点できる（`OrderT3_iff_seqemb`）。
**実測: `conv3` v12 は <=6 列 8387 個・<=7 列 77282 個で、辞書式に並べ替えても
像の辞書式で並べ替えても順序が完全に同一（位置ずれ 0、像の重複も 0）。** -/
def OrderT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {M N : TrioSeq}, ST_TS M → ST_TS N →
    (translate M <o translate N ↔ seqlex (conv3 M) (conv3 N))

/-- **挟み撃ちの上**（`m_cofinal.py` の C2@1）。シートの正解 f では 38880 対で
反例 0。`conv3` v12 の実測は <=6 列 41930 対で破れ 0 / <=7 列 386405 対で破れ 8
（n = 1..5）。その 8 対は **A が 2 個だけ**（n = 2..5 の 4 本ずつ）:

    (0,0,0)(1,1,1)(2,1,0)(3,2,1)(3,2,0)(3,1,0)(1,1,1)
    (0,0,0)(1,1,1)(2,2,1)(3,2,1)(3,2,0)(3,1,0)(1,1,1)

これは `tools/dbms/rows3.py` の残る欠陥 (c)「残余ありの縮約」の 2 個と同じ行列で、
食い違いは第 8 列の行 1 が 2 か 1 か（`f(A⟦n⟧)` が `(5,2,0)`、`(f A)⟦n+1⟧` が
`(5,1,0)`）。ImgClosedT の破れと同じ「末尾の行 1 が 1 だけずれる」病である。 -/
def SandwichUT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {A : TrioSeq}, ST_TS A → 1 < A.length → ∀ n : ℕ, 1 ≤ n →
    sle3 (conv3 (A⟦n⟧)) ((conv3 A)⟦n + 1⟧)

/-- **挟み撃ちの下**（`m_cofinal.py` の C1@1）。シートの正解 f では 38880 対で
反例 0 だが、`conv3` v12 の実測は <=6 列 41930 対で破れ 352 / <=7 列 386405 対で
破れ 4696（n = 1..5）。**下の `ReindexT1_of_block` はこれを使わない。** -/
def SandwichLT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {A : TrioSeq}, ST_TS A → 1 < A.length → ∀ n : ℕ, 1 ≤ n →
    sle3 ((conv3 A)⟦n⟧) (conv3 (A⟦n + 1⟧))

/-- 挟み撃ち（上下）。 -/
def SandwichT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  SandwichUT3 conv3 ∧ SandwichLT3 conv3

/-- 像が `blockok 0`（行 0 が 0 から始まり、隣接する段差が 1 以下）。
実測: `conv3` v12 は <=7 列 77282 個で破れ 0。 -/
def ImgBlockT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {A : TrioSeq}, ST_TS A → blockok 0 (conv3 A)

/-- 像の長さ（`|A| > 1` なら像も 2 列以上）。
実測: `conv3` v12 は <=7 列 77282 個で破れ 0。 -/
def ImgLenT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {A : TrioSeq}, ST_TS A → 1 < A.length → 1 < (conv3 A).length

/-! ### 11.2 `OrderT3` から出る道具 -/

/-- `conv3` の像で `≤` なら、もとの項も `≤o`。`conv3 M = conv3 N` の枝は
`OrderT3` から出る単射性で潰す。 -/
theorem ole_of_sle3 {conv3 : TrioSeq → TrioSeq} (hO : OrderT3 conv3)
    {M N : TrioSeq} (hM : ST_TS M) (hN : ST_TS N)
    (h : sle3 (conv3 M) (conv3 N)) : translate M ≤o translate N := by
  rcases h with heq | hlt
  · rcases seqlex_total M N with rfl | hs | hs
    · exact ole_refl _
    · exact Or.inl ((olt_ST_iff_seqlex hM hN (ne_of_seqlex hs)).2 hs)
    · have h1 : translate N <o translate M :=
        (olt_ST_iff_seqlex hN hM (ne_of_seqlex hs)).2 hs
      have h2 : seqlex (conv3 N) (conv3 M) := (hO hN hM).1 h1
      rw [heq] at h2
      exact absurd h2 (seqlex_irrefl _)
  · exact Or.inl ((hO hM hN).2 hlt)

/-- `OrderT3` は単射性を含む。 -/
theorem conv3_injective {conv3 : TrioSeq → TrioSeq} (hO : OrderT3 conv3)
    {M N : TrioSeq} (hM : ST_TS M) (hN : ST_TS N) (h : conv3 M = conv3 N) : M = N := by
  rcases seqlex_total M N with rfl | hs | hs
  · rfl
  · have h2 : seqlex (conv3 M) (conv3 N) :=
      (hO hM hN).1 ((olt_ST_iff_seqlex hM hN (ne_of_seqlex hs)).2 hs)
    rw [h] at h2
    exact absurd h2 (seqlex_irrefl _)
  · have h2 : seqlex (conv3 N) (conv3 M) :=
      (hO hN hM).1 ((olt_ST_iff_seqlex hN hM (ne_of_seqlex hs)).2 hs)
    rw [h] at h2
    exact absurd h2 (seqlex_irrefl _)

/-! ### 11.3 主定理: `ReindexT1` の分解 -/

/-- **像は展開で共終に閉じている**（`ImgClosedT3` の弱め）。

`ReindexT1_of_block` が `ImgClosedT3` から実際に使うのは **`m := n + 1` ただ 1 つ**
である。だから「すべての `m`」は要らず「**いくらでも大きい `m`**」で足りる。
差を埋めるのは展開指数についての単調性 `oper_mono_idx`（`Cofidx.lean`）で、
これは `oper` の定義が `M.take j0 ++ (List.range n).flatMap g` の形をしていること、
つまり `M⟦n+1⟧` が `M⟦n⟧` の**接尾に足しただけ**であることから出る。 -/
def ImgCofinalT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {A : TrioSeq}, ST_TS A → 1 < A.length → ∀ m0 : ℕ,
    ∃ m : ℕ, m0 ≤ m ∧ ∃ B : TrioSeq, ST_TS B ∧ (conv3 A)⟦m⟧ = conv3 B

/-- 強い方から弱い方は出る。 -/
theorem ImgCofinalT3_of_ImgClosedT3 {conv3 : TrioSeq → TrioSeq}
    (h : ImgClosedT3 conv3) : ImgCofinalT3 conv3 := by
  intro A hA hlen m0
  obtain ⟨B, hB, heq⟩ := h hA hlen (max m0 1) (le_max_right _ _)
  exact ⟨max m0 1, le_max_left _ _, B, hB, heq⟩

/-! ### ★ 課題 L28: `ReindexT1` に**全域の順序保存は要らない**

`ReindexT1_of_cofinal` の証明の中で `OrderT3` が使われるのは**3 か所だけ**で、
しかも相手は任意の `M, N` ではなく **`ImgCofinalT3` が返した `B`** に限られる:

    (1) `ole_of_sle3` の `=` の枝 … `conv3 (A⟦n⟧) = conv3 B → A⟦n⟧ = B`（**単射性だけ**）
    (2) `ole_of_sle3` の `<` の枝 … `seqlex (conv3 (A⟦n⟧)) (conv3 B) → …`（**(←) だけ**）
    (3) 最後の行            … `seqlex (conv3 B) (conv3 A) → …`（**(←) だけ**）

**(→)（順序を保つ向き）は 1 か所も使っていない。** `conv3_injective` が (→) を
使っているのは `ole_of_sle3` の `=` の枝を潰すためだけで、そこは単射性を
直に仮定すれば済む（`ole_of_sle3'`）。

⟹ 下の `OrderReindexT3` は `OrderT3` より**真に弱い**:
`B` は `(conv3 A)⟦m⟧ = conv3 B` を満たすものに限られ、向きも (←) だけである。
**課題 L24 の反例 24 対がこの形でないなら、Lean 側は通る。**（要測定） -/

/-- **単射性**（`ReindexT1` が要求する 3 本のうち、順序でない 1 本）。

`ole_of_sle3` の `=` の枝を潰すためだけに要る。`OrderT3` からは出るが、
**順序とは独立に測れる**ので分けておく。 -/
def Inj3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {M N : TrioSeq}, ST_TS M → ST_TS N → conv3 M = conv3 N → M = N

theorem inj3_of_orderT3 {conv3 : TrioSeq → TrioSeq} (hO : OrderT3 conv3) :
    Inj3 conv3 := fun hM hN h => conv3_injective hO hM hN h

/-- **(←) の向きだけの全域版**（`OrderT3` の半分）。

⚠ **`OrderT3` より弱くはない。** `seqlex` も `<o` も `ST_TS` 上では相異なる 2 つを
必ず比べる（`seqlex_total` / `olt_ST_iff_seqlex`）ので、**(→) と (←) は
全域では同値**である（下の `orderT3_of_orderBackT3`）。
⟹ **向きを制限しても何も買えない。買えるのは「相手を制限する」ほう**である
（`OrderReindexT3`）。 -/
def OrderBackT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {M N : TrioSeq}, ST_TS M → ST_TS N →
    seqlex (conv3 M) (conv3 N) → translate M <o translate N

/-- **(←) だけから (→) が出る**（`ST_TS` 上の三分律を使う）。
⟹ `OrderBackT3` と `OrderT3` は同値。**向きの制限は無意味**である。 -/
theorem orderT3_of_orderBackT3 {conv3 : TrioSeq → TrioSeq}
    (hj : Inj3 conv3) (hb : OrderBackT3 conv3) : OrderT3 conv3 := by
  intro M N hM hN
  refine ⟨fun h => ?_, fun h => hb hM hN h⟩
  rcases seqlex_total (conv3 M) (conv3 N) with heq | hs | hs
  · exact absurd (hj hM hN heq ▸ h) (olt_irrefl _)
  · exact hs
  · exact absurd (hb hN hM hs) (fun h2 => olt_asymm h h2)

/-- **`ReindexT1` が実際に要求する順序の性質だけ**を取り出したもの。

⚠ **`(→)`（順序を保つ向き）は入っていない。** 入っているのは
**`(←)`（像の辞書式から順序数へ戻す向き）だけ**で、しかも相手は
`(conv3 A)⟦m⟧ = conv3 B` を満たす `B` に限られる。 -/
def OrderReindexT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {A B : TrioSeq}, ST_TS A → ST_TS B → ∀ {n m : ℕ}, 1 ≤ n → n + 1 ≤ m →
    (conv3 A)⟦m⟧ = conv3 B →
      (seqlex (conv3 (A⟦n⟧)) (conv3 B) → translate (A⟦n⟧) <o translate B) ∧
      (seqlex (conv3 B) (conv3 A) → translate B <o translate A)

/-- `OrderT3` は `OrderReindexT3` を含む（弱化であることの確認）。 -/
theorem orderReindexT3_of_orderT3 {conv3 : TrioSeq → TrioSeq} (hO : OrderT3 conv3) :
    OrderReindexT3 conv3 := by
  intro A B hA hB n m hn hm heq
  exact ⟨fun h => (hO (ST_TS.oper hA hn) hB).2 h, fun h => (hO hB hA).2 h⟩

/-- `sle3` から `≤o`（単射性と (←) を直に受け取る版）。 -/
theorem ole_of_sle3' {conv3 : TrioSeq → TrioSeq} {M N : TrioSeq}
    (hinj : conv3 M = conv3 N → M = N)
    (hrefl : seqlex (conv3 M) (conv3 N) → translate M <o translate N)
    (h : sle3 (conv3 M) (conv3 N)) : translate M ≤o translate N := by
  rcases h with heq | hlt
  · rw [hinj heq]; exact ole_refl _
  · exact Or.inl (hrefl hlt)

/-- **`ReindexT1` が実際に要求する挟み撃ちの上だけ**（課題 L31）。

`ReindexT1_of_cofinal'` の中で `SandwichUT3` が使われるのは **1 か所**で、
しかも相手は `(conv3 A)⟦m⟧ = conv3 B` を満たす `B` に限られる。
`SandwichUT3` は `ST_TS v<=4 len<=8` の判定 59157 回で **破れ 12**（課題 R10）だが、
**この弱い版が真なら Lean 側は通る**。 -/
def SandwichUReindexT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {A B : TrioSeq}, ST_TS A → 1 < A.length → ST_TS B → ∀ {n m : ℕ},
    1 ≤ n → n + 1 ≤ m → (conv3 A)⟦m⟧ = conv3 B →
      sle3 (conv3 (A⟦n⟧)) (conv3 B)

/-- `SandwichUT3` は `SandwichUReindexT3` を含む（弱化であることの確認）。 -/
theorem sandwichUReindexT3_of_sandwichUT3 {conv3 : TrioSeq → TrioSeq}
    (hU : SandwichUT3 conv3) : SandwichUReindexT3 conv3 := by
  intro A B hA hlen hB n m hn hm heq
  have h1 := hU hA hlen n hn
  have h2 : sle3 ((conv3 A)⟦n + 1⟧) ((conv3 A)⟦m⟧) := oper_mono_idx hm
  rw [← heq]
  rcases h1 with e1 | s1
  · rcases h2 with e2 | s2
    · exact Or.inl (e1.trans e2)
    · exact Or.inr (e1 ▸ s2)
  · rcases h2 with e2 | s2
    · exact Or.inr (e2 ▸ s1)
    · exact Or.inr (seqlex_trans s1 s2)

/-- **★★ `ReindexT1` は弱い 3 本（`Inj3` / `OrderReindexT3` / `SandwichUReindexT3`）
で出る。** `OrderT3` も `SandwichUT3` も使わない。 -/
theorem ReindexT1_of_cofinal'' {conv3 : TrioSeq → TrioSeq}
    (hI : ImgCofinalT3 conv3) (hj : Inj3 conv3) (hO : OrderReindexT3 conv3)
    (hU : SandwichUReindexT3 conv3) (hb : ImgBlockT3 conv3)
    (hlen2 : ImgLenT3 conv3) : ReindexT1 conv3 := by
  intro A hA hlen n hn
  obtain ⟨m, hm0, B, hB, heq⟩ := hI hA hlen (n + 1)
  obtain ⟨hr1, hr2⟩ := hO hA hB hn hm0 heq
  refine ⟨m, B, by omega, hB, ?_, ?_, heq⟩
  · exact ole_of_sle3' (fun h => hj (ST_TS.oper hA hn) hB h) hr1
      (hU hA hlen hB hn hm0 heq)
  · refine hr2 ?_
    rw [← heq]
    exact seqlex_oper (hb hA) (hlen2 hA hlen) (by omega)

/-- **★ `ReindexT1` は `OrderT3` の代わりに `OrderReindexT3` で出る。** -/
theorem ReindexT1_of_cofinal' {conv3 : TrioSeq → TrioSeq}
    (hI : ImgCofinalT3 conv3) (hj : Inj3 conv3) (hO : OrderReindexT3 conv3)
    (hU : SandwichUT3 conv3) (hb : ImgBlockT3 conv3) (hlen2 : ImgLenT3 conv3) :
    ReindexT1 conv3 := by
  intro A hA hlen n hn
  obtain ⟨m, hm0, B, hB, heq⟩ := hI hA hlen (n + 1)
  obtain ⟨hr1, hr2⟩ := hO hA hB hn hm0 heq
  have hinj : conv3 (A⟦n⟧) = conv3 B → A⟦n⟧ = B :=
    fun h => hj (ST_TS.oper hA hn) hB h
  refine ⟨m, B, by omega, hB, ?_, ?_, heq⟩
  · have h1 := hU hA hlen n hn
    have h2 : sle3 ((conv3 A)⟦n + 1⟧) ((conv3 A)⟦m⟧) := oper_mono_idx hm0
    have h3 : sle3 (conv3 (A⟦n⟧)) (conv3 B) := by
      rw [← heq]
      rcases h1 with e1 | s1
      · rcases h2 with e2 | s2
        · exact Or.inl (e1.trans e2)
        · exact Or.inr (e1 ▸ s2)
      · rcases h2 with e2 | s2
        · exact Or.inr (e2 ▸ s1)
        · exact Or.inr (seqlex_trans s1 s2)
    exact ole_of_sle3' hinj hr1 h3
  · refine hr2 ?_
    rw [← heq]
    exact seqlex_oper (hb hA) (hlen2 hA hlen) (by omega)

/-- **`ReindexT1` は `ImgCofinalT3` から出る**（`ImgClosedT3` は要らない）。

`ImgClosedT3` 版（下の `ReindexT1_of_block`）との差は 1 行、
`conv3 (A⟦n⟧) ≤ (conv3 A)⟦n+1⟧ ≤ (conv3 A)⟦m⟧` の真ん中の `≤` である。 -/
theorem ReindexT1_of_cofinal {conv3 : TrioSeq → TrioSeq}
    (hI : ImgCofinalT3 conv3) (hO : OrderT3 conv3) (hU : SandwichUT3 conv3)
    (hb : ImgBlockT3 conv3) (hlen2 : ImgLenT3 conv3) :
    ReindexT1 conv3 := by
  intro A hA hlen n hn
  obtain ⟨m, hm0, B, hB, heq⟩ := hI hA hlen (n + 1)
  refine ⟨m, B, by omega, hB, ?_, ?_, heq⟩
  · have h1 := hU hA hlen n hn
    have h2 : sle3 ((conv3 A)⟦n + 1⟧) ((conv3 A)⟦m⟧) := oper_mono_idx hm0
    have h3 : sle3 (conv3 (A⟦n⟧)) (conv3 B) := by
      rw [← heq]
      rcases h1 with e1 | s1
      · rcases h2 with e2 | s2
        · exact Or.inl (e1.trans e2)
        · exact Or.inr (e1 ▸ s2)
      · rcases h2 with e2 | s2
        · exact Or.inr (e2 ▸ s1)
        · exact Or.inr (seqlex_trans s1 s2)
    exact ole_of_sle3 hO (ST_TS.oper hA hn) hB h3
  · refine (hO hB hA).2 ?_
    rw [← heq]
    exact seqlex_oper (hb hA) (hlen2 hA hlen) (by omega)


/-- **`ReindexT1` は `ImgClosedT3` ＋ `OrderT3` ＋ `SandwichT3` から出る。**

`m := n + 1` を取り、`ImgClosedT3` が返す `B`（`(conv3 A)⟦n+1⟧ = conv3 B`）を使う。

* 上: `SandwichU` の `n` 版が `conv3 (A⟦n⟧) ≤ conv3 B` を与え、`OrderT3` で
  `translate (A⟦n⟧) ≤o translate B` になる。
* 下: `SandwichL` の `n+1` 版が `conv3 B ≤ conv3 (A⟦n+2⟧)` を与え、`OrderT3` で
  `translate B ≤o translate (A⟦n+2⟧)`。あとは `m_step_decreases` で
  `translate (A⟦n+2⟧) <o translate A`。

これが「Sandwich から `B` の位置 `A⟦n⟧ ≤o B <o A` が出る」の中身である。 -/
theorem ReindexT1_of_sandwich {conv3 : TrioSeq → TrioSeq}
    (hI : ImgClosedT3 conv3) (hO : OrderT3 conv3) (hS : SandwichT3 conv3) :
    ReindexT1 conv3 := by
  obtain ⟨hU, hL⟩ := hS
  intro A hA hlen n hn
  obtain ⟨B, hB, heq⟩ := hI hA hlen (n + 1) (by omega)
  refine ⟨n + 1, B, by omega, hB, ?_, ?_, heq⟩
  · have h := hU hA hlen n hn
    rw [heq] at h
    exact ole_of_sle3 hO (ST_TS.oper hA hn) hB h
  · have h := hL hA hlen (n + 1) (by omega)
    rw [heq] at h
    have h1 : translate B ≤o translate (A⟦n + 1 + 1⟧) :=
      ole_of_sle3 hO hB (ST_TS.oper hA (by omega : 1 ≤ n + 1 + 1)) h
    exact ole_olt_trans h1 (m_step_decreases hlen (by omega : 1 ≤ n + 1 + 1))

/-- **下側の挟み撃ちは像の衛生から証明できる**（`SandwichL` を仮定しない版）。

`SandwichL` の役目は「`conv3 B = (conv3 A)⟦n+1⟧` が `conv3 A` より真に小さい」
ことを言うだけなので、像が `blockok 0` で 2 列以上なら `seqlex_oper` で出る。
Python が保証すべきものは

    ImgClosedT3 ＋ OrderT3 ＋ SandwichU ＋ ImgBlockT3 ＋ ImgLenT3

だけになる。うしろ 2 つは変換器の出力の形の話（行 0 が 0 から始まって 1 段ずつ）で
中身が無い。 -/
theorem ReindexT1_of_block {conv3 : TrioSeq → TrioSeq}
    (hI : ImgClosedT3 conv3) (hO : OrderT3 conv3) (hU : SandwichUT3 conv3)
    (hb : ImgBlockT3 conv3) (hlen2 : ImgLenT3 conv3) :
    ReindexT1 conv3 := by
  intro A hA hlen n hn
  obtain ⟨B, hB, heq⟩ := hI hA hlen (n + 1) (by omega)
  refine ⟨n + 1, B, by omega, hB, ?_, ?_, heq⟩
  · have h := hU hA hlen n hn
    rw [heq] at h
    exact ole_of_sle3 hO (ST_TS.oper hA hn) hB h
  · refine (hO hB hA).2 ?_
    rw [← heq]
    exact seqlex_oper (hb hA) (hlen2 hA hlen) (by omega)

/-- `ST_D3_conv3` を分解した形でまとめ直したもの。

**Python が保証すべきものは `ImgCofinalT3`（いくらでも大きい `m`）であって
`ImgClosedT3`（すべての `m`）ではない。** 強い方しか無いときは
`ImgCofinalT3_of_ImgClosedT3` を挟めばよい。 -/
theorem ST_D3_conv3_of_parts (h2 : Wset.TowerGraft2) (he : Wset.TowerExp)
    {conv3 : TrioSeq → TrioSeq}
    (hI : ImgCofinalT3 conv3) (hO : OrderT3 conv3) (hU : SandwichUT3 conv3)
    (hb : ImgBlockT3 conv3) (hlen2 : ImgLenT3 conv3) (hd : ConvDiagT3 conv3)
    {M : TrioSeq} (hM : ST_TS M) : ST_D3 (conv3 M) :=
  ST_D3_conv3_holds h2 he (ReindexT1_of_cofinal hI hO hU hb hlen2) hd hM

/-- 強い `ImgClosedT3` から直に。 -/
theorem ST_D3_conv3_of_parts' (h2 : Wset.TowerGraft2) (he : Wset.TowerExp)
    {conv3 : TrioSeq → TrioSeq}
    (hI : ImgClosedT3 conv3) (hO : OrderT3 conv3) (hU : SandwichUT3 conv3)
    (hb : ImgBlockT3 conv3) (hlen2 : ImgLenT3 conv3) (hd : ConvDiagT3 conv3)
    {M : TrioSeq} (hM : ST_TS M) : ST_D3 (conv3 M) :=
  ST_D3_conv3_of_parts h2 he (ImgCofinalT3_of_ImgClosedT3 hI) hO hU hb hlen2 hd hM


/-- **★★ 弱い順序仮定版**（課題 L28）。`OrderT3` の代わりに
`Inj3`（単射性）＋ `OrderReindexT3`（`(←)` だけ・相手は像の展開の逆像に限る）で足りる。

`OrderT3` は `len ≤ 11` の母数で 24 件破れる（課題 L24/R9）が、
**この 2 本が真なら Lean 側は通る**。 -/
theorem ST_D3_conv3_of_parts'' (h2 : Wset.TowerGraft2) (he : Wset.TowerExp)
    {conv3 : TrioSeq → TrioSeq}
    (hI : ImgCofinalT3 conv3) (hj : Inj3 conv3) (hO : OrderReindexT3 conv3)
    (hU : SandwichUT3 conv3) (hb : ImgBlockT3 conv3) (hlen2 : ImgLenT3 conv3)
    (hd : ConvDiagT3 conv3) {M : TrioSeq} (hM : ST_TS M) : ST_D3 (conv3 M) :=
  ST_D3_conv3_holds h2 he (ReindexT1_of_cofinal' hI hj hO hU hb hlen2) hd hM

/-- **★★★ いちばん弱い仮定版**（課題 L31）。`OrderT3` も `SandwichUT3` も使わない。

    Inj3                 単射性（順序と無関係）
    OrderReindexT3       (←) だけ・相手は像の展開の逆像に限る
    SandwichUReindexT3   挟み撃ちの上・相手は同上

3 本とも `OrderT3` / `SandwichUT3` から出る（弱化の確認は上の 3 定理）。
どちらの強い版も実測では偽（`OrderT3` は `len ≤ 11` で 24 件、
`SandwichUT3` は `v<=4 len<=8` で 12 件）。 -/
theorem ST_D3_conv3_of_parts''' (h2 : Wset.TowerGraft2) (he : Wset.TowerExp)
    {conv3 : TrioSeq → TrioSeq}
    (hI : ImgCofinalT3 conv3) (hj : Inj3 conv3) (hO : OrderReindexT3 conv3)
    (hU : SandwichUReindexT3 conv3) (hb : ImgBlockT3 conv3)
    (hlen2 : ImgLenT3 conv3) (hd : ConvDiagT3 conv3)
    {M : TrioSeq} (hM : ST_TS M) : ST_D3 (conv3 M) :=
  ST_D3_conv3_holds h2 he (ReindexT1_of_cofinal'' hI hj hO hU hb hlen2) hd hM

/-- **`OrderReindexT3` の第 1 成分だけ**（第 2 成分は `ReindexT1D` では要らない）。 -/
def OrderReindexT3' (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {A B : TrioSeq}, ST_TS A → ST_TS B → ∀ {n m : ℕ}, 1 ≤ n → n + 1 ≤ m →
    (conv3 A)⟦m⟧ = conv3 B →
      (seqlex (conv3 (A⟦n⟧)) (conv3 B) → translate (A⟦n⟧) <o translate B)

theorem orderReindexT3'_of_orderReindexT3 {conv3 : TrioSeq → TrioSeq}
    (h : OrderReindexT3 conv3) : OrderReindexT3' conv3 := by
  intro A B hA hB n m hn hm heq
  exact (h hA hB hn hm heq).1

/-- **★ `ReindexT1D` は弱い 3 本から出る**（第 2 成分は使わない）。 -/
theorem ReindexT1D_of_cofinal {conv3 : TrioSeq → TrioSeq}
    (hI : ImgCofinalT3 conv3) (hj : Inj3 conv3) (hO : OrderReindexT3' conv3)
    (hU : SandwichUReindexT3 conv3) (hb : ImgBlockT3 conv3)
    (hlen2 : ImgLenT3 conv3) : ReindexT1D conv3 := by
  intro A hA hlen n hn
  obtain ⟨m, hm0, B, hB, heq⟩ := hI hA hlen (n + 1)
  refine ⟨m, B, by omega, hB, ?_, ?_, heq⟩
  · exact ole_of_sle3' (fun h => hj (ST_TS.oper hA hn) hB h)
      (hO hA hB hn hm0 heq) (hU hA hlen hB hn hm0 heq)
  · rw [← heq]
    exact seqlex_oper (hb hA) (hlen2 hA hlen) (by omega)

/-- **仮定を全部並べた形（DBMS の整礎性版）。`TowerGraft2` / `TowerExp` を使わない。** -/
theorem ST_D3_conv3_of_parts_D (wfD : WellFounded RD3)
    {conv3 : TrioSeq → TrioSeq}
    (hI : ImgCofinalT3 conv3) (hj : Inj3 conv3) (hO : OrderReindexT3' conv3)
    (hU : SandwichUReindexT3 conv3) (hb : ImgBlockT3 conv3)
    (hlen2 : ImgLenT3 conv3) (hd : ConvDiagT3 conv3)
    {M : TrioSeq} (hM : ST_TS M) : ST_D3 (conv3 M) :=
  ST_D3_conv3_D wfD (ReindexT1D_of_cofinal hI hj hO hU hb hlen2) hd hM

/-- **★★★★★ 仮定を全部並べた形の停止性**（課題 L38）。

    wfD                 DBMS 3 行 (z<2) の整礎性（新しい問題）
    ImgCofinalT3        像は展開で共終（Python 側で破れ 20）
    Inj3                単射性（実測 1882196 個で衝突 0）
    OrderReindexT3'     (←)・相手は像の展開の逆像に限る（実測 破れ 0）
    SandwichUReindexT3  挟み撃ちの上・相手は同上（実測 破れ 0）
    ImgBlockT3          像は `blockok 0`（残り 160〜230 行）
    ImgLenT3            **証明ずみ**
    ConvDiagT3          **証明ずみ**

**`TowerGraft2` / `TowerExp` / `Subst1gReviveSelf` を使わない。**
`PROOF-STATUS §5` の壁とは別の入り口である。 -/
theorem TRIO_terminates_of_dbms_wf_parts (wfD : WellFounded RD3)
    {conv3 : TrioSeq → TrioSeq}
    (hI : ImgCofinalT3 conv3) (hj : Inj3 conv3) (hO : OrderReindexT3' conv3)
    (hU : SandwichUReindexT3 conv3) (hb : ImgBlockT3 conv3)
    (hlen2 : ImgLenT3 conv3) (hd : ConvDiagT3 conv3) : WellFounded stepRel :=
  TRIO_terminates_of_dbms_wf wfD (ReindexT1D_of_cofinal hI hj hO hU hb hlen2) hd

/-! ### 11.4 `ImgLenT3` の証明（課題 L2 (a)） -/

namespace Conv3

set_option maxHeartbeats 1000000 in
/-- `conv3` は入力が空でなければ必ず 1 列以上を出す（本体の `cols` に
`(dd2, e1, e2)` が必ず 1 本入る）。 -/
theorem conv3_ne_nil (p : Col) (r : TrioSeq) (d : ℕ) (L : List Lent) (F : List Bool)
    (ps pw : ℕ × ℕ) (first force : Bool) (st : St) (nx : Option Col) (off : ℕ) :
    (conv3 (p :: r) d L F ps pw first force st nx off).1 ≠ [] := by
  rw [conv3.eq_def]
  dsimp only
  split <;>
    simp only [ne_eq, List.append_eq_nil_iff, List.cons_ne_nil, and_false, false_and,
      not_false_eq_true]

theorem conv3_ne_nil' {M : TrioSeq} (hM : M ≠ []) (d : ℕ) (L : List Lent) (F : List Bool)
    (ps pw : ℕ × ℕ) (first force : Bool) (st : St) (nx : Option Col) (off : ℕ) :
    (conv3 M d L F ps pw first force st nx off).1 ≠ [] := by
  obtain ⟨p, r, rfl⟩ := List.exists_cons_of_ne_nil hM
  exact conv3_ne_nil p r d L F ps pw first force st nx off

/-- `cols ++ w ++ w'` の長さの下界（`w` か `w'` の片方が空でなければ 2 以上）。 -/
theorem two_le_app (u v : TrioSeq) (z : Col) (w w' : TrioSeq)
    (h : w ≠ [] ∨ w' ≠ []) : 1 < ((u ++ v ++ [z]) ++ w ++ w').length := by
  have key : 1 ≤ w.length + w'.length := by
    rcases h with h | h
    · cases w with
      | nil => exact absurd rfl h
      | cons a b => simp only [List.length_cons]; omega
    · cases w' with
      | nil => exact absurd rfl h
      | cons a b => simp only [List.length_cons]; omega
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- `if X then Y else none = some Z` なら `X = true`（`lad0` を書き下さずに取り出す）。 -/
theorem eq_true_of_ite_some {α : Type} {X : Bool} {Y : Option α} {Z : α}
    (h : (if X = true then Y else none) = some Z) : X = true := by
  cases X
  · exact absurd h (by simp)
  · rfl

set_option maxHeartbeats 1000000 in
/-- 入力が 2 列以上なら像も 2 列以上。 -/
theorem conv3_len_two (p : Col) (r : TrioSeq) (hr : r ≠ []) (d : ℕ) (L : List Lent)
    (F : List Bool) (ps pw : ℕ × ℕ) (first force : Bool) (st : St) (nx : Option Col)
    (off : ℕ) :
    1 < (conv3 (p :: r) d L F ps pw first force st nx off).1.length := by
  have hAB : (r.takeWhile (fun q => decide (p.1 < q.1)))
      ++ (r.dropWhile (fun q => decide (p.1 < q.1))) = r :=
    List.takeWhile_append_dropWhile
  rw [conv3.eq_def]
  dsimp only
  split
  · -- 縮約の枝: `lad0 = true` なので `cols` は 2 列以上
    rename_i heq
    have hl := eq_true_of_ite_some heq
    simp only [if_pos hl, List.length_append, List.length_cons, List.length_nil]
    omega
  · -- ふつうの枝: `A ++ B = r ≠ []` なので `rA` か `rB` の像が空でない
    refine two_le_app _ _ _ _ _ ?_
    by_cases hA : (r.takeWhile (fun q => decide (p.1 < q.1))) = []
    · right
      apply conv3_ne_nil'
      intro hB
      rw [hA, hB] at hAB
      exact hr hAB.symm
    · left
      exact conv3_ne_nil' hA _ _ _ _ _ _ _ _ _ _

end Conv3

/-- **`ImgLenT3` は `Conv3.b2d3` について証明ずみ**（課題 L2 の (a)）。

`conv3` の本体は `cols` に本体の柱 `(dd2, e1, e2)` を必ず 1 本積む。だから
入力が空でなければ像も空でない（`Conv3.conv3_ne_nil`）。入力が 2 列以上なら
* 縮約が発火する枝では `lad0` が真なので `cols` 自身が 2 列以上、
* ふつうの枝では `A ++ B = r ≠ []` なので `A` か `B` の像が 1 列以上、
のどちらかで 2 列以上になる。 -/
theorem ImgLenT3_b2d3 : ImgLenT3 Conv3.b2d3 := by
  intro A _hA hlen
  obtain ⟨p, r, rfl⟩ : ∃ p r, A = p :: r := by
    cases A with
    | nil => simp at hlen
    | cons a b => exact ⟨a, b, rfl⟩
  have hr : r ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen
  unfold Conv3.b2d3
  exact Conv3.conv3_len_two p r hr _ _ _ _ _ _ _ _ _ _



/-! ### 11.5 `ImgBlockT3` の骨組み（課題 L2 (b)） -/

namespace Conv3

/-! ### `fit` の値の範囲 -/

/-- `fitAux` が返す深さは `[x, x+k)` の中。 -/
theorem fitAux_bounds {ST : List (ℕ × ℕ)} {w : ℕ} :
    ∀ {k x y : ℕ}, fitAux ST w x k = some y → x ≤ y ∧ y < x + k := by
  intro k
  induction k with
  | zero => intro x y h; simp [fitAux] at h
  | succ k ih =>
      intro x y h
      rw [fitAux] at h
      split at h
      · have : x = y := by simpa using h
        omega
      · have := ih h
        omega

/-- `d ≤ |ST|` なら `fit` の返す深さは `[d, |ST|]` の中。 -/
theorem fit_bounds {ST : List (ℕ × ℕ)} {d w y : ℕ} (hd : d ≤ ST.length)
    (h : fit ST d w = some y) : d ≤ y ∧ y ≤ ST.length := by
  rw [fit] at h
  have := fitAux_bounds h
  omega

/-- `fit` の既定値 `e` も `[d, |ST|]` に入っているなら `getD` の値も入る。 -/
theorem fit_getD_bounds {ST : List (ℕ × ℕ)} {d w e : ℕ} (hd : d ≤ ST.length)
    (he1 : d ≤ e) (he2 : e ≤ ST.length) :
    d ≤ (fit ST d w).getD e ∧ (fit ST d w).getD e ≤ ST.length := by
  cases h : fit ST d w with
  | none => simpa [h] using ⟨he1, he2⟩
  | some y =>
      have := fit_bounds hd h
      simpa [h] using this

/-- `ST.take d ++ [x]` の長さ（`d ≤ |ST|` のとき）。 -/
theorem len_take_app {ST : List (ℕ × ℕ)} {d : ℕ} (hd : d ≤ ST.length) (x : ℕ × ℕ) :
    (ST.take d ++ [x]).length = d + 1 := by
  simp [Nat.min_eq_left hd]

/-! ### 1 本の柱が出す `cols` の形

`conv3` は 1 本の BMS 列から最大 3 本の柱を出す:

    (d,   pw.1, pw.2)     行 0 の影   （`lad0` のとき）
    (dd0, base, pl2)      行 1 の影   （`lad1` のとき）
    (dd2, e1,   e2)       本体        （つねに）

不変量は **`d ≤ |ST|`**（開始深さは祖先の鎖 `ST` の長さ以下）。これがあると
`fit` の返す深さが `[d, |ST|]` に収まり、3 本の柱の行 0 は 1 ずつしか上がらない
（`steps1`）。積んだ後の鎖の長さはちょうど「最後の柱の行 0 + 1」になる。 -/

/-- `conv3` の 1 本ぶんの深さの計算が満たす性質。 -/
theorem depths_ok {ST ST1 ST2 : List (ℕ × ℕ)} {d h1 e1 e2 base pl2 dd0 dd1 dd2 : ℕ}
    {pw : ℕ × ℕ} {lad0 lad1 : Bool} {cols : TrioSeq}
    (hd : d ≤ ST.length)
    (hST1 : ST1 = if lad0 then ST.take d ++ [(pw.1, pw.2)] else ST)
    (hdd0 : dd0 = if lad0 then d + 1 else (fit ST d h1).getD (max d ST.length))
    (hST2 : ST2 = if lad1 then ST1.take dd0 ++ [(base, pl2)] else ST1)
    (hdd1 : dd1 = if lad1 then dd0 + 1 else dd0)
    (hdd2 : dd2 = if okPlace ST2 dd1 e1 then dd1 else (fit ST2 dd1 e1).getD dd1)
    (hcols : cols = (if lad0 then [((d : ℕ), pw.1, pw.2)] else []) ++
                    (if lad1 then [(dd0, base, pl2)] else []) ++ [(dd2, e1, e2)]) :
    d ≤ dd2 ∧ dd2 ≤ ST2.length ∧ steps1 cols ∧ (cols.headI).1 ≤ ST.length ∧
      (cols.getLastD (0, 0, 0)).1 = dd2 ∧ (∀ c ∈ cols, d ≤ c.1) := by
  have hL1t : lad0 = true → ST1.length = d + 1 := by
    intro h; rw [hST1, if_pos h]; exact len_take_app hd _
  have hL1f : lad0 ≠ true → ST1.length = ST.length := by
    intro h; rw [hST1, if_neg h]
  have hdd0t : lad0 = true → dd0 = d + 1 := by intro h; rw [hdd0, if_pos h]
  have hb0 : d ≤ dd0 ∧ dd0 ≤ ST1.length := by
    by_cases h : lad0 = true
    · rw [hdd0t h, hL1t h]; omega
    · rw [hdd0, if_neg h, hL1f h]
      exact fit_getD_bounds hd (by omega) (by omega)
  have hL2t : lad1 = true → ST2.length = dd0 + 1 := by
    intro h; rw [hST2, if_pos h]; exact len_take_app hb0.2 _
  have hL2f : lad1 ≠ true → ST2.length = ST1.length := by
    intro h; rw [hST2, if_neg h]
  have hdd1t : lad1 = true → dd1 = dd0 + 1 := by intro h; rw [hdd1, if_pos h]
  have hdd1f : lad1 ≠ true → dd1 = dd0 := by intro h; rw [hdd1, if_neg h]
  have hb1 : dd0 ≤ dd1 ∧ dd1 ≤ ST2.length := by
    by_cases h : lad1 = true
    · rw [hdd1t h, hL2t h]; omega
    · rw [hdd1f h, hL2f h]; exact ⟨le_refl _, hb0.2⟩
  have hb2 : dd1 ≤ dd2 ∧ dd2 ≤ ST2.length := by
    rw [hdd2]; split
    · exact ⟨le_refl _, hb1.2⟩
    · exact fit_getD_bounds hb1.2 (le_refl _) hb1.2
  subst hcols
  by_cases hA : lad0 = true <;> by_cases hB : lad1 = true
  · -- 行 0 の影 ＋ 行 1 の影 ＋ 本体
    have g0 := hdd0t hA; have g2 := hL2t hB
    simp only [if_pos hA, if_pos hB, List.cons_append, List.nil_append]
    refine ⟨by omega, hb2.2, ?_, ?_, ?_, ?_⟩
    · simp only [steps1_cons_cons]; exact ⟨by omega, by omega, trivial⟩
    · simpa using hd
    · simp
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp <;> omega
  · -- 行 0 の影 ＋ 本体
    have g0 := hdd0t hA; have g1 := hL1t hA; have g2 := hL2f hB
    simp only [if_pos hA, if_neg hB, List.cons_append, List.nil_append, List.append_nil]
    refine ⟨by omega, hb2.2, ?_, ?_, ?_, ?_⟩
    · simp only [steps1_cons_cons]; exact ⟨by omega, trivial⟩
    · simpa using hd
    · simp
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp <;> omega
  · -- 行 1 の影 ＋ 本体
    have g1 := hL1f hA; have g2 := hL2t hB
    simp only [if_neg hA, if_pos hB, List.cons_append, List.nil_append]
    refine ⟨by omega, hb2.2, ?_, ?_, ?_, ?_⟩
    · simp only [steps1_cons_cons]; exact ⟨by omega, trivial⟩
    · simp only [List.headI]; omega
    · simp
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp <;> omega
  · -- 本体だけ
    have g1 := hL1f hA; have g2 := hL2f hB
    simp only [if_neg hA, if_neg hB, List.nil_append]
    refine ⟨by omega, hb2.2, ?_, ?_, ?_, ?_⟩
    · trivial
    · simp only [List.headI]; omega
    · simp
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl <;> simp <;> omega



/-! ### 呼び出しごとの不変量 `BlkOK`

`conv3` の 1 回の呼び出しについて、開始深さ `d` が祖先の鎖の長さ以下
（`d ≤ |st.ST|`）なら:

* 出した柱は `steps1`（行 0 の段差が 1 以下）、
* 先頭の柱の行 0 は `|st.ST|` 以下（＝直前の柱の行 0 + 1 以下）、
* 末尾の柱の行 0 + 1 はちょうど**終了時の**鎖の長さ、
* 何も出さなかったら鎖の長さは変わらない、
* 終了時の鎖の長さは `d` 以上。

3 番目と 2 番目が噛み合うので、**連結しても `steps1` が保たれる**
（`BlkOK_app`）。これが `blockok` の証明の骨である。 -/

/-- `conv3` / `convResid` の 1 回の呼び出しが満たす不変量。 -/
def BlkOK (d : ℕ) (st : St) (res : TrioSeq × St) : Prop :=
  steps1 res.1
    ∧ d ≤ res.2.ST.length
    ∧ (res.1 = [] → res.2.ST.length = st.ST.length)
    ∧ (res.1 ≠ [] → (res.1.headI).1 ≤ st.ST.length)
    ∧ (res.1 ≠ [] → (res.1.getLastD (0, 0, 0)).1 + 1 = res.2.ST.length)
    ∧ (∀ c ∈ res.1, d ≤ c.1)
    ∧ (st.dmap ≠ [] → res.2.dmap ≠ [])
    ∧ (res.2.dmap ≠ [] → res.2.dmap.getLastD 0 + 1 = res.2.ST.length)

/-! ### 課題 L16: `steps1` は接頭辞・接尾辞で保たれる

節 10 の側条件 `A.head.1 ≤ p.1 + 1` は **BMS の隣接条件**（`steps1`）そのもの
なので、`BlkInv` に `steps1 M` を足す必要がある。`conv3` の再帰は
`takeWhile` / `dropWhile` / `take` / `drop` しか使わないので、
接頭辞・接尾辞で保たれることを言えば帰納は回る。 -/

theorem steps1_prefixT {A B : TrioSeq} (h : steps1 B) (hp : A <+: B) : steps1 A := by
  obtain ⟨t, rfl⟩ := hp
  exact (steps1_append.mp h).1

theorem steps1_suffixT {A B : TrioSeq} (h : steps1 B) (hs : A <:+ B) : steps1 A := by
  obtain ⟨t, rfl⟩ := hs
  exact (steps1_append.mp h).2.1

theorem steps1_takeT {B : TrioSeq} (h : steps1 B) (n : ℕ) : steps1 (B.take n) :=
  steps1_prefixT h (List.take_prefix n B)

theorem steps1_dropT {B : TrioSeq} (h : steps1 B) (n : ℕ) : steps1 (B.drop n) :=
  steps1_suffixT h (List.drop_suffix n B)

theorem steps1_takeWhileT {B : TrioSeq} (h : steps1 B) (f : Col → Bool) :
    steps1 (B.takeWhile f) :=
  steps1_prefixT h (List.takeWhile_prefix f)

theorem steps1_dropWhileT {B : TrioSeq} (h : steps1 B) (f : Col → Bool) :
    steps1 (B.dropWhile f) :=
  steps1_suffixT h (List.dropWhile_suffix f)

theorem steps1_tailT {B : TrioSeq} (h : steps1 B) : steps1 B.tail := by
  cases B with
  | nil => simpa using h
  | cons p t => simpa using steps1_dropT h 1

/-! ### 課題 L16: 節 10（`dmap` の下界）と 節 12（下位の項の保存）

`BlkOK` に足すのではなく**別の述語**として立てる。`BlkOK` は 8 節のまま
なので、既存の補題・射影がまったく動かない（`BlkOK` に引数を足すと
`.2.2.2.2.2.2.2` のような射影が全部ずれる）。

    節 10  Dm10 d m res   出力の `dmap` は「もとの深さ 1 段につき像も 1 段」
    節 12  Dm12 m st res  ブロックは自分の先頭より浅い `dmap` の項に触らない

実測（`tools/dbms/R1-NOTES.md` 節 10、`gen3 <=8` 全数 13108043 呼び出し ＋
展開閉包 1181746 呼び出しで違反 0・陽性対照つき）／
節 12 は課題 L16 の測定（`conv3` の全呼び出し、違反 0、陽性対照
「添字を 1 つ広げる」で 27584 / 521 発火）。 -/

/-- **節 10**: もとの深さ `j` の像は、ブロックの先頭 `m` から数えて
少なくとも `j - m` 段は深い。 -/
def Dm10 (d m : ℕ) (st : St) : Prop :=
  ∀ j, m ≤ j → j < st.dmap.length → d + (j - m) ≤ st.dmap.getD j 0

/-- **節 12**: ブロックは自分の先頭 `m` より浅い `dmap` の項に触らない。

⚠ **結論に `k < |st.dmap|` を含む強い形は偽**である（課題 R1）。`rB` 版だけでなく
**`rA` 版も偽**で、最小反例は 8 列:

    M = (0,0,0)(1,1,1)(2,1,0)(1,1,0)(2,2,1)(3,1,0)(4,0,0)(5,0,0)
    cA の呼び出し、p.1 = 4、k = 4
    呼び出し前 dmap = [0,3,4,5]（長さ 4）、後 [0,3,4,5,6]（長さ 5）
    k = 4 < p.1+1 = 5 かつ k < |res.dmap| = 5、だが k は |st.dmap| = 4 の外
    破れ 0 / 11 / 349（`<=7` 列 / `<=8` 列 / `<=6` の展開閉包）

`<=7` 列では 0 で、**8 列と展開閉包で初めて出る**。値は 1 つも変わらないので、
`k < |st.dmap|` を**仮定に回した含意の形**にすると 3 母集団すべてで違反 0。 -/
def Dm12 (m : ℕ) (st : St) (res : TrioSeq × St) : Prop :=
  ∀ k, k < m → k < res.2.dmap.length → k < st.dmap.length →
    res.2.dmap.getD k 0 = st.dmap.getD k 0

/-- `(l ++ [x]).getD |l| 0 = x`。 -/
theorem getD_snoc_len {l : List ℕ} {x : ℕ} : (l ++ [x]).getD l.length 0 = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp

/-- `(l ++ [x]).getD k 0 = l.getD k 0`（`k < |l|`）。 -/
theorem getD_snoc_lt {l : List ℕ} {x k : ℕ} (hk : k < l.length) :
    (l ++ [x]).getD k 0 = l.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hk]

/-- **`conv3` の 1 列ぶんの状態は節 10 を満たす**。`dmap` の更新が
`st.dmap.take p.1 ++ [dd2]` なので、`j ≥ p.1` で範囲内なのは `j = p.1` だけで、
そこの値は `dd2 ≥ d`（`depths_le`）である。 -/
theorem Dm10_of_take {d m dd2 : ℕ} {dmo : List ℕ} {st : St}
    (hres : st.dmap = dmo.take m ++ [dd2]) (hdd : d ≤ dd2) : Dm10 d m st := by
  intro j hj hlen
  rw [hres] at hlen ⊢
  rw [List.length_append, List.length_take, List.length_singleton] at hlen
  have hjm : j = m := by omega
  subst hjm
  have hlt : (dmo.take j).length = j := by rw [List.length_take]; omega
  have hval : ((dmo.take j) ++ [dd2]).getD j 0 = dd2 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlt]
    simp
  rw [hval]
  omega

/-- **`conv3` の 1 列ぶんの状態は節 12 を満たす**（`take` は下位の項に触らない）。 -/
theorem Dm12_of_take {m dd2 : ℕ} {dmo : List ℕ} {st : St} {res : TrioSeq × St}
    (hst : st.dmap = dmo) (hres : res.2.dmap = dmo.take m ++ [dd2]) :
    Dm12 m st res := by
  intro k hk hlen hk0
  rw [hres] at hlen ⊢
  rw [hst] at hk0 ⊢
  have hlt : k < (dmo.take m).length := by rw [List.length_take]; omega
  rw [getD_snoc_lt hlt, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD]
  first
    | rw [List.getElem?_take (by omega)]
    | rw [List.getElem?_take_of_lt (by omega)]
    | simp [List.getElem?_take, show k < m by omega]

theorem Dm10_nil {d m : ℕ} {st : St} (h : ∀ j, m ≤ j → j < st.dmap.length →
    d + (j - m) ≤ st.dmap.getD j 0) : Dm10 d m st := h

theorem Dm12_refl {m : ℕ} {st : St} : Dm12 m st ([], st) :=
  fun _ _ _ _ => rfl

/-- **状態の不変量（課題 R1 の「節 12''」）**: ブロックの頭より浅い `dmap` の項は
`d + 1` 以下。

⚠ **`≤ d` は偽**。最小反例は 5 列:

    M = (0,0,0)(1,1,1)(1,0,0)(2,1,1)(2,0,0)
    ブロックの頭 p = (2,0,0)、d = 2、st.dmap = [0,3]、k = 1
    dmap[1] = 3 > d = 2

`gen3 <=5` 全数で 1 件、`<=7` 全数 530680 呼び出しで 50 件（`<=4` では 0 なので
**5 列がちょうど境目**）。`≤ d + 1` にすると **530680 呼び出しで違反 0**、
陽性対照 `≤ d` が 50、`≤ d - 1` が 449 で**タイト**。

これが `cols_blk` で「古い `dmap` の項に `≤ dd2 + 1` が要る」穴を塞ぐ:
`st.dmap[k] ≤ d + 1 ≤ dd2 + 1`（`d ≤ dd2` は `depths_le`）。 -/
def Dm11 (d m : ℕ) (st : St) : Prop :=
  ∀ k, k < m → k < st.dmap.length → st.dmap.getD k 0 ≤ d + 1

/-- **節 10 は `m` について上向きに単調**（`m` が大きいほど弱い）。

`Dm10` は `res.2.dmap`（＝ 最後の状態）しか見ないので、5 重連結の**結論**は
**いちばん最後のブロック**のものがそのまま使える。最後は `cB`（`m' = Bq.head.1 ≤ p.1`、
深さも `d`）なので、これで `Dm10 d p.1` が出る。**中間の場合は結論側には現れない。** -/
theorem Dm10_mono_m {d m m' : ℕ} {st : St} (hle : m' ≤ m)
    (h : Dm10 d m' st) : Dm10 d m st := by
  intro j hj hlen
  have h5 := h j (by omega) hlen
  omega

/-- **節 10 の付け替え**（課題 L20）: `(d', m')` の節 10 から `(d, m)` の節 10 へ。

`j ≥ m'` の部分は**数の条件 `d + m' ≤ d' + m`** だけで移る。`m ≤ j < m'` の
中間だけを別に与える。 -/
theorem Dm10_shift {d d' m m' : ℕ} {st : St}
    (hmm : d + m' ≤ d' + m) (h : Dm10 d' m' st)
    (hmid : ∀ j, m ≤ j → j < m' → j < st.dmap.length →
      d + (j - m) ≤ st.dmap.getD j 0) : Dm10 d m st := by
  intro j hj hlen
  by_cases hjm : m' ≤ j
  · have h5 := h j hjm hlen
    omega
  · exact hmid j hj (by omega) hlen

/-- **`rA` の付け替え（弱い版）**。`d ≤ dd2` だけで `(d, p.1)` の節 10 に移せる
（`d + 1 ≤ dd2` が要るのは結論を `(d+1, p.1)` にするときだけ）。非縮約の枝で使う。 -/
theorem Dm10_of_child' {d dd2 m : ℕ} {st1 : St} {res : TrioSeq × St}
    (hdd : d ≤ dd2) (h : Dm10 (dd2 + 1) (m + 1) res.2)
    (h12 : Dm12 (m + 1) st1 res)
    (hst1 : st1.dmap.getD m 0 = dd2) (hlen1 : m < st1.dmap.length) :
    Dm10 d m res.2 := by
  refine Dm10_shift (by omega) h ?_
  intro j hj hjm hlen
  have hjeq : j = m := by omega
  subst hjeq
  rw [h12 j (by omega) hlen hlen1, hst1]
  omega

/-- **`rA` の付け替え**（課題 L20 の要）。`cA` は深さ `dd2+1`・先頭 `p.1+1` で
呼ばれるので、`d + 1 ≤ dd2` があれば `(d+1, p.1)` の節 10 に移せる:

* `j > p.1` … `(dd2+1) + (j - p.1 - 1) ≥ (d+1) + (j - p.1)` ⟺ `d + 1 ≤ dd2`
* `j = p.1` … `cA` は添字 `p.1` を触らない（`Dm12`）ので値は `dd2 ≥ d + 1`

⟹ **課題 L18 で「鎖が閉じない」と報告した箇所はここで閉じる**
（`cU` の入口が要求するのは `Dm10 (d+1) U.head.1 rA.2` で、
課題 R1 の測定より `U.head.1 = p.1`（`<=7` 列で 6/6）だから）。 -/
theorem Dm10_of_child {d dd2 m : ℕ} {st1 : St} {res : TrioSeq × St}
    (hdd : d + 1 ≤ dd2) (h : Dm10 (dd2 + 1) (m + 1) res.2)
    (h12 : Dm12 (m + 1) st1 res)
    (hst1 : st1.dmap.getD m 0 = dd2) (hlen1 : m < st1.dmap.length) :
    Dm10 (d + 1) m res.2 := by
  refine Dm10_shift (by omega) h ?_
  intro j hj hjm hlen
  have hjeq : j = m := by omega
  subst hjeq
  rw [h12 j (by omega) hlen hlen1, hst1]
  omega

/-- **節 12 の連結**（`m ≤ m'` が要る）。 -/
theorem Dm12_app {m m' : ℕ} {st stm st' : St} {X Y : TrioSeq} (hle : m ≤ m')
    (hstm : m ≤ stm.dmap.length)
    (hX : Dm12 m st (X, stm)) (hY : Dm12 m' stm (Y, st')) :
    Dm12 m st (X ++ Y, st') := by
  intro k hk hlen hk0
  simp only at hlen ⊢
  have h1 : k < stm.dmap.length := by omega
  have h2 := hY k (by omega) hlen h1
  simp only at h2
  have h4 := hX k hk h1 hk0
  simp only at h4
  rw [h2, h4]

/-- 状態の `dmap` 不変量: 最後に書いた像の深さ ＋ 1 が鎖の長さ。
実測（`lean/l11_blkmeas.py`）: `<=6` 列 48997 呼び出し ＋ 7 列 1134 呼び出しで
**違反 0**。`dmap` の狭義単調性や「全要素 < |ST|」は**偽**なので、真なのはこれだけ。 -/
def DmOK (st : St) : Prop :=
  st.dmap ≠ [] → st.dmap.getLastD 0 + 1 = st.ST.length

theorem BlkOK_nil {d : ℕ} {st : St} (hd : d ≤ st.ST.length) (hdm : DmOK st) :
    BlkOK d st ([], st) :=
  ⟨trivial, hd, fun _ => rfl, fun h => absurd rfl h, fun h => absurd rfl h,
    fun _ hc => absurd hc (by simp), fun h => h, hdm⟩

/-- 空でない `Y` に付ける既定値は `getLastD` の値に効かない。 -/
theorem getLastD_indep {Y : TrioSeq} (hy : Y ≠ []) (a b : Col) :
    Y.getLastD a = Y.getLastD b := by
  cases Y with
  | nil => exact absurd rfl hy
  | cons c Y => rw [List.getLastD_cons, List.getLastD_cons]

/-- `Y` が空でなければ `X ++ Y` の末尾は `Y` の末尾。 -/
theorem getLastD_app {Y : TrioSeq} (hy : Y ≠ []) :
    ∀ (X : TrioSeq) (dd : Col), (X ++ Y).getLastD dd = Y.getLastD dd := by
  intro X
  induction X with
  | nil => intro dd; simp
  | cons a X ih =>
      intro dd
      rw [List.cons_append, List.getLastD_cons, ih a]
      exact getLastD_indep hy a dd

/-- **連結の補題**。`X` を出した後の状態から `Y` を出したなら、`X ++ Y` も
不変量を満たす。`steps1` の継ぎ目は「`Y` の先頭 ≤ 途中の鎖の長さ = `X` の末尾 + 1」
でつながる。 -/
theorem BlkOK_app {d d' : ℕ} {st stm st' : St} {X Y : TrioSeq}
    (hdd : d ≤ d') (hX : BlkOK d st (X, stm)) (hY : BlkOK d' stm (Y, st')) :
    BlkOK d st (X ++ Y, st') := by
  obtain ⟨hs1, hl1, he1, hh1, hg1, hlow1, hn1, hm1⟩ := hX
  obtain ⟨hs2, hl2, he2, hh2, hg2, hlow2, hn2, hm2⟩ := hY
  simp only at hs1 hl1 he1 hh1 hg1 hlow1 hs2 hl2 he2 hh2 hg2 hlow2
  refine ⟨?_, (by omega : d ≤ st'.ST.length), ?_, ?_, ?_, ?_, fun h => hn2 (hn1 h), hm2⟩
  · refine steps1_append.mpr ⟨hs1, hs2, ?_⟩
    by_cases hx : X = []
    · exact Or.inl hx
    · by_cases hy : Y = []
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr (by have := hh2 hy; have := hg1 hx; omega))
  · intro h
    have hx : X = [] := (List.append_eq_nil_iff.mp h).1
    have hy : Y = [] := (List.append_eq_nil_iff.mp h).2
    rw [he2 hy, he1 hx]
  · intro _
    by_cases hx : X = []
    · subst hx
      by_cases hy : Y = []
      · subst hy; simp at *
      · rw [List.nil_append]
        have := hh2 hy
        rw [he1 rfl] at this
        exact this
    · obtain ⟨a, X', rfl⟩ := List.exists_cons_of_ne_nil hx
      simpa using hh1 (by simp)
  · intro _
    by_cases hy : Y = []
    · subst hy
      rw [List.append_nil, he2 rfl]
      by_cases hx : X = []
      · subst hx; simp at *
      · exact hg1 hx
    · rw [getLastD_app hy]
      exact hg2 hy
  · intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hlow1 c h
    · exact le_trans hdd (hlow2 c h)

/-- `BlkOK` は開始深さについて**下向きに単調**（節 2 と節 6 が緩むだけ）。 -/
theorem BlkOK_mono {d d' : ℕ} {st : St} {res : TrioSeq × St} (h : d' ≤ d)
    (hb : BlkOK d st res) : BlkOK d' st res := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hb
  exact ⟨h1, by omega, h3, h4, h5, fun x hx => le_trans h (h6 x hx), h7, h8⟩

/-- `(l ++ [x]).getLastD dflt = x`（型を選ばない版）。 -/
theorem getLastD_snoc {α : Type} : ∀ (l : List α) (x dflt : α),
    (l ++ [x]).getLastD dflt = x
  | [], _, _ => rfl
  | a :: t, x, _ => by rw [List.cons_append, List.getLastD_cons]; exact getLastD_snoc t x a

/-- 空でないリストの `getLastD` はそのリストの元。 -/
theorem getLastD_memT {l : TrioSeq} (h : l ≠ []) (dflt : Col) : l.getLastD dflt ∈ l := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast (h := h)]
  simpa using List.getLast_mem h

/-- **出力の鎖の長さの下界**。入口の鎖が `k` 以上で `k ≤ d + 1` なら、出口も `k`
以上。空なら鎖は変わらず、空でなければ末尾の柱の行 0 が `d` 以上（節 6）だから。 -/
theorem BlkOK_ST_ge {d k : ℕ} {st : St} {res : TrioSeq × St} (h : BlkOK d st res)
    (hst : k ≤ st.ST.length) (hk : k ≤ d + 1) : k ≤ res.2.ST.length := by
  obtain ⟨-, -, h3, -, h5, h6, -, -⟩ := h
  by_cases hn : res.1 = []
  · rw [h3 hn]; exact hst
  · have hl := h5 hn
    have hm := h6 _ (getLastD_memT hn (0, 0, 0))
    omega

/-- **連結の補題（開始深さが下がってもよい版）**。

`convResid` は残余を**森**として読むので、次の木の開始深さは
`rd - (c.1 - tail[0].1)` と**下がる**。そこでは `BlkOK_app` の `d ≤ d'` が
使えない。`d ≤ d'` は結論の第 2 項 `d ≤ st'.ST.length` を出すためだけに
使われているので、それを直に仮定に取る。 -/
theorem BlkOK_app' {d d' : ℕ} {st stm st' : St} {X Y : TrioSeq}
    (hfin : d ≤ st'.ST.length) (hlowY : ∀ c ∈ Y, d ≤ c.1)
    (hX : BlkOK d st (X, stm)) (hY : BlkOK d' stm (Y, st')) :
    BlkOK d st (X ++ Y, st') := by
  obtain ⟨hs1, hl1, he1, hh1, hg1, hlow1, hn1, hm1⟩ := hX
  obtain ⟨hs2, hl2, he2, hh2, hg2, hlow2, hn2, hm2⟩ := hY
  simp only at hs1 hl1 he1 hh1 hg1 hlow1 hs2 hl2 he2 hh2 hg2 hlow2
  refine ⟨?_, hfin, ?_, ?_, ?_, ?_, fun h => hn2 (hn1 h), hm2⟩
  · refine steps1_append.mpr ⟨hs1, hs2, ?_⟩
    by_cases hx : X = []
    · exact Or.inl hx
    · by_cases hy : Y = []
      · exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr (by have := hh2 hy; have := hg1 hx; omega))
  · intro h
    have hx : X = [] := (List.append_eq_nil_iff.mp h).1
    have hy : Y = [] := (List.append_eq_nil_iff.mp h).2
    rw [he2 hy, he1 hx]
  · intro _
    by_cases hx : X = []
    · subst hx
      by_cases hy : Y = []
      · subst hy; simp at *
      · rw [List.nil_append]
        have := hh2 hy
        rw [he1 rfl] at this
        exact this
    · obtain ⟨a, X', rfl⟩ := List.exists_cons_of_ne_nil hx
      simpa using hh1 (by simp)
  · intro _
    by_cases hy : Y = []
    · subst hy
      rw [List.append_nil, he2 rfl]
      by_cases hx : X = []
      · subst hx; simp at *
      · exact hg1 hx
    · rw [getLastD_app hy]
      exact hg2 hy
  · intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hlow1 c h
    · exact hlowY c h

/-- `depths_ok` を `BlkOK` の形に包んだもの（`conv3` の 1 列ぶん）。 -/
theorem cols_blk {ST ST1 ST2 : List (ℕ × ℕ)} {d h1 e1 e2 base pl2 dd0 dd1 dd2 prv nc : ℕ}
    {pw : ℕ × ℕ} {lad0 lad1 : Bool} {cols : TrioSeq} {st : St} {dm : List ℕ}
    {Mo : TrioSeq} {rcl : List (ℕ × ℕ)}
    (hd : d ≤ st.ST.length) (hSTe : ST = st.ST)
    (hST1 : ST1 = if lad0 then ST.take d ++ [(pw.1, pw.2)] else ST)
    (hdd0 : dd0 = if lad0 then d + 1 else (fit ST d h1).getD (max d ST.length))
    (hST2 : ST2 = if lad1 then ST1.take dd0 ++ [(base, pl2)] else ST1)
    (hdd1 : dd1 = if lad1 then dd0 + 1 else dd0)
    (hdd2 : dd2 = if okPlace ST2 dd1 e1 then dd1 else (fit ST2 dd1 e1).getD dd1)
    (hcols : cols = (if lad0 then [((d : ℕ), pw.1, pw.2)] else []) ++
                    (if lad1 then [(dd0, base, pl2)] else []) ++ [(dd2, e1, e2)])
    (hdmne : dm ≠ []) (hdmlast : dm.getLastD 0 = dd2) :
    BlkOK d st
      (cols, { ST := ST2.take dd2 ++ [(e1, e2)], prev := prv, dmap := dm, Mo := Mo,
               nc := nc, rc := rcl }) := by
  subst hSTe
  obtain ⟨hdd, hd2, hstep, hhead, hlast, hlow⟩ :=
    depths_ok hd hST1 hdd0 hST2 hdd1 hdd2 hcols
  have hst1 : (ST2.take dd2 ++ [(e1, e2)]).length = dd2 + 1 := len_take_app hd2 _
  have hne : cols ≠ [] := by
    rw [hcols]
    simp only [ne_eq, List.append_eq_nil_iff, List.cons_ne_nil, and_false,
      not_false_eq_true]
  exact ⟨hstep, by simp only []; omega, fun h => absurd h hne, fun _ => hhead,
    fun _ => by simp only []; omega, hlow, fun _ => hdmne,
    fun _ => by simp only []; rw [hdmlast]; omega⟩

/-- `depths_ok` の深さの部分だけ（`cols` を含まない形）。

`cols` を結論に含めると `e2` や `pw` が単一化で決まらないので、深さだけの
形を別に用意しておく。 -/
theorem depths_le {ST ST1 ST2 : List (ℕ × ℕ)} {d h1 e1 base pl2 dd0 dd1 dd2 : ℕ}
    {pw : ℕ × ℕ} {lad0 lad1 : Bool}
    (hd : d ≤ ST.length)
    (hST1 : ST1 = if lad0 then ST.take d ++ [(pw.1, pw.2)] else ST)
    (hdd0 : dd0 = if lad0 then d + 1 else (fit ST d h1).getD (max d ST.length))
    (hST2 : ST2 = if lad1 then ST1.take dd0 ++ [(base, pl2)] else ST1)
    (hdd1 : dd1 = if lad1 then dd0 + 1 else dd0)
    (hdd2 : dd2 = if okPlace ST2 dd1 e1 then dd1 else (fit ST2 dd1 e1).getD dd1) :
    d ≤ dd2 ∧ dd2 ≤ ST2.length :=
  ⟨(depths_ok (e2 := 0) hd hST1 hdd0 hST2 hdd1 hdd2 rfl).1,
   (depths_ok (e2 := 0) hd hST1 hdd0 hST2 hdd1 hdd2 rfl).2.1⟩

/-- `fit` の値は既定値 `d` 以上（`fitAux` は `d` から上へ探すので）。 -/
theorem fit_getD_ge {ST : List (ℕ × ℕ)} (d w : ℕ) : d ≤ (fit ST d w).getD d := by
  cases h : fit ST d w with
  | none => simp [h]
  | some y =>
      rw [fit] at h
      have := fitAux_bounds h
      simp only [h, Option.getD_some]
      omega

/-- `lad0 = true` なら本体の深さは `d + 1` 以上（行 0 の影を 1 本立てるから）。
縮約の枝では `cfm` が `lad0` の中にしか無いので、これがつねに使える。 -/
theorem depths_le_lad0 {ST ST2 : List (ℕ × ℕ)} {d h1 e1 dd0 dd1 dd2 : ℕ}
    {lad0 lad1 : Bool} (hl0 : lad0 = true)
    (hdd0 : dd0 = if lad0 then d + 1 else (fit ST d h1).getD (max d ST.length))
    (hdd1 : dd1 = if lad1 then dd0 + 1 else dd0)
    (hdd2 : dd2 = if okPlace ST2 dd1 e1 then dd1 else (fit ST2 dd1 e1).getD dd1) :
    d + 1 ≤ dd2 := by
  have h0 : dd0 = d + 1 := by rw [hdd0, if_pos hl0]
  have h1' : dd0 ≤ dd1 := by rw [hdd1]; split <;> omega
  have h2' : dd1 ≤ dd2 := by
    rw [hdd2]; split
    · exact le_rfl
    · exact fit_getD_ge _ _
  omega

/-- `getD` の最後の位置は `getLastD`。 -/
theorem getD_last {dm : List ℕ} : dm.getD (dm.length - 1) 0 = dm.getLastD 0 := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
    List.getD_eq_getElem?_getD]

/-- **`dmapAt` の両側の評価。**

`dmap.last + 1 = |ST|`（`BlkOK` の節 8）から、`k` が

* `k = |dm|`（範囲外がちょうど 1 個だけ外） … `dmapAt = dm.last + 1 = n`
* `k = |dm| - 1`（範囲内の**最後**）      … `dmapAt = dm.last = n - 1`

のどちらでも閉じる。実測（`lean/l11_blkmeas.py`）ではこの 2 つしか起きない
（`<=6` 列 0 回、7 列の縮約発火 294 個で 6 回 = 前者 4 ＋ 後者 2）。
残るのは `k + 1 < |dm|` の場合だけで、**実測では 0 回**。 -/
theorem dmapAt_bounds {dm : List ℕ} {k n d : ℕ} (hne : dm ≠ [])
    (hlast : dm.getLastD 0 + 1 = n) (hd : d + 1 ≤ n) (hk : k ≤ dm.length)
    (hin : k + 1 < dm.length → d ≤ dm.getD k 0 ∧ dm.getD k 0 ≤ n) :
    d ≤ dmapAt dm k ∧ dmapAt dm k ≤ n := by
  unfold dmapAt
  rw [if_neg hne]
  by_cases h : k < dm.length
  · rw [if_pos h]
    by_cases h2 : k + 1 < dm.length
    · exact hin h2
    · have hkk : k = dm.length - 1 := by omega
      subst hkk
      rw [getD_last]
      omega
  · rw [if_neg h]
    have hkk : k = dm.length := by omega
    subst hkk
    simp only [Nat.sub_self]
    omega

/-! ### `blockok` の本体（**まだ証明していない — 仮定 `BlkInv` に落とした**）

`conv3` の再帰に沿った不変量。`conv3.induct`（相互再帰版の関数帰納法）で
6 つの枝に割れる。土台（`depths_ok`）と継ぎ目（`BlkOK_app`）は証明ずみだが、
**帰納法そのものはまだ通っていない**。未証明のかけらをファイルに残さないため、残りを
`BlkInv` という 1 本の命題に括り出してある（`ST_D3_conv3_of_parts` が仮定を
並べているのと同じ流儀）。詰まった点と残りの補題は `lean/L1-NOTES.md` の
「課題 L2」に書いた。要点だけ:

1. `conv3.induct` は使える（`intro` を 49 本入れると枝の局所値が全部名前つきで
   手に入る）。空の枝は `conv3_nil` ＋ `BlkOK_nil` で**閉じた**。
2. 縮約でない枝は `depths_ok` ＋ `BlkOK_app` ×2 で組めるが、最後に
   `rw [conv3.eq_def]; dsimp only` で開いた**巨大な項**と、局所値で書いた
   証明項との defeq 検査が `whnf` で燃え尽きる（2000000 heartbeats でも足りない）。
   `conv3` の 1 列ぶんの本体を**名前つきの関数に括り出す**（`conv3Body` など）と
   等式が構文的な書き換えになって解ける見込み。定義の意味は変えない。
3. 縮約の枝は、さらに 2 つの補題が要る（下の doc を見よ）。 -/

/-- **`contrOne` が見つける双子 `q` は `p` と同じ深さ**（定義の門そのもの）。

`contrOne` は `if (q.2.1, q.2.2) ≠ qlab ∨ q.1 ≠ p.1 then none` で弾くので、
`some` が返るなら `q.1 = p.1` である。これが課題 L16 の側条件 a5 の残り
（`Bq.head.1 ≤ p.1`）を出す: `deepGe_head_lt` で `Bq.head.1 ≤ q.1` だから。 -/
theorem contrOne_q_eq {p : Col} {A B : TrioSeq} {ps : ℕ × ℕ}
    {v s2 prev0 e kU kp : ℕ} {na : Col}
    (h : contrOne p A B ps v s2 prev0 e = some (kU, kp, na)) :
    ((B.drop kU).headD (0, 0, 0)).1 = p.1 := by
  unfold contrOne at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i q r2 hq
    split at h
    · exact absurd h (by simp)
    · rename_i hne
      have hkU : kU = unitsLen p.1 (ps.1 + e, ps.2) B := by
        repeat' split at h
        all_goals
          first
            | exact (congrArg (fun t => t.1) (Option.some.inj h)).symm
            | exact absurd h (by simp)
      rw [hkU, hq]
      simp only [List.headD_cons]
      push_neg at hne
      exact hne.2

/-- `contrFind` の双子も同じ深さ。 -/
theorem contrFind_q_eq {p : Col} {A B : TrioSeq} {ps : ℕ × ℕ}
    {v s2 prev0 e kU kp : ℕ} {na : Col}
    (h : contrFind p A B ps v s2 prev0 = some (e, kU, kp, na)) :
    ((B.drop kU).headD (0, 0, 0)).1 = p.1 := by
  unfold contrFind at h
  split at h
  · rename_i x hx
    obtain ⟨kU', kp', na'⟩ := x
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, h1, h2, h3⟩ := h
    subst h1; subst h2; subst h3
    exact contrOne_q_eq hx
  · split at h
    · rename_i x hx
      obtain ⟨kU', kp', na'⟩ := x
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, h1, h2, h3⟩ := h
      subst h1; subst h2; subst h3
      exact contrOne_q_eq hx
    · exact absurd h (by simp)

/-- `contrFind` が返す `e` は `0` か `1`。 -/
theorem contrFind_e_le {p : Col} {A B : TrioSeq} {ps : ℕ × ℕ}
    {v s2 prev0 e kU kp : ℕ} {na : Col}
    (h : contrFind p A B ps v s2 prev0 = some (e, kU, kp, na)) : e ≤ 1 := by
  unfold contrFind at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · exact absurd h (by simp)

/-- `if b then X else none` が `some` なら条件は真（巨大項に `simp` を当てずに
条件だけ取り出す。`split at` は識別子の `simp` で燃え尽きる）。 -/
theorem cond_of_ite_some {α : Type} {b : Bool} {X : Option α} {w : α}
    (h : (if b = true then X else none) = some w) : b = true := by
  cases b
  · rw [if_neg (by simp)] at h; simp at h
  · rfl

/-- `if b then X else some u` が `some w` なら、どちらかの枝が当たっている。 -/
theorem ite_some_pair {α : Type} {b : Bool} {X : Option α} {u w : α}
    (h : (if b = true then X else some u) = some w) : X = some w ∨ u = w := by
  cases b
  · rw [if_neg (by simp)] at h; exact Or.inr (Option.some.inj h)
  · rw [if_pos rfl] at h; exact Or.inl h

/-- `if b then some u else none` が `some w` なら `u = w`。 -/
theorem ite_some_none {α : Type} {b : Bool} {u w : α}
    (h : (if b = true then some u else none) = some w) : u = w := by
  cases b
  · rw [if_neg (by simp)] at h; simp at h
  · rw [if_pos rfl] at h; exact Option.some.inj h

/-- **縮約の残余の開始深さ `rd` の両側。**

`d + 1 + e` の枝は `e ≤ 1`（`contrFind_e_le`）と `d + 2 ≤ n` から出る。
`dmapAt` の枝は `dmapAt_bounds` に落ちる: 範囲外が「ちょうど 1 個だけ外」なら
`dmap.last + 1 = n` でぴったり `n` に届き、範囲内だけが仮定で残る。 -/
theorem rd_bounds {d e k n : ℕ} {dm : List ℕ} {c : Prop} [Decidable c]
    (he : e ≤ 1) (hn2 : d + 2 ≤ n) (hne : dm ≠ []) (hlast : dm.getLastD 0 + 1 = n)
    (hk : ¬ c → k ≤ dm.length)
    (hin : ¬ c → k + 1 < dm.length → d ≤ dm.getD k 0 ∧ dm.getD k 0 ≤ n) :
    d ≤ (if c then d + 1 + e else dmapAt dm k)
      ∧ (if c then d + 1 + e else dmapAt dm k) ≤ n := by
  by_cases h : c
  · rw [if_pos h]; omega
  · rw [if_neg h]
    exact dmapAt_bounds hne hlast (by omega) (hk h) (hin h)

/-- **縮約の枝の 5 重連結**。局所値を全部変数にしてあるので、呼び出し側では
巨大項に触らずに済む（`conv3` の本体で組み立てようとすると `whnf` が燃える）。 -/
theorem blk_contr {d dd2 nc' : ℕ} {st st1 stA stU stR stB : St}
    {cols A1 U1 R1 B1 : TrioSeq}
    (hddd : d + 1 ≤ dd2) (hst1 : dd2 + 1 ≤ st1.ST.length) (hst1ne : st1.dmap ≠ [])
    (hcols : BlkOK d st (cols, st1))
    (hA : BlkOK (dd2 + 1) st1 (A1, stA))
    (hU : d + 1 ≤ stA.ST.length → DmOK stA → BlkOK (d + 1) stA (U1, stU))
    (hR : d + 2 ≤ stU.ST.length → stU.dmap ≠ [] → DmOK stU →
      BlkOK d stU (R1, stR))
    (hB : d ≤ stR.ST.length → DmOK stR → BlkOK d stR (B1, stB)) :
    BlkOK d st (cols ++ A1 ++ U1 ++ R1 ++ B1, { stB with nc := nc' }) := by
  have hA2 : d + 2 ≤ stA.ST.length := BlkOK_ST_ge (k := d + 2) hA (by omega) (by omega)
  have hUok : BlkOK (d + 1) stA (U1, stU) := hU (by omega) hA.2.2.2.2.2.2.2
  have hU2 : d + 2 ≤ stU.ST.length := BlkOK_ST_ge (k := d + 2) hUok (by omega) (by omega)
  have hRok := hR hU2 (hUok.2.2.2.2.2.2.1 (hA.2.2.2.2.2.2.1 hst1ne)) hUok.2.2.2.2.2.2.2
  have hRlen : d ≤ stR.ST.length := hRok.2.1
  have hBok := hB (by omega) hRok.2.2.2.2.2.2.2
  exact BlkOK_app (le_refl d)
    (BlkOK_app (le_refl d)
      (BlkOK_app (Nat.le_succ d) (BlkOK_app (by omega) hcols hA) hUok) hRok) hBok

/-! ### 課題 L23: 「ブロックの全柱は先頭の柱の深さ以上」（`BlkLo`）

課題 R1 の構造的な理由をそのまま不変量にしたもの。`steps1`（BMS の隣接条件）と
合わせると、`conv3` の 4 つの再帰の先頭の深さが**等号**で決まる:

    A = r.takeWhile (p.1 < ·)   ⟹  A.head.1 = p.1 + 1
    B = r.dropWhile (p.1 < ·)   ⟹  B.head.1 = p.1
    U = B.take kU               ⟹  U.head.1 = p.1
    Bq                          ⟹  Bq.head.1 = p.1

実測（課題 R1、`gen3 <=7` 全数 ＋ 展開閉包・最長 24 列）: 上の 4 本とも違反 0
（`cA` 304386/304386 と 364983/364983、`cU` 1264/1264、`cB` 148533/148533 ほか）。
**`≤` ではなく `=`** なので、`Dm10_of_child` の隙間の処理が消える。 -/

/-- ブロックの全柱は先頭の柱の深さ以上。 -/
def BlkLo (M : TrioSeq) : Prop := ∀ c ∈ M, (M.headI).1 ≤ c.1

@[simp] theorem blkLo_nil : BlkLo [] := by intro c hc; simp at hc

/-- `takeWhile` の先頭はもとの先頭。 -/
theorem headI_takeWhile {f : Col → Bool} {l : TrioSeq} (h : l.takeWhile f ≠ []) :
    (l.takeWhile f).headI = l.headI := by
  cases l with
  | nil => simp at h
  | cons a t =>
      rw [List.takeWhile_cons] at h ⊢
      by_cases hf : f a = true
      · rw [if_pos hf]; rfl
      · rw [if_neg hf] at h; simp at h

/-- `takeWhile` が空でなければ述語は先頭で真。 -/
theorem takeWhile_head_true {f : Col → Bool} {l : TrioSeq}
    (h : l.takeWhile f ≠ []) : f l.headI = true := by
  cases l with
  | nil => simp at h
  | cons a t =>
      rw [List.takeWhile_cons] at h
      by_cases hf : f a = true
      · exact hf
      · rw [if_neg hf] at h; simp at h

/-- **`A = r.takeWhile (p.1 < ·)` の先頭は `p.1 + 1`**（`steps1` から）。 -/
theorem takeWhile_head_eq {p : Col} {r : TrioSeq}
    (hs : steps1 (p :: r)) (h : r.takeWhile (fun q => decide (p.1 < q.1)) ≠ []) :
    ((r.takeWhile (fun q => decide (p.1 < q.1))).headI).1 = p.1 + 1 := by
  have hne : r ≠ [] := by
    intro hc; rw [hc] at h; simp at h
  have h1 : p.1 < r.headI.1 := by
    have := takeWhile_head_true h
    simpa using this
  have h2 : r.headI.1 ≤ p.1 + 1 := by
    cases r with
    | nil => exact absurd rfl hne
    | cons q t => exact (steps1_cons_cons.mp hs).1
  rw [headI_takeWhile h]
  omega

/-- `headI` は `headD (0,0,0)`。 -/
theorem headI_eq_headD (l : TrioSeq) : l.headI = l.headD (0, 0, 0) := by
  cases l <;> rfl

/-- **`A` の全柱は `A` の先頭以上**。 -/
theorem takeWhile_blkLo {p : Col} {r : TrioSeq}
    (hs : steps1 (p :: r)) : BlkLo (r.takeWhile (fun q => decide (p.1 < q.1))) := by
  intro c hc
  by_cases h : r.takeWhile (fun q => decide (p.1 < q.1)) = []
  · rw [h] at hc; simp at hc
  · rw [takeWhile_head_eq hs h]
    have := List.mem_takeWhile_imp hc
    simpa using this

/-- 空でないリストの `headD` はそのリストの元。 -/
theorem headD_memT {l : TrioSeq} (h : l ≠ []) (x : Col) : l.headD x ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => simp

/-- `dropWhile` の直後の柱は述語を満たさない。`B = r.dropWhile (p.1 < ·)` の
先頭が `p.1` 以下であること（課題 L16 の側条件 b2）はこれから出る。 -/
theorem dropWhile_headD_false {f : Col → Bool} : ∀ (l : TrioSeq) (x : Col),
    l.dropWhile f ≠ [] → f ((l.dropWhile f).headD x) = false := by
  intro l
  induction l with
  | nil => intro x h; simp at h
  | cons a t ih =>
      intro x h
      rw [List.dropWhile_cons] at h ⊢
      by_cases hf : f a = true
      · rw [if_pos hf] at h ⊢
        exact ih x h
      · rw [if_neg hf] at h ⊢
        simp only [List.headD_cons]
        exact Bool.eq_false_iff.mpr hf

/-- **側条件 b2 は証明できる**: `B = r.dropWhile (p.1 < ·)` の先頭は `p.1` 以下。 -/
theorem dropWhile_headD_le {r : TrioSeq} {a : ℕ} {x : Col}
    (h : (r.dropWhile (fun q => decide (a < q.1))) ≠ []) :
    ((r.dropWhile (fun q => decide (a < q.1))).headD x).1 ≤ a := by
  have := dropWhile_headD_false (f := fun q => decide (a < q.1)) r x h
  simp only [decide_eq_false_iff_not, Nat.not_lt] at this
  exact this

/-- **`B = r.dropWhile (p.1 < ·)` の先頭は `p.1`**（`BlkLo` から下から挟む）。 -/
theorem dropWhile_head_eq {p : Col} {r : TrioSeq} (hlo : BlkLo (p :: r))
    (h : r.dropWhile (fun q => decide (p.1 < q.1)) ≠ []) :
    ((r.dropWhile (fun q => decide (p.1 < q.1))).headI).1 = p.1 := by
  have hle := dropWhile_headD_le (r := r) (a := p.1) (x := (0, 0, 0)) h
  have hmem : (r.dropWhile (fun q => decide (p.1 < q.1))).headI ∈ p :: r := by
    rw [headI_eq_headD]
    exact List.mem_cons_of_mem _
      ((List.dropWhile_sublist _).mem (headD_memT h (0, 0, 0)))
  have hge : p.1 ≤ ((r.dropWhile (fun q => decide (p.1 < q.1))).headI).1 := by
    have h9 := hlo _ hmem
    simpa using h9
  rw [headI_eq_headD]
  rw [headI_eq_headD] at hge
  omega

/-- **`B` の全柱は `B` の先頭以上**。 -/
theorem dropWhile_blkLo {p : Col} {r : TrioSeq} (hlo : BlkLo (p :: r)) :
    BlkLo (r.dropWhile (fun q => decide (p.1 < q.1))) := by
  intro c hc
  have h : r.dropWhile (fun q => decide (p.1 < q.1)) ≠ [] := by
    intro hn; rw [hn] at hc; simp at hc
  rw [dropWhile_head_eq hlo h]
  have hmem : c ∈ p :: r :=
    List.mem_cons_of_mem _ ((List.dropWhile_sublist _).mem hc)
  have h9 := hlo _ hmem
  simpa using h9

/-- **`take` は `BlkLo` を保つ**（`U = B.take kU`）。 -/
theorem blkLo_take {l : TrioSeq} (h : BlkLo l) (k : ℕ) : BlkLo (l.take k) := by
  intro c hc
  have hne : l.take k ≠ [] := by intro hn; rw [hn] at hc; simp at hc
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hne
    · exact hk
  have hhd : (l.take k).headI = l.headI := by
    cases l with
    | nil => simp at hne
    | cons a t =>
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [List.take_succ_cons]; rfl
  rw [hhd]
  exact h c ((List.take_sublist k l).mem hc)

/-- `deepGe a rs` の中の柱は行 0 が `a` 以上（`deepGe` の定義そのもの）。 -/
theorem deepGe_take_ge {a : ℕ} : ∀ (rs : TrioSeq), ∀ x ∈ rs.take (deepGe a rs),
    a ≤ x.1
  | [], x, hx => by simp [deepGe] at hx
  | (q :: r), x, hx => by
      rw [deepGe] at hx
      split at hx
      · rename_i hq
        rw [List.take_succ_cons] at hx
        rcases List.mem_cons.mp hx with rfl | hm
        · exact hq
        · exact deepGe_take_ge r x hm
      · simp at hx

/-- **`convResid` が切り出す木は `BlkLo`**。 -/
theorem blkLo_take_deepGe {c : Col} {rs : TrioSeq} :
    BlkLo ((c :: rs).take (1 + deepGe c.1 rs)) := by
  have hrw : (c :: rs).take (1 + deepGe c.1 rs) = c :: rs.take (deepGe c.1 rs) := by
    rw [Nat.add_comm 1 (deepGe c.1 rs), List.take_succ_cons]
  intro x hx
  rw [hrw] at hx ⊢
  simp only [List.headI]
  rcases List.mem_cons.mp hx with rfl | hm
  · exact le_rfl
  · exact deepGe_take_ge rs x hm

/-- 全柱が `a` 以上で先頭が `a` 以下なら、**先頭はちょうど `a`**。 -/
theorem head_eq_of_le_of_ge {L : TrioSeq} {a : ℕ} {x : Col}
    (hall : ∀ c ∈ L, a ≤ c.1) (hne : L ≠ []) (hle : (L.headD x).1 ≤ a) :
    (L.headD x).1 = a := by
  have := hall _ (headD_memT hne x)
  omega

/-- 全柱が `a` 以上で先頭が `a` 以下なら `BlkLo`（`Bq` に使う）。 -/
theorem blkLo_of_le {L : TrioSeq} {a : ℕ} (hall : ∀ c ∈ L, a ≤ c.1)
    (hhd : L ≠ [] → (L.headI).1 ≤ a) : BlkLo L := by
  intro c hc
  have hne : L ≠ [] := by intro h; rw [h] at hc; simp at hc
  exact le_trans (hhd hne) (hall c hc)

/-- `deepGe a rs` の直後の柱は行 0 が `a` 未満（`deepGe` の定義そのもの）。 -/
theorem deepGe_head_lt {a : ℕ} : ∀ (rs : TrioSeq) (x : Col),
    rs.drop (deepGe a rs) ≠ [] → ((rs.drop (deepGe a rs)).headD x).1 < a
  | [], _, h => by simp [deepGe] at h
  | q :: r, x, h => by
      rw [deepGe] at h ⊢
      split at h
      · rename_i hq
        rw [if_pos hq, List.drop_succ_cons] at *
        exact deepGe_head_lt r x h
      · rename_i hq
        rw [if_neg hq, List.drop_zero, List.headD_cons]
        omega

set_option maxHeartbeats 1000000 in
/-- **★ `convResid` は外側の `d` の block である**（課題 R1 §3 / R2）。

`convResid` は残余を**森**として読み、次の木の開始深さは
`rd - (c.1 - tail[0].1)` と**必ず下がる**（`tail[0]` は `deepGe` の定義から
`c` より浅い）。だから `BlkOK rd` は偽である（課題 L13 の `ResidBlkT`、
`<=8` 列に反例）。しかし側条件

    (H)  ∀ c' ∈ rest, d + rest.head.1 ≤ rd + c'.1

があれば、`c' := rest.head` から `d ≤ rd` が出て切り詰めが死に、(H) は
再帰でそのまま保たれるので、**外側の `d`** については block になる。
`convResid` は `conv3 head` を `|head| ≤ |rest|` で呼ぶので、
`conv3` の強い帰納の仮定 `IH` がそのまま使える。 -/
theorem resid_blk {NN d : ℕ}
    (IH : ∀ (M' : TrioSeq), M'.length ≤ NN → steps1 M' → BlkLo M' → ∀ (d' : ℕ)
        (L' : List Lent) (F' : List Bool) (ps' pw' : ℕ × ℕ) (f1 f2 : Bool)
        (st' : St) (nx' : Option Col) (off' : ℕ), d' ≤ st'.ST.length → DmOK st' →
        BlkOK d' st' (conv3 M' d' L' F' ps' pw' f1 f2 st' nx' off')) :
    ∀ (n : ℕ) (rest : TrioSeq), rest.length ≤ n → rest.length ≤ NN → steps1 rest →
      ∀ (rd : ℕ) (Lr : List Lent) (ps pw : ℕ × ℕ) (st : St) (nx : Option Col)
        (off : ℕ), d ≤ st.ST.length → rd ≤ st.ST.length → DmOK st →
        (∀ c ∈ rest, d + (rest.headD (0, 0, 0)).1 ≤ rd + c.1) →
        BlkOK d st (convResid rest rd Lr ps pw st nx off) := by
  intro n
  induction n with
  | zero =>
      intro rest hn _ _ rd Lr ps pw st nx off hd _ hdm _
      have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      rw [convResid.eq_def]
      exact BlkOK_nil hd hdm
  | succ n ih =>
      intro rest hn hNN hs1 rd Lr ps pw st nx off hd hrd hdm hH
      cases rest with
      | nil => rw [convResid.eq_def]; exact BlkOK_nil hd hdm
      | cons c rs =>
          simp only [List.length_cons] at hn hNN
          have hdrd : d ≤ rd := by
            have h := hH c (by simp)
            simp only [List.headD_cons] at h
            omega
          have hlen : ((c :: rs).take (1 + deepGe c.1 rs)).length ≤ NN := by
            simp only [List.length_take, List.length_cons]
            omega
          have hrh0 := IH ((c :: rs).take (1 + deepGe c.1 rs)) hlen
            (steps1_takeT hs1 _) blkLo_take_deepGe rd Lr
            (List.replicate 12 false) ps pw false false st
            (match (c :: rs).drop (1 + deepGe c.1 rs) with
             | t :: _ => some t | [] => nx) off hrd hdm
          rw [convResid.eq_def]
          dsimp only
          split
          · exact BlkOK_mono hdrd hrh0
          · rename_i hne
            refine BlkOK_app (le_refl d) (BlkOK_mono hdrd hrh0)
              (ih _ ?_ ?_ (steps1_dropT hs1 _) _ _ _ _ _ _ _ ?_ ?_
                hrh0.2.2.2.2.2.2.2 ?_)
            · simp only [List.length_drop, List.length_cons]; omega
            · simp only [List.length_drop, List.length_cons]; omega
            · have := hrh0.2.1; omega
            · have := hrh0.2.1; omega
            · intro c' hc'
              have hnn : (c :: rs).drop (1 + deepGe c.1 rs) ≠ [] := by
                intro hc; rw [hc] at hne; simp at hne
              have hdr : (c :: rs).drop (1 + deepGe c.1 rs)
                  = rs.drop (deepGe c.1 rs) := by
                rw [Nat.add_comm, List.drop_succ_cons]
              have hlt : (((c :: rs).drop (1 + deepGe c.1 rs)).headD
                  ((0, 0, 0) : Col)).1 < c.1 := by
                rw [hdr]
                exact deepGe_head_lt rs (0, 0, 0) (by rw [← hdr]; exact hnn)
              have h1 : c' ∈ c :: rs := List.mem_of_mem_drop hc'
              have h2 := hH c' h1
              have h3 := hH _ (List.mem_of_mem_drop (headD_memT hnn (0, 0, 0)))
              simp only [List.headD_cons] at h2 h3
              omega

set_option maxHeartbeats 2000000 in
/-- **`BlkInv` の帰納の 1 歩**（課題 L13 / L15）。

`hres`（`convResid` が外側の `d` の block）は **`resid_blk` で証明ずみ**なので
仮定ではなく、`blkInv_aux` が強い帰納の中で渡す。残る仮定は 2 本:

* `hside` … 呼び出し点で側条件 (H) が出ること（R1-NOTES §3 / R2-3。
  補題 A ＋ 節 10 から出るはず）。
* `hdmin` … `dmapAt` の枝の**範囲内**の場合（R1-NOTES 節 10 ＋ 節 11 から
  出るはず）。⚠ 課題 L13 の「`k+1 < |dmap|` は空虚」は**誤り**で、
  9 列で 3 例・10 列で 39 例踏まれる。 -/
theorem blk_step (p : Col) (r : TrioSeq) (d : ℕ) (L : List Lent) (F : List Bool)
    (ps pw : ℕ × ℕ) (first force : Bool) (st : St) (nx : Option Col) (off : ℕ)
    (hd : d ≤ st.ST.length) (hst1s : steps1 (p :: r)) (hblo : BlkLo (p :: r))
    (IH : ∀ (M' : TrioSeq), M'.length ≤ r.length → steps1 M' → BlkLo M' → ∀ (d' : ℕ)
        (L' : List Lent) (F' : List Bool) (ps' pw' : ℕ × ℕ) (f1 f2 : Bool)
        (st' : St) (nx' : Option Col) (off' : ℕ), d' ≤ st'.ST.length → DmOK st' →
        BlkOK d' st' (conv3 M' d' L' F' ps' pw' f1 f2 st' nx' off'))
    (hres : ∀ (rest : TrioSeq), rest.length ≤ r.length → steps1 rest → ∀ (rd : ℕ)
        (Lr : List Lent) (ps' pw' : ℕ × ℕ) (st' : St) (nx' : Option Col)
        (off' : ℕ), d ≤ st'.ST.length → rd ≤ st'.ST.length → DmOK st' →
        (∀ c ∈ rest, d + (rest.headD (0, 0, 0)).1 ≤ rd + c.1) →
        BlkOK d st' (convResid rest rd Lr ps' pw' st' nx' off'))
    (hside : ∀ (stU : St) (rest2 : TrioSeq) (e : ℕ), ∀ c ∈ rest2,
        d + (rest2.headD (0, 0, 0)).1
          ≤ (if rest2 = [] ∨ (rest2.headD (0, 0, 0)).1 = p.1 + 1 then d + 1 + e
             else dmapAt stU.dmap ((rest2.headD (0, 0, 0)).1 - 1)) + c.1)
    (hdmin : ∀ (stU : St) (rest2 : TrioSeq),
        ¬(rest2 = [] ∨ (rest2.headD (0, 0, 0)).1 = p.1 + 1) →
        ((rest2.headD (0, 0, 0)).1 - 1 ≤ stU.dmap.length ∧
          ((rest2.headD (0, 0, 0)).1 - 1 + 1 < stU.dmap.length →
            d ≤ stU.dmap.getD ((rest2.headD (0, 0, 0)).1 - 1) 0 ∧
              stU.dmap.getD ((rest2.headD (0, 0, 0)).1 - 1) 0 ≤ stU.ST.length))) :
    BlkOK d st (conv3 (p :: r) d L F ps pw first force st nx off) := by
  have hA : (r.takeWhile (fun q => decide (p.1 < q.1))).length ≤ r.length :=
    (List.takeWhile_sublist _).length_le
  have hB : (r.dropWhile (fun q => decide (p.1 < q.1))).length ≤ r.length :=
    List.length_dropWhile_le _ r
  have hr1 : steps1 r := steps1_tailT hst1s
  rw [conv3.eq_def]
  dsimp only
  split
  · rename_i ee kUv kpv nav he
    have hlad0 := cond_of_ite_some he
    rw [if_pos hlad0] at he
    split at he
    · simp at he
    · rename_i e kU kp na hcf
      have hw : ((e, kU, kp, na) : ℕ × ℕ × ℕ × Col) = (ee, kUv, kpv, nav) := by
        rcases ite_some_pair he with h | h
        · exact ite_some_none h
        · exact h
      have hee : ee ≤ 1 := by
        have h1 : e = ee := congrArg (fun t => t.1) hw
        have h2 := contrFind_e_le hcf
        omega
      refine blk_contr (depths_le_lad0 hlad0 rfl rfl rfl)
          (len_take_app (depths_le hd rfl rfl rfl rfl rfl).2 _).ge (by simp)
          (cols_blk hd rfl rfl rfl rfl rfl rfl rfl (by simp) (getLastD_snoc _ _ _))
          (IH _ hA ?_ ?_ _ _ _ _ _ _ _ _ _ _ ?_ ?_)
          (fun h1 h2 => IH _ ?_ ?_ ?_ _ _ _ _ _ _ _ _ _ _ h1 h2)
          (fun h2 h3 h4 => hres _ ?_ ?_ _ _ _ _ _ _ _ (by omega)
            (rd_bounds hee h2 h3 (h4 h3)
              (fun hc => (hdmin _ _ hc).1) (fun hc => (hdmin _ _ hc).2)).2
            h4 (fun c hc => hside _ _ _ c hc))
          (fun h1 h2 => IH _ ?_ ?_ ?_ _ _ _ _ _ _ _ _ _ _ h1 h2)
      · exact steps1_takeWhileT hr1 _
      · exact takeWhile_blkLo hst1s
      · exact (len_take_app (depths_le hd rfl rfl rfl rfl rfl).2 _).ge
      · intro _
        rw [getLastD_snoc, len_take_app (depths_le hd rfl rfl rfl rfl rfl).2 _]
      · simp only [List.length_take]; omega
      ·
        repeat' first
          | exact hr1
          | apply steps1_takeT
          | apply steps1_dropT
          | apply steps1_takeWhileT
          | apply steps1_dropWhileT
          | apply steps1_tailT
      · exact blkLo_take (dropWhile_blkLo hblo) _
      · simp only [List.length_drop, List.length_take, List.length_tail]; omega
      ·
        repeat' first
          | exact hr1
          | apply steps1_takeT
          | apply steps1_dropT
          | apply steps1_takeWhileT
          | apply steps1_dropWhileT
          | apply steps1_tailT
      · simp only [List.length_drop, List.length_tail]; omega
      ·
        repeat' first
          | exact hr1
          | apply steps1_takeT
          | apply steps1_dropT
          | apply steps1_takeWhileT
          | apply steps1_dropWhileT
          | apply steps1_tailT
      · refine blkLo_of_le (a := p.1) (fun c hc => ?_) (fun hne => ?_)
        · exact hblo c (List.mem_cons_of_mem _ (by
            first
              | exact ((List.drop_sublist _ _).trans
                  ((List.tail_sublist _).trans
                    ((List.drop_sublist _ _).trans (List.dropWhile_sublist _)))).mem hc
              | exact ((List.take_sublist _ _).trans (List.dropWhile_sublist _)).mem hc
              | exact (List.dropWhile_sublist _).mem hc))
        · rw [headI_eq_headD]
          have h8 := deepGe_head_lt _ (0, 0, 0) hne
          have hq := contrFind_q_eq hcf
          have hk : kU = kUv := congrArg (fun t => t.2.1) hw
          rw [hk] at hq
          omega
  · refine BlkOK_app (le_refl d)
      (BlkOK_app ?_
        (cols_blk hd rfl rfl rfl rfl rfl rfl rfl (by simp) (getLastD_snoc _ _ _))
        (IH _ hA ?_ ?_ _ _ _ _ _ _ _ _ _ _ ?_ ?_)) (IH _ hB ?_ ?_ _ _ _ _ _ _ _ _ _ _ ?_ ?_)
    · exact Nat.le_succ_of_le (depths_le hd rfl rfl rfl rfl rfl).1
    · exact steps1_takeWhileT hr1 _
    · exact takeWhile_blkLo hst1s
    · exact (len_take_app (depths_le hd rfl rfl rfl rfl rfl).2 _).ge
    · intro _
      rw [getLastD_snoc, len_take_app (depths_le hd rfl rfl rfl rfl rfl).2 _]
    · exact steps1_dropWhileT hr1 _
    · exact dropWhile_blkLo hblo
    · exact le_trans (Nat.le_succ_of_le (depths_le hd rfl rfl rfl rfl rfl).1)
        (IH _ hA (steps1_takeWhileT hr1 _) (takeWhile_blkLo hst1s) _ _ _ _ _ _ _ _ _ _
          (len_take_app (depths_le hd rfl rfl rfl rfl rfl).2 _).ge
          (by intro _
              rw [getLastD_snoc,
                len_take_app (depths_le hd rfl rfl rfl rfl rfl).2 _])).2.1
    · exact (IH _ hA (steps1_takeWhileT hr1 _) (takeWhile_blkLo hst1s) _ _ _ _ _ _ _ _ _ _
        (len_take_app (depths_le hd rfl rfl rfl rfl rfl).2 _).ge
        (by intro _
            rw [getLastD_snoc,
              len_take_app (depths_le hd rfl rfl rfl rfl rfl).2 _])).2.2.2.2.2.2.2

/-! ### 課題 L40: `dmap` の下位保存 `DmKeep`（`Dm12` の強い版）

`Dm12`（節 12）は `k < res.2.dmap.length` を**仮定**に置いた含意だった（課題 R1 の
反例のため）。ところが `Dm12_app` はそのせいで中間状態の長さ `m ≤ |stm.dmap|` を
要求し、**鎖がつながらない**。

`k < res.2.dmap.length` を**結論**に移すと（下の `DmKeep`）、

* 課題 R1 の反例（`k=4`, `|st.dmap|=4`, `|res.dmap|=5`）は**仮定 `k < |st.dmap|` を
  満たさない**ので反例にならない。
* 連結 `DmKeep_trans` は**長さの条件をまったく要らない**。

⟹ **課題 L40 で R1 に頼んだ測定 (L)（`p.1 ≤ |st.dmap| + 1`）は不要になった。**

証明が短いのは **`conv3` 全体で `dmap` を書く場所が 1 か所しかない**から
（`st1.dmap = st.dmap.take p.1 ++ [dd2]`)。`convResid` は `dmap` を直に触らない。
ブロックの下界 `m` を「先頭の行」ではなく**パラメータ**にすると、再帰呼び出しは
すべて同じ `m` で回るので、`steps1` も `BlkLo` も要らない。 -/

/-- **`dmap` の下位保存**: 入口で範囲内だった `m` 未満の添字は、値も範囲内であることも
変わらない。 -/
def DmKeep (m : ℕ) (st st' : St) : Prop :=
  ∀ k, k < m → k < st.dmap.length →
    k < st'.dmap.length ∧ st'.dmap.getD k 0 = st.dmap.getD k 0

theorem DmKeep_refl {m : ℕ} {st : St} : DmKeep m st st :=
  fun _ _ hk => ⟨hk, rfl⟩

/-- **連結**。`Dm12_app` と違い**長さの仮定が要らない**のが要点。 -/
theorem DmKeep_trans {m : ℕ} {a b c : St} (h1 : DmKeep m a b) (h2 : DmKeep m b c) :
    DmKeep m a c := by
  intro k hk hlen
  obtain ⟨h3, h4⟩ := h1 k hk hlen
  obtain ⟨h5, h6⟩ := h2 k hk h3
  exact ⟨h5, by rw [h6, h4]⟩

/-- **1 列ぶんの状態の更新**（`conv3` で `dmap` を書く唯一の場所）。 -/
theorem DmKeep_take {m j : ℕ} {st st1 : St}
    (hst1 : ∃ dd2, st1.dmap = st.dmap.take j ++ [dd2]) (hj : m ≤ j) : DmKeep m st st1 := by
  obtain ⟨dd2, hst1⟩ := hst1
  intro k hk hlen
  have hlt : k < (st.dmap.take j).length := by rw [List.length_take]; omega
  refine ⟨by rw [hst1, List.length_append]; omega, ?_⟩
  rw [hst1, getD_snoc_lt hlt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  first
    | rw [List.getElem?_take (by omega)]
    | rw [List.getElem?_take_of_lt (by omega)]
    | simp [List.getElem?_take, show k < j by omega]

/-- `DmKeep` は `Dm12`（節 12）を含む。 -/
theorem Dm12_of_DmKeep {m : ℕ} {st : St} {res : TrioSeq × St}
    (h : DmKeep m st res.2) : Dm12 m st res :=
  fun k hk _ hk0 => (h k hk hk0).2

theorem mem_le_of_sublist {m : ℕ} {X Y : TrioSeq} (hX : X.Sublist Y)
    (h : ∀ c ∈ Y, m ≤ c.1) : ∀ c ∈ X, m ≤ c.1 := fun c hc => h c (hX.mem hc)

/-- 部分列を作る道具。`A` / `B` / `U` / `rest2` / `Bq` はすべて `r` の部分列。 -/
syntax "subl_tac" : tactic
macro_rules
  | `(tactic| subl_tac) =>
    `(tactic|
      repeat' first
        | exact List.Sublist.refl _
        | exact List.takeWhile_sublist _
        | exact List.dropWhile_sublist _
        | refine (List.take_sublist _ _).trans ?_
        | refine (List.drop_sublist _ _).trans ?_
        | refine (List.tail_sublist _).trans ?_)

/-- **`conv3` の 1 列ぶんの `DmKeep`**。縮約の枝も縮約でない枝も、
状態の鎖 `st → st1 → rA.2 → (rU.2 → rR.2 →) rB.2` を `DmKeep_trans` でつなぐだけ。 -/
theorem dmKeep_step (p : Col) (r : TrioSeq) (m d : ℕ) (L : List Lent) (F : List Bool)
    (ps pw : ℕ × ℕ) (first force : Bool) (st : St) (nx : Option Col) (off : ℕ)
    (hm : ∀ c ∈ p :: r, m ≤ c.1)
    (IH : ∀ (M' : TrioSeq), M'.length ≤ r.length → (∀ c ∈ M', m ≤ c.1) →
        ∀ (d' : ℕ) (L' : List Lent) (F' : List Bool) (ps' pw' : ℕ × ℕ) (f1 f2 : Bool)
          (st' : St) (nx' : Option Col) (off' : ℕ),
          DmKeep m st' (conv3 M' d' L' F' ps' pw' f1 f2 st' nx' off').2)
    (hres : ∀ (rest : TrioSeq), rest.length ≤ r.length → (∀ c ∈ rest, m ≤ c.1) →
        ∀ (rd : ℕ) (Lr : List Lent) (ps' pw' : ℕ × ℕ) (st' : St) (nx' : Option Col)
          (off' : ℕ), DmKeep m st' (convResid rest rd Lr ps' pw' st' nx' off').2) :
    DmKeep m st (conv3 (p :: r) d L F ps pw first force st nx off).2 := by
  have hmp : m ≤ p.1 := hm p (by simp)
  have hmr : ∀ c ∈ r, m ≤ c.1 := fun c hc => hm c (List.mem_cons_of_mem _ hc)
  rw [conv3.eq_def]
  dsimp only
  split
  · -- 縮約の枝: st → st1 → rA.2 → rU.2 → rR.2 → rB.2
    refine DmKeep_trans (DmKeep_take (j := p.1) ?hst hmp)
      (DmKeep_trans (IH _ ?_ ?_ _ _ _ _ _ _ _ _ _ _)
        (DmKeep_trans (IH _ ?_ ?_ _ _ _ _ _ _ _ _ _ _)
          (DmKeep_trans (hres _ ?_ ?_ _ _ _ _ _ _ _)
            (IH _ ?_ ?_ _ _ _ _ _ _ _ _ _ _))))
    case hst => exact ⟨_, rfl⟩
    all_goals
      first
        | exact List.Sublist.length_le (by subl_tac)
        | exact mem_le_of_sublist (by subl_tac) hmr
  · -- 縮約でない枝: st → st1 → rA.2 → rB.2
    refine DmKeep_trans (DmKeep_take (j := p.1) ?hst hmp)
      (DmKeep_trans (IH _ ?_ ?_ _ _ _ _ _ _ _ _ _ _)
        (IH _ ?_ ?_ _ _ _ _ _ _ _ _ _ _))
    case hst => exact ⟨_, rfl⟩
    all_goals
      first
        | exact List.Sublist.length_le (by subl_tac)
        | exact mem_le_of_sublist (by subl_tac) hmr

/-- **`convResid` の `DmKeep`**。`convResid` は `dmap` を直に触らず、
`conv3` を部分列に呼ぶだけ。 -/
theorem dmKeep_resid {NN m : ℕ}
    (IH : ∀ (M' : TrioSeq), M'.length ≤ NN → (∀ c ∈ M', m ≤ c.1) →
        ∀ (d' : ℕ) (L' : List Lent) (F' : List Bool) (ps' pw' : ℕ × ℕ) (f1 f2 : Bool)
          (st' : St) (nx' : Option Col) (off' : ℕ),
          DmKeep m st' (conv3 M' d' L' F' ps' pw' f1 f2 st' nx' off').2) :
    ∀ (n : ℕ) (rest : TrioSeq), rest.length ≤ n → rest.length ≤ NN →
      (∀ c ∈ rest, m ≤ c.1) →
      ∀ (rd : ℕ) (Lr : List Lent) (ps pw : ℕ × ℕ) (st : St) (nx : Option Col)
        (off : ℕ), DmKeep m st (convResid rest rd Lr ps pw st nx off).2 := by
  intro n
  induction n with
  | zero =>
      intro rest hn _ _ rd Lr ps pw st nx off
      have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      rw [convResid.eq_def]
      exact DmKeep_refl
  | succ n ih =>
      intro rest hn hNN hmm rd Lr ps pw st nx off
      cases rest with
      | nil => rw [convResid.eq_def]; exact DmKeep_refl
      | cons c rs =>
          simp only [List.length_cons] at hn hNN
          rw [convResid.eq_def]
          dsimp only
          split
          · exact IH _ (by simp only [List.length_take, List.length_cons]; omega)
              (mem_le_of_sublist (List.take_sublist _ _) hmm) _ _ _ _ _ _ _ _ _ _
          · refine DmKeep_trans
              (IH _ (by simp only [List.length_take, List.length_cons]; omega)
                (mem_le_of_sublist (List.take_sublist _ _) hmm) _ _ _ _ _ _ _ _ _ _)
              (ih _ ?_ ?_ (mem_le_of_sublist (List.drop_sublist _ _) hmm) _ _ _ _ _ _ _)
            · simp only [List.length_drop, List.length_cons]; omega
            · simp only [List.length_drop, List.length_cons]; omega

/-- **★ `DmKeep` は `conv3` の全呼び出しで成り立つ**（仮定ゼロ）。 -/
theorem dmKeep_aux (m : ℕ) :
    ∀ (n : ℕ) (M : TrioSeq), M.length ≤ n → (∀ c ∈ M, m ≤ c.1) → ∀ (d : ℕ)
      (L : List Lent) (F : List Bool) (ps pw : ℕ × ℕ) (first force : Bool) (st : St)
      (nx : Option Col) (off : ℕ),
      DmKeep m st (conv3 M d L F ps pw first force st nx off).2 := by
  intro n
  induction n with
  | zero =>
      intro M hM _ d L F ps pw first force st nx off
      have hnil : M = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      rw [conv3_nil]
      exact DmKeep_refl
  | succ n ih =>
      intro M hM hmm d L F ps pw first force st nx off
      cases M with
      | nil => rw [conv3_nil]; exact DmKeep_refl
      | cons p r =>
          have hr : r.length ≤ n := by simp only [List.length_cons] at hM; omega
          exact dmKeep_step p r m d L F ps pw first force st nx off hmm
            (fun M' hM' hm' => ih M' (le_trans hM' hr) hm')
            (fun rest hlen hm' => dmKeep_resid (NN := n)
              (fun M' hM'' hm'' => ih M' hM'' hm'') rest.length rest le_rfl
              (le_trans hlen hr) hm')

/-- **★ `DmKeep`（仮定ゼロ、任意の下界 `m`）**。 -/
theorem dmKeep_holds {m : ℕ} (M : TrioSeq) (hmm : ∀ c ∈ M, m ≤ c.1) (d : ℕ)
    (L : List Lent) (F : List Bool) (ps pw : ℕ × ℕ) (first force : Bool) (st : St)
    (nx : Option Col) (off : ℕ) :
    DmKeep m st (conv3 M d L F ps pw first force st nx off).2 :=
  dmKeep_aux m M.length M le_rfl hmm d L F ps pw first force st nx off

/-! ### 課題 L41: `Dm10`（節 10）を `conv3` の全呼び出しで出す

**定式化の要点**（課題 L25 で詰まっていた「空リストの場合分け」を消す形）:

    結論   Dm10 d m res.2
    仮定   ∀ c ∈ M, m ≤ c.1      … ブロックの下界
           M ≠ [] → M.headI.1 = m … 頭はちょうど m（BlkLo から）
           m ≤ |st.dmap|          … dmap は下界まで届いている
           Dm10 d m st            … 入口

`M = []` のとき `res.2 = st` なので**入口の仮定がそのまま結論**になる。
⟹ `A = []` / `B = []` / `U = []` / `Bq = []` の**場合分けが 1 つも要らない**。

伝播はすべて `DmKeep`（課題 L40）で出る:

    st1                 |st1.dmap| = m + 1              （m ≤ |st.dmap| から）
    A の呼び出し（頭 m+1、深さ dd2+1）
                        入口 Dm10 (dd2+1) (m+1) st1 は**空虚**（範囲が m+1 まで）
                        出口を Dm10_of_child' で (d, m) に付け替える
    B / U / Bq          DmKeep で長さが降り、Dm10 はそのまま渡る
-/

/-- `d ≤ dd2` は **`d ≤ |ST|` を仮定しなくても出る**（`fit` は `d` から上へ探し、
既定値 `max d |ST|` も `d` 以上だから）。これで `Dm10` の帰納は `BlkOK` と
切り離せる。 -/
theorem depths_le_lo {ST ST2 : List (ℕ × ℕ)} {d h1 e1 dd0 dd1 dd2 : ℕ}
    {lad0 lad1 : Bool}
    (hdd0 : dd0 = if lad0 then d + 1 else (fit ST d h1).getD (max d ST.length))
    (hdd1 : dd1 = if lad1 then dd0 + 1 else dd0)
    (hdd2 : dd2 = if okPlace ST2 dd1 e1 then dd1 else (fit ST2 dd1 e1).getD dd1) :
    d ≤ dd2 := by
  have h0 : d ≤ dd0 := by
    rw [hdd0]
    split
    · omega
    · cases h : fit ST d h1 with
      | none => simp [h]
      | some y =>
          rw [fit] at h
          have := fitAux_bounds h
          simp only [h, Option.getD_some]
          omega
  have h1' : dd0 ≤ dd1 := by rw [hdd1]; split <;> omega
  have h2' : dd1 ≤ dd2 := by
    rw [hdd2]; split
    · exact le_rfl
    · exact fit_getD_ge _ _
  omega

theorem getD_take_snoc {dm : List ℕ} {j x : ℕ} (hj : j ≤ dm.length) :
    (dm.take j ++ [x]).getD j 0 = x := by
  have h : (dm.take j).length = j := by rw [List.length_take]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), h]
  simp

theorem len_take_snoc {dm : List ℕ} {j x : ℕ} (hj : j ≤ dm.length) :
    (dm.take j ++ [x]).length = j + 1 := by
  simp only [List.length_append, List.length_take, List.length_singleton]
  omega

theorem dmKeep_lt {m k : ℕ} {st st' : St} (h : DmKeep m st st') (hk : k < m)
    (hkl : k < st.dmap.length) : k < st'.dmap.length := (h k hk hkl).1

theorem dmKeep_le {m : ℕ} {st st' : St} (h : DmKeep m st st')
    (hm : m ≤ st.dmap.length) : m ≤ st'.dmap.length := by
  cases m with
  | zero => omega
  | succ n => have := (h n (by omega) (by omega)).1; omega

/-- `take` の先頭はもとの先頭。 -/
theorem headI_take {l : TrioSeq} {n : ℕ} (h : l.take n ≠ []) :
    (l.take n).headI = l.headI := by
  cases l with
  | nil => simp at h
  | cons a t =>
      cases n with
      | zero => simp at h
      | succ n => rfl

/-- 範囲の外なら `Dm10` は空虚。 -/
theorem dm10_vac {d j : ℕ} {st : St} (h : st.dmap.length ≤ j) : Dm10 d j st :=
  fun _ hj hjl => absurd hjl (by omega)

/-- `convResid` の `DmKeep`（仮定ゼロ）。 -/
theorem dmKeep_resid_holds {m : ℕ} (rest : TrioSeq) (hmm : ∀ c ∈ rest, m ≤ c.1)
    (rd : ℕ) (Lr : List Lent) (ps pw : ℕ × ℕ) (st : St) (nx : Option Col) (off : ℕ) :
    DmKeep m st (convResid rest rd Lr ps pw st nx off).2 :=
  dmKeep_resid (NN := rest.length) (fun M' _ hm' => dmKeep_holds M' hm')
    rest.length rest le_rfl le_rfl hmm rd Lr ps pw st nx off

/-- `Dm10` は `dmap` しか見ないので、`nc` だけ違う状態に移せる。 -/
theorem dm10_congr {d j : ℕ} {st st' : St} (h : Dm10 d j st)
    (hd : st'.dmap = st.dmap) : Dm10 d j st' := by
  intro jj hj hjl
  rw [hd] at hjl ⊢
  exact h jj hj hjl

/-- **`Dm10` の帰納の 1 歩**（課題 L41）。 -/
theorem dm10_step (p : Col) (r : TrioSeq) (d : ℕ) (L : List Lent) (F : List Bool)
    (ps pw : ℕ × ℕ) (first force : Bool) (st : St) (nx : Option Col) (off : ℕ)
    (hs1 : steps1 (p :: r)) (hblo : BlkLo (p :: r))
    (hlen : p.1 ≤ st.dmap.length)
    (IH : ∀ (M' : TrioSeq), M'.length ≤ r.length → steps1 M' → ∀ (m' d' : ℕ),
        (∀ c ∈ M', m' ≤ c.1) → (M' ≠ [] → (M'.headI).1 = m') →
        ∀ (L' : List Lent) (F' : List Bool) (ps' pw' : ℕ × ℕ) (f1 f2 : Bool)
          (st' : St) (nx' : Option Col) (off' : ℕ),
          m' ≤ st'.dmap.length → (M' = [] → Dm10 d' m' st') →
          Dm10 d' m' (conv3 M' d' L' F' ps' pw' f1 f2 st' nx' off').2)
    (hres : ∀ (rest : TrioSeq) (rd : ℕ) (Lr : List Lent) (ps' pw' : ℕ × ℕ) (st' : St)
        (nx' : Option Col) (off' e : ℕ),
        rest.length ≤ r.length → steps1 rest →
        (∀ c ∈ rest, p.1 + 1 ≤ c.1) → p.1 ≤ st'.dmap.length → Dm10 (d + 1) p.1 st' →
        rd = (if rest = [] ∨ (rest.headD (0, 0, 0)).1 = p.1 + 1 then d + 1 + e
              else dmapAt st'.dmap ((rest.headD (0, 0, 0)).1 - 1)) →
        Dm10 d p.1 (convResid rest rd Lr ps' pw' st' nx' off').2) :
    Dm10 d p.1 (conv3 (p :: r) d L F ps pw first force st nx off).2 := by
  have hr1 : steps1 r := steps1_tailT hs1
  have hmr : ∀ c ∈ r, p.1 ≤ c.1 := by
    intro c hc
    have h9 := hblo c (List.mem_cons_of_mem _ hc)
    simpa using h9
  have hAmem : ∀ c ∈ r.takeWhile (fun q => decide (p.1 < q.1)), p.1 + 1 ≤ c.1 := by
    intro c hc
    have hne : r.takeWhile (fun q => decide (p.1 < q.1)) ≠ [] := by
      intro h; rw [h] at hc; simp at hc
    have h1 := takeWhile_blkLo hs1 c hc
    rw [takeWhile_head_eq hs1 hne] at h1
    exact h1
  have hAmem' : ∀ c ∈ r.takeWhile (fun q => decide (p.1 < q.1)), p.1 ≤ c.1 :=
    fun c hc => le_trans (Nat.le_succ _) (hAmem c hc)
  have hlen1 : ∀ x : ℕ, (st.dmap.take p.1 ++ [x]).length = p.1 + 1 :=
    fun x => len_take_snoc hlen
  rw [conv3.eq_def]
  dsimp only
  split
  · -- 縮約の枝
    rename_i ee kUv kpv nav he
    have hlad0 := cond_of_ite_some he
    rw [if_pos hlad0] at he
    split at he
    · simp at he
    · rename_i e kU kp na hcf
      have hw : ((e, kU, kp, na) : ℕ × ℕ × ℕ × Col) = (ee, kUv, kpv, nav) := by
        rcases ite_some_pair he with h | h
        · exact ite_some_none h
        · exact h
      have hk : kU = kUv := congrArg (fun t => t.2.1) hw
      refine dm10_congr (IH _ ?lQ ?sQ p.1 d ?mQ ?hQ _ _ _ _ _ _ _ _ _ ?dQ ?pQ) rfl
      case lQ => exact List.Sublist.length_le (by subl_tac)
      case sQ =>
        repeat' first
          | exact hr1
          | apply steps1_takeT
          | apply steps1_dropT
          | apply steps1_takeWhileT
          | apply steps1_dropWhileT
          | apply steps1_tailT
      case mQ => exact mem_le_of_sublist (by subl_tac) hmr
      case hQ =>
        intro hne
        rw [headI_eq_headD]
        refine head_eq_of_le_of_ge (x := (0, 0, 0)) ?_ hne ?_
        · intro c hc
          exact mem_le_of_sublist (by subl_tac) hmr c hc
        · have h8 := deepGe_head_lt _ (0, 0, 0) hne
          have hq := contrFind_q_eq hcf
          rw [hk] at hq
          omega
      case dQ =>
        exact dmKeep_le (dmKeep_resid_holds _ (mem_le_of_sublist (by subl_tac) hmr) _ _ _ _ _ _ _)
          (dmKeep_le (dmKeep_holds _ (mem_le_of_sublist (by subl_tac) hmr) _ _ _ _ _ _ _ _ _ _)
            (dmKeep_le (dmKeep_holds _ hAmem' _ _ _ _ _ _ _ _ _ _)
              (by rw [hlen1]; omega)))
      case pQ =>
        intro _
        refine hres _ _ _ _ _ _ _ _ _ ?lRs ?sRs ?mRs ?dU ?pU rfl
        case lRs => exact List.Sublist.length_le (by subl_tac)
        case sRs =>
          repeat' first
            | exact hr1
            | apply steps1_takeT
            | apply steps1_dropT
            | apply steps1_takeWhileT
            | apply steps1_dropWhileT
            | apply steps1_tailT
        case mRs =>
          intro cc hcc
          have hne2 :
              ((r.dropWhile (fun q => decide (p.1 < q.1))).drop kUv).tail ≠ [] := by
            intro hc
            rw [hc] at hcc
            simp at hcc
          have hnep : (r.dropWhile (fun q => decide (p.1 < q.1))).drop kUv ≠ [] := by
            intro hc
            rw [hc] at hne2
            simp at hne2
          have hqmem :
              (((r.dropWhile (fun q => decide (p.1 < q.1))).drop kUv).headD (0, 0, 0)) ∈ r :=
            ((List.drop_sublist _ _).trans (List.dropWhile_sublist _)).mem
              (headD_memT hnep _)
          have hq := hmr _ hqmem
          have h1 := deepGe_take_ge _ cc ((List.drop_sublist _ _).mem hcc)
          omega
        case dU =>
          exact dmKeep_le (dmKeep_holds _ (mem_le_of_sublist (by subl_tac) hmr) _ _ _ _ _ _ _ _ _ _)
            (dmKeep_le (dmKeep_holds _ hAmem' _ _ _ _ _ _ _ _ _ _) (by rw [hlen1]; omega))
        case pU =>
          refine IH _ ?lU ?sU p.1 (d + 1) ?mU ?hU
            _ _ _ _ _ _ _ _ _ ?dA ?pA
          case mU => exact mem_le_of_sublist (by subl_tac) hmr
          case lU => exact List.Sublist.length_le (by subl_tac)
          case sU =>
            repeat' first
              | exact hr1
              | apply steps1_takeT
              | apply steps1_dropT
              | apply steps1_takeWhileT
              | apply steps1_dropWhileT
              | apply steps1_tailT
          case hU =>
            intro hne
            have hne2 : r.dropWhile (fun q => decide (p.1 < q.1)) ≠ [] := by
              intro hc; rw [hc] at hne; simp at hne
            rw [headI_take hne]
            exact dropWhile_head_eq hblo hne2
          case dA =>
            exact dmKeep_le (dmKeep_holds _ hAmem' _ _ _ _ _ _ _ _ _ _)
              (by rw [hlen1]; omega)
          case pA =>
            intro _
            refine Dm10_of_child ?hdd
              (IH _ ?lA ?sA (p.1 + 1) _ hAmem ?hA _ _ _ _ _ _ _ _ _ ?dA1 ?pA1)
              (Dm12_of_DmKeep (dmKeep_holds _ hAmem _ _ _ _ _ _ _ _ _ _)) ?hv ?hl
            case hdd => exact depths_le_lad0 hlad0 rfl rfl rfl
            case lA => exact List.Sublist.length_le (by subl_tac)
            case sA => exact steps1_takeWhileT hr1 _
            case hA => exact fun h => takeWhile_head_eq hs1 h
            case dA1 => rw [hlen1]
            case pA1 => exact fun _ => dm10_vac (by rw [hlen1])
            case hv => exact getD_take_snoc hlen
            case hl => rw [hlen1]; omega
  · -- 縮約でない枝
    refine IH _ ?lB ?sB p.1 d ?mB ?hB _ _ _ _ _ _ _ _ _ ?dAn ?pAn
    case lB => exact List.length_dropWhile_le _ r
    case sB => exact steps1_dropWhileT hr1 _
    case mB => exact mem_le_of_sublist (List.dropWhile_sublist _) hmr
    case hB => exact dropWhile_head_eq hblo
    case dAn =>
      exact dmKeep_le (dmKeep_holds _ hAmem' _ _ _ _ _ _ _ _ _ _) (by rw [hlen1]; omega)
    case pAn =>
      intro _
      refine Dm10_of_child' ?hdd2
        (IH _ ?lA2 ?sA2 (p.1 + 1) _ hAmem ?hA2 _ _ _ _ _ _ _ _ _ ?dA2 ?pA2)
        (Dm12_of_DmKeep (dmKeep_holds _ hAmem _ _ _ _ _ _ _ _ _ _)) ?hv2 ?hl2
      case hdd2 => exact depths_le_lo rfl rfl rfl
      case lA2 => exact (List.takeWhile_sublist _).length_le
      case sA2 => exact steps1_takeWhileT hr1 _
      case hA2 => exact fun h => takeWhile_head_eq hs1 h
      case dA2 => rw [hlen1]
      case pA2 => exact fun _ => dm10_vac (by rw [hlen1])
      case hv2 => exact getD_take_snoc hlen
      case hl2 => rw [hlen1]; omega

/-- **`convResid` の節 10**（課題 L41）。残る債務は**頭が `dmap` の範囲に届く**
1 本（`rest ≠ [] → rest.headI.1 ≤ |st.dmap|`）だけで、これは再帰の中では
`deepGe_head_lt` ＋ `DmKeep` で伝わる（＝ **いちばん外側でしか要らない**）。 -/
theorem dm10_resid {NN : ℕ}
    (IH : ∀ (M' : TrioSeq), M'.length ≤ NN → steps1 M' → ∀ (m' d' : ℕ),
        (∀ c ∈ M', m' ≤ c.1) → (M' ≠ [] → (M'.headI).1 = m') →
        ∀ (L' : List Lent) (F' : List Bool) (ps' pw' : ℕ × ℕ) (f1 f2 : Bool)
          (st' : St) (nx' : Option Col) (off' : ℕ),
          m' ≤ st'.dmap.length → (M' = [] → Dm10 d' m' st') →
          Dm10 d' m' (conv3 M' d' L' F' ps' pw' f1 f2 st' nx' off').2) :
    ∀ (n : ℕ) (rest : TrioSeq), rest.length ≤ n → rest.length ≤ NN → steps1 rest →
      ∀ (m d rd : ℕ) (Lr : List Lent) (ps pw : ℕ × ℕ) (st : St) (nx : Option Col)
        (off : ℕ),
        (∀ c ∈ rest, m ≤ c.1) → m ≤ st.dmap.length → Dm10 d m st →
        (rest ≠ [] → (rest.headI).1 ≤ st.dmap.length) →
        (rest ≠ [] → d + (rest.headI).1 ≤ rd + m) →
        Dm10 d m (convResid rest rd Lr ps pw st nx off).2 := by
  intro n
  induction n with
  | zero =>
      intro rest hn _ _ m d rd Lr ps pw st nx off _ _ hpre _ _
      have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      rw [convResid.eq_def]
      exact hpre
  | succ n ih =>
      intro rest hn hNN hs1 m d rd Lr ps pw st nx off hmem hlen hpre hhd hdep
      cases rest with
      | nil => rw [convResid.eq_def]; exact hpre
      | cons c rs =>
          simp only [List.length_cons] at hn hNN
          have hcm : m ≤ c.1 := hmem c (by simp)
          have hc1 : c.1 ≤ st.dmap.length := by
            have h9 := hhd (by simp); simpa using h9
          have hdep1 : d + c.1 ≤ rd + m := by
            have h9 := hdep (by simp); simpa using h9
          have hhead : (c :: rs).take (1 + deepGe c.1 rs)
              = c :: rs.take (deepGe c.1 rs) := by rw [Nat.add_comm]; rfl
          have htail : (c :: rs).drop (1 + deepGe c.1 rs)
              = rs.drop (deepGe c.1 rs) := by rw [Nat.add_comm]; rfl
          have hmemH : ∀ x ∈ (c :: rs).take (1 + deepGe c.1 rs), c.1 ≤ x.1 := by
            rw [hhead]
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hm
            · exact le_rfl
            · exact deepGe_take_ge rs x hm
          have hmemH' : ∀ x ∈ (c :: rs).take (1 + deepGe c.1 rs), m ≤ x.1 :=
            fun x hx => le_trans hcm (hmemH x hx)
          have hneH : (c :: rs).take (1 + deepGe c.1 rs) ≠ [] := by rw [hhead]; simp
          have hhdH : ((c :: rs).take (1 + deepGe c.1 rs)).headI.1 = c.1 := by
            rw [hhead]; rfl
          have hlenH : ((c :: rs).take (1 + deepGe c.1 rs)).length ≤ NN := by
            simp only [List.length_take, List.length_cons]; omega
          have hsH : steps1 ((c :: rs).take (1 + deepGe c.1 rs)) := steps1_takeT hs1 _
          have hkeep : ∀ (rd' : ℕ) (Lr' : List Lent) (F' : List Bool) (ps' pw' : ℕ × ℕ)
              (f1 f2 : Bool) (nx' : Option Col) (off' : ℕ),
              DmKeep c.1 st (conv3 ((c :: rs).take (1 + deepGe c.1 rs)) rd' Lr' F'
                ps' pw' f1 f2 st nx' off').2 :=
            fun rd' Lr' F' ps' pw' f1 f2 nx' off' =>
              dmKeep_holds _ hmemH rd' Lr' F' ps' pw' f1 f2 st nx' off'
          have hkeep' : ∀ (rd' : ℕ) (Lr' : List Lent) (F' : List Bool) (ps' pw' : ℕ × ℕ)
              (f1 f2 : Bool) (nx' : Option Col) (off' : ℕ),
              m ≤ (conv3 ((c :: rs).take (1 + deepGe c.1 rs)) rd' Lr' F'
                ps' pw' f1 f2 st nx' off').2.dmap.length :=
            fun rd' Lr' F' ps' pw' f1 f2 nx' off' =>
              dmKeep_le (dmKeep_holds _ hmemH' rd' Lr' F' ps' pw' f1 f2 st nx' off') hlen
          have hrh : ∀ (nx' : Option Col), Dm10 d m
              (conv3 ((c :: rs).take (1 + deepGe c.1 rs)) rd Lr (List.replicate 12 false)
                ps pw false false st nx' off).2 := by
            intro nx'
            refine Dm10_shift hdep1
              (IH _ hlenH hsH c.1 rd hmemH (fun _ => hhdH) _ _ _ _ _ _ _ _ _ hc1
                (fun h => absurd h hneH)) ?_
            intro j hj hjc hjl
            have hk := hkeep rd Lr (List.replicate 12 false) ps pw false false nx' off
              j hjc (by omega)
            rw [hk.2]
            exact hpre j hj (by omega)
          rw [convResid.eq_def]
          dsimp only
          split
          · exact hrh _
          · rename_i hne
            have hnetail : rs.drop (deepGe c.1 rs) ≠ [] := by
              rw [← htail]
              intro hc
              rw [hc] at hne
              simp at hne
            have hlt : ((rs.drop (deepGe c.1 rs)).headD (0, 0, 0)).1 < c.1 :=
              deepGe_head_lt rs (0, 0, 0) hnetail
            have hmemT : ∀ x ∈ (c :: rs).drop (1 + deepGe c.1 rs), m ≤ x.1 :=
              fun x hx => hmem x ((List.drop_sublist _ _).mem hx)
            have hmT : m ≤ ((rs.drop (deepGe c.1 rs)).headD (0, 0, 0)).1 := by
              refine hmemT _ ?_
              rw [htail]
              exact headD_memT hnetail (0, 0, 0)
            refine ih _ ?_ ?_ ?_ m d _ _ _ _ _ _ _ ?_ (hkeep' _ _ _ _ _ _ _ _ _)
              (hrh _) ?_ ?_
            · simp only [List.length_drop, List.length_cons]; omega
            · simp only [List.length_drop, List.length_cons]; omega
            · exact steps1_dropT hs1 _
            · exact hmemT
            · intro _
              rw [headI_eq_headD, htail]
              exact le_of_lt (dmKeep_lt (hkeep _ _ _ _ _ _ _ _ _) hlt (by omega))
            · intro _
              rw [headI_eq_headD, htail]
              omega

/-- 深さは下向きに弱められる。 -/
theorem dm10_weak {d m : ℕ} {st : St} (h : Dm10 (d + 1) m st) : Dm10 d m st :=
  fun j hj hjl => le_trans (by omega) (h j hj hjl)

/-- **残余の開始深さ `rd` の下界**。`Dm10 (d+1) m st'` を添字 `h-1` で読むだけ。
`h = m + 1` の枝は `rd = d + 1 + e ≥ d + 1` から直に出る。 -/
theorem resid_rd_lb {rest : TrioSeq} {st' : St} {m d rd e : ℕ}
    (hne : rest ≠ []) (hmem : ∀ c ∈ rest, m + 1 ≤ c.1)
    (hhd : (rest.headI).1 ≤ st'.dmap.length) (hpre : Dm10 (d + 1) m st')
    (hrd : rd = if rest = [] ∨ (rest.headD (0, 0, 0)).1 = m + 1 then d + 1 + e
                else dmapAt st'.dmap ((rest.headD (0, 0, 0)).1 - 1)) :
    d + (rest.headI).1 ≤ rd + m := by
  rw [headI_eq_headD] at hhd ⊢
  have hm1 : m + 1 ≤ (rest.headD (0, 0, 0)).1 := hmem _ (headD_memT hne _)
  rw [hrd]
  by_cases hc : rest = [] ∨ (rest.headD (0, 0, 0)).1 = m + 1
  · rw [if_pos hc]
    rcases hc with h | h
    · exact absurd h hne
    · omega
  · rw [if_neg hc]
    have hne2 : (rest.headD (0, 0, 0)).1 ≠ m + 1 := fun h => hc (Or.inr h)
    have hk : (rest.headD (0, 0, 0)).1 - 1 < st'.dmap.length := by omega
    have hdm : st'.dmap ≠ [] := by
      intro h
      rw [h] at hk
      simp at hk
    have hval : dmapAt st'.dmap ((rest.headD (0, 0, 0)).1 - 1)
        = st'.dmap.getD ((rest.headD (0, 0, 0)).1 - 1) 0 := by
      rw [dmapAt, if_neg hdm, if_pos hk]
    rw [hval]
    have h9 := hpre ((rest.headD (0, 0, 0)).1 - 1) (by omega) hk
    omega

/-- **★ 残余の開始深さ `rd` の下界（弱い仮定版、課題 L46）。**

課題 L45 で `ResidHeadT` を `h ≤ |dmap|` と書いたのは **off-by-one** だった。
実測（`residhead.py`、`gen3(BMS,<=8)` の呼び出し点 2386 件）:

    |dmap| == h      2082
    |dmap| == h + 1   243
    |dmap| == h - 1    61     ← `h ≤ |dmap|` の破れ
    その他              0
    ⟹ **h ≤ |dmap| + 1 は 2386 / 2386 = 100%**

そしてこれは **R1-NOTES §4.3 の紙の証明の対象そのもの**（`h - 1 ≤ |dmap|`）で、
`DmapInT` の第 1 項の書き方とも一致する。**壊れていたのは私の `ResidHeadT` だけ。**

`h - 1 = |dmap|` の 61 件でも下界は閉じる:

    dmapAt は外挿の枝 ⟹ rd = dmap.getLastD + (h-1-|dmap|+1) = dmap.getLastD + 1
    Dm10 を**最後の添字** |dmap|-1 で読むと
      (d+1) + (|dmap|-1-m) ≤ dmap.getLastD
    ⟹ rd ≥ d + |dmap| + 1 - m = d + h - m   ✓ ぴったり

`m ≤ |dmap| - 1` は `else` の枝（`h ≠ m+1`）から `h ≥ m+2` ⟹ `|dmap| ≥ m+1` で出る。
`dmap ≠ []` も同じ不等式から出るので、**追加の仮定は要らない**。 -/
theorem resid_rd_lb' {rest : TrioSeq} {st' : St} {m d rd e : ℕ}
    (hne : rest ≠ []) (hmem : ∀ c ∈ rest, m + 1 ≤ c.1)
    (hhd : (rest.headI).1 ≤ st'.dmap.length + 1) (hpre : Dm10 (d + 1) m st')
    (hrd : rd = if rest = [] ∨ (rest.headD (0, 0, 0)).1 = m + 1 then d + 1 + e
                else dmapAt st'.dmap ((rest.headD (0, 0, 0)).1 - 1)) :
    d + (rest.headI).1 ≤ rd + m := by
  rw [headI_eq_headD] at hhd ⊢
  have hm1 : m + 1 ≤ (rest.headD (0, 0, 0)).1 := hmem _ (headD_memT hne _)
  rw [hrd]
  by_cases hc : rest = [] ∨ (rest.headD (0, 0, 0)).1 = m + 1
  · rw [if_pos hc]
    rcases hc with h | h
    · exact absurd h hne
    · omega
  · rw [if_neg hc]
    have hne2 : (rest.headD (0, 0, 0)).1 ≠ m + 1 := fun h => hc (Or.inr h)
    have hdm : st'.dmap ≠ [] := by
      intro h
      rw [h] at hhd
      simp only [List.length_nil] at hhd
      omega
    have hlen1 : 1 ≤ st'.dmap.length := by
      cases h : st'.dmap with
      | nil => exact absurd h hdm
      | cons a t => simp
    by_cases hk : (rest.headD (0, 0, 0)).1 - 1 < st'.dmap.length
    · have hval : dmapAt st'.dmap ((rest.headD (0, 0, 0)).1 - 1)
          = st'.dmap.getD ((rest.headD (0, 0, 0)).1 - 1) 0 := by
        rw [dmapAt, if_neg hdm, if_pos hk]
      rw [hval]
      have h9 := hpre ((rest.headD (0, 0, 0)).1 - 1) (by omega) hk
      omega
    · have heq : (rest.headD (0, 0, 0)).1 - 1 = st'.dmap.length := by omega
      have hval : dmapAt st'.dmap ((rest.headD (0, 0, 0)).1 - 1)
          = st'.dmap.getLastD 0 + 1 := by
        rw [dmapAt, if_neg hdm, if_neg hk, heq]
        omega
      rw [hval]
      have h9 := hpre (st'.dmap.length - 1) (by omega) (by omega)
      rw [getD_last] at h9
      omega

/-- ⚠⚠ **この形は偽である**（課題 L46）。1 だけ弱めた `h ≤ |dmap| + 1` が正しい。

実測（team-lead `residhead.py`、`ST_TS ∩ {len<=8}` の呼び出し点 2386 件）:

    h ≤ |dmap| + 1  : **2386 / 2386（100%）**   ← 正しい形
    h ≤ |dmap|      : 2325（**破れ 61**）        ← この `def`。**偽**
    h ≤ |dmap| - 1  : 243（破れ 2143）           ← 陽性対照

⟹ **陽性対照が両方鳴っているので、100% は空虚ではない。**
R1-NOTES §4.3 の紙の証明の対象は `h - 1 ≤ |dmap|`（＝ `h ≤ |dmap| + 1`）で、
`DmapInR` の第 1 項の書き方とも一致する。**壊れているのはこの `def` だけ。**

`resid_rd_lb'` は**正しい形だけで**証明ずみ（61 件も閉じる）。残るのは
`dm10_step` / `dm10_aux` / `dm10_holds` / `dm10_at_U` / `dmST_step` の
`hlen : m ≤ |st.dmap|` を **`m ≤ |st.dmap| + 1`** に一般化する作業（下の設計を見よ）。

### 一般化の設計（課題 L46 §7）

`|st1.dmap| = min p.1 |st.dmap| + 1` が **`p.1 + 1` と `p.1` の 2 通り**になる:

    p.1 ≤ |st.dmap|      … |st1.dmap| = p.1 + 1   （いまの形）
    p.1 = |st.dmap| + 1  … |st1.dmap| = p.1       （新しい場合）

**只で通るもの**（`p.1 ≤ |st1.dmap| ≤ p.1 + 1` が両方の場合で成り立つから）:

    A の呼び出しの入口   p.1 + 1 ≤ |st1.dmap| + 1        ✓
    B / U / Bq の入口    p.1 ≤ |st1.dmap|                ✓
    dm10_vac の空虚性    |st1.dmap| ≤ p.1 + 1            ✓

**要るもの**: `Dm10_of_child'` / `Dm10_of_child` は添字 `p.1` の値が `dd2` である
ことを使うので、`|st1.dmap| = p.1` の場合（添字 `p.1` が範囲外）に別の議論が要る。
そのとき `rA.2.dmap[p.1]` は **A ブロックの最初の書き込み `dd2'`**（`≥ dd2 + 1 ≥ d + 1`）
になる。つまり次の不変量を足せばよい:

    def DmBot (d : ℕ) (st st' : St) : Prop :=
      ∀ j, st.dmap.length ≤ j → j < st'.dmap.length → d ≤ st'.dmap.getD j 0

「**入口の `dmap` の外側に書かれた値は、その呼び出しの深さ以上**」。

連結のとき `[|st.dmap|, |st1.dmap|)` の範囲は `DmKeep` で凍る
（`|st1.dmap| ≤ p.1 + 1` で、子の下界は `p.1` か `p.1+1`）。
境目の添字 `p.1` だけ場合分けが要る。**見積もり 150〜200 行。** -/
def ResidHeadT : Prop :=
  ∀ (rest : TrioSeq) (st' : St) (m d : ℕ), rest ≠ [] → (∀ c ∈ rest, m + 1 ≤ c.1) →
    m ≤ st'.dmap.length → Dm10 (d + 1) m st' → (rest.headI).1 ≤ st'.dmap.length

/-- **★ `Dm10`（節 10）は `ResidHeadT` だけから出る**（課題 L41）。 -/
theorem dm10_aux (hhdT : ResidHeadT) :
    ∀ (n : ℕ) (M : TrioSeq), M.length ≤ n → steps1 M → ∀ (m d : ℕ),
      (∀ c ∈ M, m ≤ c.1) → (M ≠ [] → (M.headI).1 = m) →
      ∀ (L : List Lent) (F : List Bool) (ps pw : ℕ × ℕ) (first force : Bool)
        (st : St) (nx : Option Col) (off : ℕ),
        m ≤ st.dmap.length → (M = [] → Dm10 d m st) →
        Dm10 d m (conv3 M d L F ps pw first force st nx off).2 := by
  intro n
  induction n with
  | zero =>
      intro M hM _ m d _ _ L F ps pw first force st nx off _ hpre
      have hnil : M = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      rw [conv3_nil]
      exact hpre rfl
  | succ n ih =>
      intro M hM hs1 m d hmem hhd L F ps pw first force st nx off hlen hpre
      cases M with
      | nil => rw [conv3_nil]; exact hpre rfl
      | cons p r =>
          have hr : r.length ≤ n := by simp only [List.length_cons] at hM; omega
          have hpm : p.1 = m := by
            have h9 := hhd (by simp)
            simpa using h9
          subst hpm
          exact dm10_step p r d L F ps pw first force st nx off hs1
            (blkLo_of_le hmem (fun _ => le_rfl)) hlen
            (fun M' hM' hs' m' d' hm' hh' => ih M' (le_trans hM' hr) hs' m' d' hm' hh')
            (fun rest rd Lr ps' pw' st' nx' off' e hlr hsr hmr1 hlr2 hpr hrd =>
              dm10_resid (NN := n) (fun M' h1 h2 => ih M' h1 h2)
                rest.length rest le_rfl (le_trans hlr hr) hsr p.1 d rd Lr ps' pw' st'
                nx' off' (fun c hc => le_trans (Nat.le_succ _) (hmr1 c hc)) hlr2
                (dm10_weak hpr)
                (fun hne => hhdT rest st' p.1 d hne hmr1 hlr2 hpr)
                (fun hne =>
                  resid_rd_lb hne hmr1 (hhdT rest st' p.1 d hne hmr1 hlr2 hpr) hpr hrd))

/-- **★ `Dm10`（節 10）** -/
theorem dm10_holds (hhdT : ResidHeadT) {m d : ℕ} (M : TrioSeq) (hs1 : steps1 M)
    (hmem : ∀ c ∈ M, m ≤ c.1) (hhd : M ≠ [] → (M.headI).1 = m)
    (L : List Lent) (F : List Bool) (ps pw : ℕ × ℕ) (first force : Bool) (st : St)
    (nx : Option Col) (off : ℕ) (hlen : m ≤ st.dmap.length)
    (hpre : M = [] → Dm10 d m st) :
    Dm10 d m (conv3 M d L F ps pw first force st nx off).2 :=
  dm10_aux hhdT M.length M le_rfl hs1 m d hmem hhd L F ps pw first force st nx off hlen
    hpre

/-- `conv3` の呼び出しごとの不変量（**まだ証明していない**、課題 L2 (b)）。

### 残りの補題（課題 L3 で**縮約でない枝まで詰めた**）

* 空の入力 … `conv3_nil` ＋ `BlkOK_nil`（**証明ずみ**）
* 縮約でない枝 … **証明ずみ**（`lean/L1-NOTES.md` の課題 L3 に戦術の全文がある。
  `depths_le` ＋ `cols_blk` ＋ `BlkOK_app` ×2 で 6 行。項が巨大なので
  `depths_ok` のように `cols` を結論に含む形だと単一化が `e2` / `pw` を
  決められない。深さだけの `depths_le` を別に立てるのが鍵）
* 縮約の枝 … **ここだけが残り**。2 つの穴がある:
  - **`contr_rd_ok`**: 残余の開始深さ `rd`（`d + 1 + e` か
    `dmapAt rU.2.dmap (rest2[0].1 - 1)`）が `d ≤ rd ≤ |rU.2.ST|` に収まる。
    前者は `dd2 ≥ d`（`depths_ok`）から出るが、**後者は `st.dmap`（もとの深さ ->
    像の深さ）と `st.ST` の関係を不変量にしないと出ない**。
    候補: 「`k < |dmap|` なら `dmap[k] < |ST|`、かつ `dmap` は狭義単調」。
  - **`convResid_blk`**: `convResid` の不変量。残余は**森**なので次の木で開始深さが
    `rd - (m0 - tail[0].1)` と**下がる**。連結のとき `BlkOK_app` の `d ≤ d'` が
    使えないので、`BlkOK_app'`（結論の第 2 項を直に仮定する版、**証明ずみ**）で
    受ける。そのうえで縮約の枝の `rB`（開始深さ `d`）に必要な `d ≤ |rR.2.ST|`
    を別に出す必要がある。

### ★ 課題 L11: 上の債務を**実際の呼び出し点で測った**（2026-08-28）

`lean/l11_blkmeas.py` が `Dbms3.lean` の本文をそのまま貼った使い捨ての Lean
file を作り、縮約の枝に計測を埋め込む（埋め込み先は `St.nc`。`nc` は像に
一切効かない）。**10 本すべて違反 0**:

    <=6 列 全数 8387 個   … 発火 44、違反 0、陽性対照 44/44
    7 列 縮約発火 294 個  … 発火 294、違反 0、陽性対照 294/294
    合計 338 発火 = 既知の発火（338/77282）を全部踏んでいる

測った 10 本: `d ≤ rd` / `rd ≤ |rU.2.ST|`（＝ `contr_rd_ok`）、
`BlkOK rd rU.2 (rR.1, rR.2)` の 5 節すべて（＝ `convResid_blk`）、
`d ≤ |rR.2.ST|`、`dmap` が狭義単調、`dmap` の全要素 `< |ST|`。

⟹ **`convResid_blk` は呼び出し点では `BlkOK` そのままで真**（弱めた形は
要らない。`rd` の上界を落とした `ResidBlk` が偽なのとは別の話）。
⟹ `BlkOK` に足す候補の `dmap` 不変量（狭義単調・`< |ST|`）も**真**。 -/
def BlkInv : Prop :=
  ∀ (M : TrioSeq) (d : ℕ) (L : List Lent) (F : List Bool) (ps pw : ℕ × ℕ)
    (first force : Bool) (st : St) (nx : Option Col) (off : ℕ),
    d ≤ st.ST.length → DmOK st → steps1 M → BlkLo M →
      BlkOK d st (conv3 M d L F ps pw first force st nx off)

/-! ### 課題 L13: `BlkInv` に残る仮定は 2 本だけ

`blk_step` を列数についての強い帰納法で回すと `BlkInv` が出る。
残るのは次の 2 本で、どちらも**縮約の枝の中でしか使わない**。 -/

/-- **(H1 の残り)** 残余の開始深さを `dmap` から読む枝で要る 3 つ。

`rd = dmapAt stU.dmap ((rest2.head).1 - 1)` の枝について

    第 1 項 `k ≤ |dmap|`      R1-NOTES §4.3 で**紙の証明あり**（Lean はまだ）
    下界 `d ≤ dmap[k]`        R1-NOTES 節 10（全 `conv3` 呼び出しで違反 0）
    上界 `dmap[k] ≤ |ST|`     R1-NOTES 節 11（同上）

⚠ **課題 L13 の「`k + 1 < |dmap|` は 338 発火で 0 回だから空虚」は誤りだった。**
母数を広げると **9 列で 3 例・10 列で 39 例**踏まれる（R1-NOTES §4.2）。
`dmapAt_bounds` は `k = |dmap|` と `k = |dmap| - 1` しか扱えないので、
**この仮定は空虚ではない**。R1 の節 10 / 節 11 を `BlkOK` に足せば消える見込み。

⚠ **課題 L12 の「`∀ k ∈ dmap, k < |ST|` は偽」も、不等号を `≤` にすると真**
（R1-NOTES 節 11、`gen3 <=8` の 13108043 呼び出し x2 で違反 0）。L12 が
「道具が無い」と判定した箇所の答えはこれである。 -/
def DmapInT : Prop :=
  ∀ (d : ℕ) (p : Col) (stU : St) (rest2 : TrioSeq),
    ¬(rest2 = [] ∨ (rest2.headD (0, 0, 0)).1 = p.1 + 1) →
    ((rest2.headD (0, 0, 0)).1 - 1 ≤ stU.dmap.length ∧
      ((rest2.headD (0, 0, 0)).1 - 1 + 1 < stU.dmap.length →
        d ≤ stU.dmap.getD ((rest2.headD (0, 0, 0)).1 - 1) 0 ∧
          stU.dmap.getD ((rest2.headD (0, 0, 0)).1 - 1) 0 ≤ stU.ST.length))

/-- **側条件 (H)**（課題 R2）。`convResid` の呼び出し点で成り立つべき

    ∀ c ∈ rest2, d + rest2.head.1 ≤ rd + c.1

を、`rd` の定義式で書き下したもの。R1-NOTES §3 / R2-3 によれば、これは
補題 A（`∀ c ∈ rest2, p.1 + 1 ≤ c.1`）と節 10（`dmap[k] ≥ d + (k - p.1)`）から
**出る**。まだ Lean に写していないので仮定として置く。 -/
def ResidSideT : Prop :=
  ∀ (d : ℕ) (p : Col) (stU : St) (rest2 : TrioSeq) (e : ℕ), ∀ c ∈ rest2,
    d + (rest2.headD (0, 0, 0)).1
      ≤ (if rest2 = [] ∨ (rest2.headD (0, 0, 0)).1 = p.1 + 1 then d + 1 + e
         else dmapAt stU.dmap ((rest2.headD (0, 0, 0)).1 - 1)) + c.1



/-- **縮約の枝で `rU.2` の節 10 を出す 1 歩**（課題 L45）。
`A` の子から `Dm10_of_child` で `(d+1, p.1)` に付け替え、`U` の呼び出しに渡す。 -/
theorem dm10_at_U (hhdT : ResidHeadT)
    {p : Col} {A U : TrioSeq} {d dd2 : ℕ} {st st1 : St}
    {LA LU : List Lent} {FA FU : List Bool} {psA pwA psU pwU : ℕ × ℕ}
    {f1A f2A f1U f2U : Bool} {nxA nxU : Option Col} {oa ou : ℕ}
    (hst1 : st1.dmap = st.dmap.take p.1 ++ [dd2])
    (hdd : d + 1 ≤ dd2) (hlen : p.1 ≤ st.dmap.length)
    (hsA : steps1 A) (hmA : ∀ c ∈ A, p.1 + 1 ≤ c.1)
    (hhA : A ≠ [] → (A.headI).1 = p.1 + 1)
    (hsU : steps1 U) (hmU : ∀ c ∈ U, p.1 ≤ c.1)
    (hhU : U ≠ [] → (U.headI).1 = p.1) :
    Dm10 (d + 1) p.1
      (conv3 U (d + 1) LU FU psU pwU f1U f2U
        (conv3 A (dd2 + 1) LA FA psA pwA f1A f2A st1 nxA oa).2 nxU ou).2 := by
  have hmA' : ∀ c ∈ A, p.1 ≤ c.1 := fun c hc => le_trans (Nat.le_succ _) (hmA c hc)
  have hlen1 : st1.dmap.length = p.1 + 1 := by rw [hst1, len_take_snoc hlen]
  have hrA : Dm10 (d + 1) p.1
      (conv3 A (dd2 + 1) LA FA psA pwA f1A f2A st1 nxA oa).2 := by
    refine Dm10_of_child hdd
      (dm10_holds hhdT A hsA hmA hhA _ _ _ _ _ _ _ _ _ (by omega)
        (fun _ => dm10_vac (by omega)))
      (Dm12_of_DmKeep (dmKeep_holds A hmA _ _ _ _ _ _ _ _ _ _)) ?_ (by omega)
    rw [hst1]
    exact getD_take_snoc hlen
  exact dm10_holds hhdT U hsU hmU hhU _ _ _ _ _ _ _ _ _
    (dmKeep_le (dmKeep_holds A hmA' _ _ _ _ _ _ _ _ _ _) (by omega)) (fun _ => hrA)

/-! ### 課題 L44: `DmapInT` / `ResidSideT` の**制限版**（呼び出し点の文脈つき）

上の 2 つの `example` のとおり、無制限の形は偽である。呼び出し点で分かっている
ことを仮定に足すと、**`ResidSideR` は仮定ゼロで、`DmapInR` は状態の不変量
`DmST`（＝ 節 11）だけで出る**。 -/

/-- **状態の不変量（R1 の節 11）**: `dmap` の値は `ST` の高さ以下。

⚠ **`st` を無制限に全称化した形は偽**（`st.ST = []`, `st.dmap = [5]`）。
呼び出しの鎖に沿って運ぶ述語として使うこと。実測は `gen3 <=8` の
13108043 呼び出し x2 で違反 0（R1-NOTES 節 11）。 -/
def DmST (st : St) : Prop :=
  ∀ k, k < st.dmap.length → st.dmap.getD k 0 ≤ st.ST.length

/-- **側条件 (H) の制限版**。 -/
def ResidSideR : Prop :=
  ∀ (d : ℕ) (p : Col) (stU : St) (rest2 : TrioSeq) (e : ℕ),
    (∀ c ∈ rest2, p.1 + 1 ≤ c.1) → p.1 ≤ stU.dmap.length → Dm10 (d + 1) p.1 stU →
    (rest2 ≠ [] → (rest2.headI).1 ≤ stU.dmap.length) →
    ∀ c ∈ rest2,
      d + (rest2.headD (0, 0, 0)).1
        ≤ (if rest2 = [] ∨ (rest2.headD (0, 0, 0)).1 = p.1 + 1 then d + 1 + e
           else dmapAt stU.dmap ((rest2.headD (0, 0, 0)).1 - 1)) + c.1

/-- **★ 側条件 (H) は制限すると仮定ゼロで出る**（課題 L44）。
`resid_rd_lb` が `d + h ≤ rd + p.1` をくれ、`c.1 ≥ p.1 + 1` で押し上げるだけ。 -/
theorem residSideR_holds : ResidSideR := by
  intro d p stU rest2 e hmem hlen hpre hhd c hc
  have hne : rest2 ≠ [] := by
    intro h
    rw [h] at hc
    simp at hc
  have h1 := resid_rd_lb (m := p.1) (d := d) (e := e) hne hmem (hhd hne) hpre rfl
  rw [headI_eq_headD] at h1
  have h2 := hmem c hc
  omega

/-- **`DmapInT` の制限版**。 -/
def DmapInR : Prop :=
  ∀ (d : ℕ) (p : Col) (stU : St) (rest2 : TrioSeq),
    (∀ c ∈ rest2, p.1 + 1 ≤ c.1) → p.1 ≤ stU.dmap.length → Dm10 (d + 1) p.1 stU →
    (rest2 ≠ [] → (rest2.headI).1 ≤ stU.dmap.length) → DmST stU →
    ¬(rest2 = [] ∨ (rest2.headD (0, 0, 0)).1 = p.1 + 1) →
    ((rest2.headD (0, 0, 0)).1 - 1 ≤ stU.dmap.length ∧
      ((rest2.headD (0, 0, 0)).1 - 1 + 1 < stU.dmap.length →
        d ≤ stU.dmap.getD ((rest2.headD (0, 0, 0)).1 - 1) 0 ∧
          stU.dmap.getD ((rest2.headD (0, 0, 0)).1 - 1) 0 ≤ stU.ST.length))

/-- **★ `DmapInT` は制限すると `DmST`（節 11）だけから出る**（課題 L44）。
第 1 項は `ResidHeadT`、下界は `Dm10` を添字 `h-1` で読むだけ、
上界は `DmST` そのもの。 -/
theorem dmapInR_holds : DmapInR := by
  intro d p stU rest2 hmem hlen hpre hhd hst hc
  have hne : rest2 ≠ [] := fun h => hc (Or.inl h)
  have hne2 : (rest2.headD (0, 0, 0)).1 ≠ p.1 + 1 := fun h => hc (Or.inr h)
  have hh := hhd hne
  rw [headI_eq_headD] at hh
  have hm1 : p.1 + 1 ≤ (rest2.headD (0, 0, 0)).1 := hmem _ (headD_memT hne _)
  refine ⟨by omega, ?_⟩
  intro hlt
  refine ⟨?_, hst _ (by omega)⟩
  have h9 := hpre ((rest2.headD (0, 0, 0)).1 - 1) (by omega) (by omega)
  omega

/-! ### ⚠⚠ 課題 L44: `DmapInT` / `ResidSideT` は**そのままでは偽**（2026-08-29）

どちらも `stU` / `rest2` を**無制限に**全称化しているので、呼び出し点と無関係な
状態を入れると破れる。実測（R1 / `l11_blkmeas.py`）は**呼び出し点で**測ったもので、
Lean の `def` はそれより広い。⟹ **いまの `ImgBlockT3_of_resid` は空虚**である。

下の 2 つの `example` がその証明。 -/

example : ¬ ResidSideT := by
  intro h
  exact absurd (h 5 (0, 0, 0) ⟨[], 2, [0], [], 0, []⟩ [(2, 0, 0)] 0 (2, 0, 0) (by simp))
    (by decide)

example : ¬ DmapInT := by
  intro h
  have h2 := (h 0 (0, 0, 0) ⟨[], 2, [], [], 0, []⟩ [(5, 0, 0)] (by simp)).1
  simp at h2

/-! ### 課題 L45: 状態の不変量 `DmST`（節 11）の伝播

`DmST`（`dmap` の値 ≤ `ST` の高さ）を保つには、`st1.ST = ST2.take dd2 ++ [·]` で
**スタックが `dd2` に切り詰められる**ので、古い `dmap[k]`（`k < p.1`）が `≤ dd2+1`
である必要がある。それを言うのが `Dm11`（`dmap[k] ≤ d+1`、`d ≤ dd2`）。

⚠ `Dm11` は `DmKeep` だけでは伝わらない（`k < |st'.dmap|` から `k < |st.dmap|` が
出ないから ＝ 課題 R1 の 8 列の反例）。**`m ≤ |st.dmap|` を足すと伝わる**
（`dm11_keep`）。呼び出し点ではそれが成り立っている。 -/

/-- 深さと `dmap` の 2 つの不変量を一緒に運ぶ。 -/
def StOK (d : ℕ) (st : St) : Prop := d ≤ st.ST.length ∧ DmST st

theorem StOK_mono {d d' : ℕ} {st : St} (h : d ≤ d') (hs : StOK d' st) : StOK d st :=
  ⟨le_trans h hs.1, hs.2⟩

theorem dm11_mono {d d' m : ℕ} {st : St} (h : d ≤ d') (hs : Dm11 d m st) :
    Dm11 d' m st := fun k hk hl => le_trans (hs k hk hl) (by omega)

theorem getD_take_lt {l : List ℕ} {j k : ℕ} (hk : k < j) :
    (l.take j).getD k 0 = l.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  first
    | rw [List.getElem?_take hk]
    | rw [List.getElem?_take_of_lt hk]
    | simp [List.getElem?_take, hk]

/-- **`Dm11` は `m ≤ |st.dmap|` があれば `DmKeep` で伝わる**。 -/
theorem dm11_keep {d m : ℕ} {st st' : St} (hm : m ≤ st.dmap.length)
    (h : Dm11 d m st) (hk : DmKeep m st st') : Dm11 d m st' := by
  intro k hkm hlen
  have h1 : k < st.dmap.length := by omega
  rw [(hk k hkm h1).2]
  exact h k hkm h1

/-- **1 列ぶんの状態は `StOK (dd2+1)`**（`DmST` の要）。 -/
theorem dmST_st1 {d dd2 j : ℕ} {st st1 : St} {ST2 : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hdmap : st1.dmap = st.dmap.take j ++ [dd2])
    (hST : st1.ST = ST2.take dd2 ++ [x])
    (hdd2 : dd2 ≤ ST2.length) (hd : d ≤ dd2)
    (hj : j ≤ st.dmap.length) (h11 : Dm11 d j st) :
    StOK (dd2 + 1) st1 := by
  have hlenST : st1.ST.length = dd2 + 1 := by rw [hST, len_take_app hdd2]
  refine ⟨by omega, ?_⟩
  intro k hk
  rw [hlenST, hdmap]
  rw [hdmap, len_take_snoc hj] at hk
  by_cases hkj : k < j
  · rw [getD_snoc_lt (by rw [List.length_take]; omega), getD_take_lt hkj]
    have h9 := h11 k hkj (by omega)
    omega
  · have hkk : k = j := by omega
    subst hkk
    rw [getD_take_snoc hj]
    omega

/-- 子の呼び出しに渡す `Dm11`（深さ `dd2+1`、下界 `j+1`）。 -/
theorem dm11_st1 {d dd2 j : ℕ} {st st1 : St}
    (hdmap : st1.dmap = st.dmap.take j ++ [dd2])
    (hd : d ≤ dd2) (hj : j ≤ st.dmap.length) (h11 : Dm11 d j st) :
    Dm11 (dd2 + 1) (j + 1) st1 := by
  intro k hk hlen
  rw [hdmap] at hlen ⊢
  rw [len_take_snoc hj] at hlen
  by_cases hkj : k < j
  · rw [getD_snoc_lt (by rw [List.length_take]; omega), getD_take_lt hkj]
    have h9 := h11 k hkj (by omega)
    omega
  · have hkk : k = j := by omega
    subst hkk
    rw [getD_take_snoc hj]
    omega

/-- 同じ深さ・同じ下界の `Dm11` は `take` を越えて残る。 -/
theorem dm11_st1' {d dd2 j : ℕ} {st st1 : St}
    (hdmap : st1.dmap = st.dmap.take j ++ [dd2])
    (hj : j ≤ st.dmap.length) (h11 : Dm11 d j st) : Dm11 d j st1 := by
  intro k hk hlen
  rw [hdmap] at hlen ⊢
  rw [len_take_snoc hj] at hlen
  rw [getD_snoc_lt (by rw [List.length_take]; omega), getD_take_lt hk]
  exact h11 k hk (by omega)

/-- **`DmST` の帰納の 1 歩**（課題 L45）。`convResid` の枝だけ仮定 `hres` に置く
（測定 (N') 待ち）。 -/
theorem dmST_step (p : Col) (r : TrioSeq) (d : ℕ) (L : List Lent) (F : List Bool)
    (ps pw : ℕ × ℕ) (first force : Bool) (st : St) (nx : Option Col) (off : ℕ)
    (hs1 : steps1 (p :: r)) (hblo : BlkLo (p :: r))
    (hlen : p.1 ≤ st.dmap.length) (hst : StOK d st) (h11 : Dm11 d p.1 st)
    (IH : ∀ (M' : TrioSeq), M'.length ≤ r.length → steps1 M' → ∀ (m' d' : ℕ),
        (∀ c ∈ M', m' ≤ c.1) → (M' ≠ [] → (M'.headI).1 = m') →
        ∀ (L' : List Lent) (F' : List Bool) (ps' pw' : ℕ × ℕ) (f1 f2 : Bool)
          (st' : St) (nx' : Option Col) (off' : ℕ),
          m' ≤ st'.dmap.length → StOK d' st' → Dm11 d' m' st' →
          StOK d' (conv3 M' d' L' F' ps' pw' f1 f2 st' nx' off').2)
    (hres : ∀ (rest : TrioSeq) (rd : ℕ) (Lr : List Lent) (ps' pw' : ℕ × ℕ) (st' : St)
        (nx' : Option Col) (off' e : ℕ),
        rest.length ≤ r.length → steps1 rest → (∀ c ∈ rest, p.1 + 1 ≤ c.1) →
        p.1 ≤ st'.dmap.length → StOK (d + 1) st' → Dm11 (d + 1) p.1 st' →
        (rest ≠ [] → (rest.headI).1 ≤ st'.dmap.length) →
        rd = (if rest = [] ∨ (rest.headD (0, 0, 0)).1 = p.1 + 1 then d + 1 + e
              else dmapAt st'.dmap ((rest.headD (0, 0, 0)).1 - 1)) →
        StOK d (convResid rest rd Lr ps' pw' st' nx' off').2)
    (hhdT : ResidHeadT) :
    StOK d (conv3 (p :: r) d L F ps pw first force st nx off).2 := by
  have hr1 : steps1 r := steps1_tailT hs1
  have hmr : ∀ c ∈ r, p.1 ≤ c.1 := by
    intro c hc
    have h9 := hblo c (List.mem_cons_of_mem _ hc)
    simpa using h9
  have hAmem : ∀ c ∈ r.takeWhile (fun q => decide (p.1 < q.1)), p.1 + 1 ≤ c.1 := by
    intro c hc
    have hne : r.takeWhile (fun q => decide (p.1 < q.1)) ≠ [] := by
      intro h; rw [h] at hc; simp at hc
    have h1 := takeWhile_blkLo hs1 c hc
    rw [takeWhile_head_eq hs1 hne] at h1
    exact h1
  have hAmem' : ∀ c ∈ r.takeWhile (fun q => decide (p.1 < q.1)), p.1 ≤ c.1 :=
    fun c hc => le_trans (Nat.le_succ _) (hAmem c hc)
  have hlen1 : ∀ x : ℕ, (st.dmap.take p.1 ++ [x]).length = p.1 + 1 :=
    fun x => len_take_snoc hlen
  rw [conv3.eq_def]
  dsimp only
  split
  · -- 縮約の枝
    rename_i ee kUv kpv nav he
    have hlad0 := cond_of_ite_some he
    rw [if_pos hlad0] at he
    split at he
    · simp at he
    · rename_i e kU kp na hcf
      have hw : ((e, kU, kp, na) : ℕ × ℕ × ℕ × Col) = (ee, kUv, kpv, nav) := by
        rcases ite_some_pair he with h | h
        · exact ite_some_none h
        · exact h
      have hk : kU = kUv := congrArg (fun t => t.2.1) hw
      have hmRs : ∀ cc ∈ ((((r.dropWhile (fun q => decide (p.1 < q.1))).drop kUv).tail).take
          (deepGe ((((r.dropWhile (fun q => decide (p.1 < q.1))).drop kUv).headD (0, 0, 0)).1 + 1)
            (((r.dropWhile (fun q => decide (p.1 < q.1))).drop kUv).tail))).drop kpv,
          p.1 + 1 ≤ cc.1 := by
        intro cc hcc
        have hne2 :
            ((r.dropWhile (fun q => decide (p.1 < q.1))).drop kUv).tail ≠ [] := by
          intro hc
          rw [hc] at hcc
          simp at hcc
        have hnep : (r.dropWhile (fun q => decide (p.1 < q.1))).drop kUv ≠ [] := by
          intro hc
          rw [hc] at hne2
          simp at hne2
        have hqmem :
            (((r.dropWhile (fun q => decide (p.1 < q.1))).drop kUv).headD (0, 0, 0)) ∈ r :=
          ((List.drop_sublist _ _).trans (List.dropWhile_sublist _)).mem
            (headD_memT hnep _)
        have hq := hmr _ hqmem
        have h1 := deepGe_take_ge _ cc ((List.drop_sublist _ _).mem hcc)
        omega
      refine IH _ ?lQ ?sQ p.1 d ?mQ ?hQ _ _ _ _ _ _ _ _ _ ?dQ ?sQ2 ?dm11Q
      case lQ => exact List.Sublist.length_le (by subl_tac)
      case sQ =>
        repeat' first
          | exact hr1
          | apply steps1_takeT
          | apply steps1_dropT
          | apply steps1_takeWhileT
          | apply steps1_dropWhileT
          | apply steps1_tailT
      case mQ => exact mem_le_of_sublist (by subl_tac) hmr
      case hQ =>
        intro hne
        rw [headI_eq_headD]
        refine head_eq_of_le_of_ge (x := (0, 0, 0)) ?_ hne ?_
        · intro c hc
          exact mem_le_of_sublist (by subl_tac) hmr c hc
        · have h8 := deepGe_head_lt _ (0, 0, 0) hne
          have hq := contrFind_q_eq hcf
          rw [hk] at hq
          omega
      case dQ =>
        exact dmKeep_le (dmKeep_resid_holds _ (mem_le_of_sublist (by subl_tac) hmr) _ _ _ _ _ _ _)
          (dmKeep_le (dmKeep_holds _ (mem_le_of_sublist (by subl_tac) hmr) _ _ _ _ _ _ _ _ _ _)
            (dmKeep_le (dmKeep_holds _ hAmem' _ _ _ _ _ _ _ _ _ _)
              (by rw [hlen1]; omega)))
      case dm11Q =>
        refine dm11_keep ?_ ?_ (dmKeep_resid_holds _ (mem_le_of_sublist (by subl_tac) hmr) _ _ _ _ _ _ _)
        · exact dmKeep_le (dmKeep_holds _ (mem_le_of_sublist (by subl_tac) hmr) _ _ _ _ _ _ _ _ _ _)
            (dmKeep_le (dmKeep_holds _ hAmem' _ _ _ _ _ _ _ _ _ _) (by rw [hlen1]; omega))
        · refine dm11_keep ?_ ?_ (dmKeep_holds _ (mem_le_of_sublist (by subl_tac) hmr) _ _ _ _ _ _ _ _ _ _)
          · exact dmKeep_le (dmKeep_holds _ hAmem' _ _ _ _ _ _ _ _ _ _) (by rw [hlen1]; omega)
          · exact dm11_keep (by rw [hlen1]; omega)
              (dm11_st1' rfl hlen h11) (dmKeep_holds _ hAmem' _ _ _ _ _ _ _ _ _ _)
      case sQ2 =>
        refine hres _ _ _ _ _ _ _ _ _ ?lRs ?sRs hmRs ?dU ?sU ?d11U ?hhU rfl
        case lRs => exact List.Sublist.length_le (by subl_tac)
        case sRs =>
          repeat' first
            | exact hr1
            | apply steps1_takeT
            | apply steps1_dropT
            | apply steps1_takeWhileT
            | apply steps1_dropWhileT
            | apply steps1_tailT
        case dU =>
          exact dmKeep_le (dmKeep_holds _ (mem_le_of_sublist (by subl_tac) hmr) _ _ _ _ _ _ _ _ _ _)
            (dmKeep_le (dmKeep_holds _ hAmem' _ _ _ _ _ _ _ _ _ _) (by rw [hlen1]; omega))
        case d11U =>
          refine dm11_keep ?_ ?_ (dmKeep_holds _ (mem_le_of_sublist (by subl_tac) hmr) _ _ _ _ _ _ _ _ _ _)
          · exact dmKeep_le (dmKeep_holds _ hAmem' _ _ _ _ _ _ _ _ _ _) (by rw [hlen1]; omega)
          · exact dm11_mono (by omega)
              (dm11_keep (by rw [hlen1]; omega) (dm11_st1' rfl hlen h11)
                (dmKeep_holds _ hAmem' _ _ _ _ _ _ _ _ _ _))
        case hhU =>
          intro hne
          refine hhdT _ _ p.1 d hne hmRs ?_ ?_
          · exact dmKeep_le (dmKeep_holds _ (mem_le_of_sublist (by subl_tac) hmr) _ _ _ _ _ _ _ _ _ _)
              (dmKeep_le (dmKeep_holds _ hAmem' _ _ _ _ _ _ _ _ _ _) (by rw [hlen1]; omega))
          · refine dm10_at_U hhdT ?hq1 ?hq2 hlen
              (steps1_takeWhileT hr1 _) hAmem (fun h => takeWhile_head_eq hs1 h) ?hq3
              ?hq4 ?hq5
            case hq1 => rfl
            case hq2 => exact depths_le_lad0 hlad0 rfl rfl rfl
            case hq3 =>
              repeat' first
                | exact hr1
                | apply steps1_takeT
                | apply steps1_dropT
                | apply steps1_takeWhileT
                | apply steps1_dropWhileT
                | apply steps1_tailT
            case hq4 => exact mem_le_of_sublist (by subl_tac) hmr
            case hq5 =>
              intro hne2
              have hne3 : r.dropWhile (fun q => decide (p.1 < q.1)) ≠ [] := by
                intro hc; rw [hc] at hne2; simp at hne2
              rw [headI_take hne2]
              exact dropWhile_head_eq hblo hne3
        case sU =>
          refine IH _ ?lU ?sU2 p.1 (d + 1) ?mU ?hU _ _ _ _ _ _ _ _ _ ?dA ?sA ?d11A
          case lU => exact List.Sublist.length_le (by subl_tac)
          case sU2 =>
            repeat' first
              | exact hr1
              | apply steps1_takeT
              | apply steps1_dropT
              | apply steps1_takeWhileT
              | apply steps1_dropWhileT
              | apply steps1_tailT
          case mU => exact mem_le_of_sublist (by subl_tac) hmr
          case hU =>
            intro hne
            have hne2 : r.dropWhile (fun q => decide (p.1 < q.1)) ≠ [] := by
              intro hc; rw [hc] at hne; simp at hne
            rw [headI_take hne]
            exact dropWhile_head_eq hblo hne2
          case dA =>
            exact dmKeep_le (dmKeep_holds _ hAmem' _ _ _ _ _ _ _ _ _ _)
              (by rw [hlen1]; omega)
          case d11A =>
            exact dm11_mono (by omega)
              (dm11_keep (by rw [hlen1]; omega) (dm11_st1' rfl hlen h11)
                (dmKeep_holds _ hAmem' _ _ _ _ _ _ _ _ _ _))
          case sA =>
            refine StOK_mono (d' := _) ?_
              (IH _ ?lA ?sA2 (p.1 + 1) _ hAmem ?hA _ _ _ _ _ _ _ _ _ ?dA1 ?sA1 ?d11A1)
            case lA => exact List.Sublist.length_le (by subl_tac)
            case sA2 => exact steps1_takeWhileT hr1 _
            case hA => exact fun h => takeWhile_head_eq hs1 h
            case dA1 => rw [hlen1]
            case sA1 =>
              exact dmST_st1 rfl rfl (depths_le hst.1 rfl rfl rfl rfl rfl).2
                (depths_le_lo rfl rfl rfl) hlen h11
            case d11A1 => exact dm11_st1 rfl (depths_le_lo rfl rfl rfl) hlen h11
            · exact Nat.le_succ_of_le (depths_le_lad0 hlad0 rfl rfl rfl)
  · -- 縮約でない枝
    refine IH _ ?lB ?sB p.1 d ?mB ?hB _ _ _ _ _ _ _ _ _ ?dAn ?sAn ?d11An
    case lB => exact List.length_dropWhile_le _ r
    case sB => exact steps1_dropWhileT hr1 _
    case mB => exact mem_le_of_sublist (List.dropWhile_sublist _) hmr
    case hB => exact dropWhile_head_eq hblo
    case dAn =>
      exact dmKeep_le (dmKeep_holds _ hAmem' _ _ _ _ _ _ _ _ _ _) (by rw [hlen1]; omega)
    case d11An =>
      exact dm11_keep (by rw [hlen1]; omega) (dm11_st1' rfl hlen h11)
        (dmKeep_holds _ hAmem' _ _ _ _ _ _ _ _ _ _)
    case sAn =>
      refine StOK_mono (d' := _) ?_
        (IH _ ?lA2 ?sA3 (p.1 + 1) _ hAmem ?hA2 _ _ _ _ _ _ _ _ _ ?dA2 ?sA2b ?d11A2)
      case lA2 => exact (List.takeWhile_sublist _).length_le
      case sA3 => exact steps1_takeWhileT hr1 _
      case hA2 => exact fun h => takeWhile_head_eq hs1 h
      case dA2 => rw [hlen1]
      case sA2b =>
        exact dmST_st1 rfl rfl (depths_le hst.1 rfl rfl rfl rfl rfl).2
          (depths_le_lo rfl rfl rfl) hlen h11
      case d11A2 => exact dm11_st1 rfl (depths_le_lo rfl rfl rfl) hlen h11
      · exact Nat.le_succ_of_le (depths_le_lo rfl rfl rfl)

theorem blkInv_aux (h2 : DmapInT) (h3 : ResidSideT) :
    ∀ (n : ℕ) (M : TrioSeq), M.length ≤ n → steps1 M → BlkLo M → ∀ (d : ℕ)
      (L : List Lent)
      (F : List Bool) (ps pw : ℕ × ℕ) (first force : Bool) (st : St)
      (nx : Option Col) (off : ℕ), d ≤ st.ST.length → DmOK st →
      BlkOK d st (conv3 M d L F ps pw first force st nx off) := by
  intro n
  induction n with
  | zero =>
      intro M hM _ _ d L F ps pw first force st nx off hd hdm
      have hnil : M = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      rw [conv3_nil]
      exact BlkOK_nil hd hdm
  | succ n ih =>
      intro M hM hs1 hbl d L F ps pw first force st nx off hd hdm
      cases M with
      | nil => rw [conv3_nil]; exact BlkOK_nil hd hdm
      | cons p r =>
          have hr : r.length ≤ n := by simp only [List.length_cons] at hM; omega
          exact blk_step p r d L F ps pw first force st nx off hd hs1 hbl
            (fun M' hM' hs' hb' => ih M' (le_trans hM' hr) hs' hb')
            (fun rest hlen hsr rd Lr ps' pw' st' nx' off' hd' hb hdm' hH =>
              resid_blk (NN := n) (d := d)
                (fun M' hM'' hs'' hb'' => ih M' hM'' hs'' hb'') rest.length rest
                le_rfl (le_trans hlen hr) hsr rd Lr ps' pw' st' nx' off' hd' hb
                hdm' hH)
            (fun stU rest2 e c hc => h3 d p stU rest2 e c hc)
            (fun stU rest2 hc => h2 d p stU rest2 hc)

/-- **★ `BlkInv` は 2 本の仮定から出る**（課題 L15）。 -/
theorem blkInv_of (h2 : DmapInT) (h3 : ResidSideT) : BlkInv :=
  fun M d L F ps pw first force st nx off hd hdm hs hbl =>
    blkInv_aux h2 h3 M.length M le_rfl hs hbl d L F ps pw first force st nx off hd
      hdm

end Conv3

/-- **`ImgBlockT3` は `Conv3.BlkInv` から出る**（課題 L2 (b)）。

入口 `b2d3` は `st.ST = []` で始めるので `|st.ST| = 0`、したがって
`BlkOK` の「先頭の柱の行 0 ≤ `|st.ST|`」がそのまま「先頭の柱の行 0 = 0」になる。
`∀ p ∈ B, 0 ≤ p.1` は ℕ なので自明。残りは `steps1` そのもの。 -/
theorem ImgBlockT3_of_BlkInv (h : Conv3.BlkInv) : ImgBlockT3 Conv3.b2d3 := by
  intro A _hA
  obtain ⟨hs, -, -, hh, -, -, -, -⟩ :=
    h A 0 [] [] (0, 0) (0, 0) true false ⟨[], 2, [], A, 0, []⟩ none 0 (by simp)
      (by intro hc; exact absurd rfl hc) (blockok_ST_TS _hA).2.2
      (by
        intro c hc
        have hne : A ≠ [] := by intro hh; rw [hh] at hc; simp at hc
        rw [(blockok_ST_TS _hA).1 hne]
        exact Nat.zero_le _)
  refine ⟨?_, fun p _ => Nat.zero_le _, hs⟩
  intro hne
  simpa using hh hne

/-- **★★ `ImgBlockT3` は 2 本の仮定から出る**（課題 L15）。

    ResidSideT   `convResid` の呼び出し点の側条件 (H)（R1-NOTES §3 / R2-3）
    DmapInT      `dmapAt` の範囲内の枝（R1-NOTES 節 10 ＋ 節 11）

`convResid` そのものの block 性（課題 L13 の `ResidBlkT`、結論が `BlkOK rd` で
**偽**だったもの）は、結論を **`BlkOK d`** に直したうえで `resid_blk` として
**証明した**ので仮定から消えた。残る 2 本はどちらも
`tools/dbms/R1-NOTES.md` が全 `conv3` 呼び出し（`gen3 <=8` 全数 13108043 回）で
違反 0・陽性対照つきで測っている。 -/
theorem ImgBlockT3_of_resid (h2 : Conv3.DmapInT) (h3 : Conv3.ResidSideT) :
    ImgBlockT3 Conv3.b2d3 := ImgBlockT3_of_BlkInv (Conv3.blkInv_of h2 h3)


/-! ## 12. `OrderT3` を証明するには何が要るか

2 行側の `conC_olt_iff_seqlex`（`Dbms.lean:2791`）は 2 行だけである:

    rw [readC_conC_ST hM, readC_conC_ST hN]
    exact olt_iff_seqlex (blockok_ST_PS hM) (blockok_ST_PS hN) hne

つまり中身は 2 つで、**どちらも 3 行にはまだ無い**。

1. **読みの保存** `readCon (conC M) = translate M`（`Dbms.lean:2765`）。
   `readC_convC` の証明は `Dbms.lean` の §5-§8、2600 行ぶんある。
   3 行では読み `read3` そのものがまだ書かれていない（`readD` は
   「ブロックの先頭で段が親と同じ・次が `p + (1,1)` なら影として捨てる」という
   節を `translate` に 1 つ足したもの。3 行では行 1 の影と行 2 の影の 2 種類が
   あるので節は 2 つ要る）。

2. **DBMS 側の順序同型**。2 行版はここで `olt_iff_seqlex` を **BMS 側の**
   `M`, `N` に当てて逃げている（右辺が `seqlex M N`）。`OrderT3` は右辺が
   `seqlex (conv3 M) (conv3 N)` なので、DBMS 側で

       read3 C <o read3 D  ↔  seqlex C D

   が要る。`read3` は影の列を読み飛ばすので `translate` ではなく、
   `olt_iff_seqlex` をそのまま当てることはできない。`blockok` に当たる
   「影の作法」（影の直後には必ずその昇格列が来る、等）を DBMS 側の不変量
   `dok` として立て、それが `conv3` の像で成り立つことと、`dok` の上で
   `read3` が `seqlex` への順序同型になることを示す必要がある。

下の `OrderT3_of_read` はこの 2 段をそのまま組んだもの（`read3` と `dok` は
関数／述語の変数）。**証明は 3 行**で、仕事は全部 3 つの仮定の側にある。 -/

/-- 読みの保存（2 行の `readC_conC_ST` の 3 行版）。 -/
def ReadT3 (read3 : TrioSeq → Three) (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {M : TrioSeq}, ST_TS M → read3 (conv3 M) = translate M

/-- 像は DBMS 側の作法 `dok` を満たす（2 行の `blockok_ST_PS` に当たる）。 -/
def ImgDokT3 (dok : TrioSeq → Prop) (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {M : TrioSeq}, ST_TS M → dok (conv3 M)

/-- `dok` の上で `read3` は列辞書式への順序同型（2 行の `olt_iff_seqlex` に当たる）。 -/
def ReadLexT3 (read3 : TrioSeq → Three) (dok : TrioSeq → Prop) : Prop :=
  ∀ {C D : TrioSeq}, dok C → dok D → (read3 C <o read3 D ↔ seqlex C D)

/-- **`OrderT3` は「読みの保存」＋「DBMS 側の順序同型」から出る。**

証明は 3 行で、仕事は全部 3 つの仮定の側にある。 -/
theorem OrderT3_of_read {read3 : TrioSeq → Three} {dok : TrioSeq → Prop}
    {conv3 : TrioSeq → TrioSeq}
    (hr : ReadT3 read3 conv3) (hk : ImgDokT3 dok conv3) (hx : ReadLexT3 read3 dok) :
    OrderT3 conv3 := by
  intro M N hM hN
  rw [← hr hM, ← hr hN]
  exact hx (hk hM) (hk hN)

/-! ### 12.1 `OrderT3` の順序数を通らない言い換え

標準形の上では `translate` が `seqlex` への順序同型（`olt_ST_iff_seqlex`）なので、
`OrderT3` は「`conv3` が列辞書式の順序埋め込みである」と**同値**である。
こちらは項も読みも順序数も出てこないので、Python で

    L を辞書式に並べ替えたもの  と  L を像の辞書式で並べ替えたもの  が一致するか

を見るだけで全数採点できる（実測: `conv3` v12 は <=6 列 8387 個・<=7 列 77282 個で
位置ずれ 0、像の重複も 0）。読み `read3` を書かずに `OrderT3` を証明する道があるなら
この形（`conv3` の構造帰納法）だろう。 -/

/-! ### ⚠ `OrderT3` は **未成立**（`len ≤ 11` で 24 件破れる）（課題 R7/R8/R9）

`OrderT3_iff_seqemb`（下、**証明ずみ**）より `OrderT3 ↔ SeqEmbT3` なので、
`SeqEmbT3` の反例は `OrderT3` の反例でもある。**証明しに行かないこと。**

反例（8 列 ＋ 9 列。どちらも `ST_TS`）:

    M1 = (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,1,0)(3,0,0)(4,1,1)(4,1,0)
    M2 = M1 ++ (5,1,0)                     M1 は M2 の**真の接頭辞**

    seqlex M1 M2 = 真（`seqlex_prefix`）
    f M1 = …(6,2,1)**(6,2,0)**
    f M2 = …(6,2,1)**(5,1,0)**(6,1,0)
    第 8 柱で (6,2,0) vs (5,1,0)。6 > 5 なので seqlex (f M1) (f M2) = **偽**

`ST_TS` であることは展開の道を復元して確認ずみ: 共通の祖先
`X = M1 ++ (5,2,1)` から `M1 = X⟦1⟧`、`M2 = X⟦2⟧⟦2⟧`、`X` 自身は
`diagSeqT 0 2` から 15 手。

**なぜ今まで見えなかったか**（母数の問題。課題 L14 と同じ形）:

| 母集団 | 個数 | (→) の破れ | (←) の破れ |
|---|---:|---:|---:|
| `ST_TS` 展開閉包 `v≤4, len≤9` | 44063 | **0** | **0** |
| **`v≤5, len≤10`** | **416607** | **41** | **38** |

**両方 `≤8` 列の対は 41 件中 0 件**なので、`gen3 ≤8` の突き合わせでは
**原理的に見えない**。これまでの「順序保存 違反 0」は母数が狭かっただけである。

**犯人は縮約ではない**（破れ 41 件中 39 件で縮約は 1 度も発火しない）:

> **分岐列 `(a,1,0)` の綴りが「次の列」に依存すること。**
> 反例では末尾の `(4,1,0)` が、行列の末尾のときは深く `(6,2,0)`、
> 後ろに `(5,1,0)` が来ると浅く `(5,1,0)` と綴られる。

接頭辞単調が破れる 22624 個も**同じ機構**（100% が `body` の柱、
0% が縮約の中、98.6% が像の末尾 1 柱だけ、96.9% が「行 1 だけ違う」）。

## ⚠ 訂正（課題 R9, 2026-08-29）: **3 旗オフでも成立しない**

いったん「3 条項を切れば `SeqEmbT3` の破れ 41 -> 0」と測れたが、
**母数を `len ≤ 11`（1882196 個）に広げると (→) 24 件 / (←) 24 件破れる**。

    M1 = (0,0,0)(1,1,1)(1,1,1)(1,0,0)(2,1,1)(2,1,0)(3,1,0)(2,1,0)(3,1,0)(2,1,0)(3,1,0)
    M2 = (0,0,0)(1,1,1)(1,1,1)(1,0,0)(2,1,1)(2,1,0)(3,1,0)(3,0,0)

⟹ Lean の 6 仮定の表では **`OrderT3` は「未成立（`len ≤ 11` で 24 件）」**とする。
**`len ≤ 10` で 0 だったのは母数が狭かっただけ**（今日 4 度目の同じ形）。

## ★ ただし `ReindexT1` に**全域の順序保存は要らない**（課題 L28）

下の `OrderReindexT3` / `ReindexT1_of_cofinal'` を見よ。**(→) は 1 か所も使わない。**

## 参考: シート自身は完全に順序保存（課題 R8）

**シート自身は完全に順序保存**である:

| 切り方 | 母数 | A 列が昇順 | E 列が昇順 |
|---|---:|---|---|
| 誤記 5 件を除く / z<2 の 3 行 | 1618 | **1617/1617** | **1617/1617** |
| 誤記を除かない / 全部 | 1622 | 1621/1621 | 1621/1621 |

    A 列の `seqlex` 昇順で E 列も昇順: 増 1588 / 等 0 / **減 0**、重複 0

`seqlex` は BMS 標準形の上で順序数の順序と一致する（`olt_ST_iff_seqlex`）ので、
「A 列が行番号順に昇順（破れ 0）」は「**行番号の順序 ＝ 順序数の順序**」の
証明そのものである。

**犯人は 3 条項**（`tiesd` / `awflip` / `h1`）で、決め手が 2 つ:

    反例 41 対はシートに **1 件も載っていない**（0/41）
    3 条項を切ってもシート点は **1354/1358 のまま**

⟹ **`SeqEmbT3` を壊す 3 条項はシートに 1 行も寄与していない。**
3 旗オフで `SeqEmbT3` の破れ **41 -> 0**、非標準の像も **177 -> 105**（改善）。
代償は `ImgClosedT` / `C1` だけ（lim=5 で 2 -> 4）。

⟹ **`OrderT3` を諦めないこと。** 変換器が 3 旗オフを基準にしたら、
`SeqEmbT3`（`OrderT3_iff_seqemb` で同値）を攻める道が開く。
そのときの母数は **`ST_TS` 展開閉包で `len ≥ 10` まで**（`gen3 ≤8` では見えない）。 -/

/-- `conv3` は列辞書式の順序埋め込み。 -/
def SeqEmbT3 (conv3 : TrioSeq → TrioSeq) : Prop :=
  ∀ {M N : TrioSeq}, ST_TS M → ST_TS N → (seqlex M N ↔ seqlex (conv3 M) (conv3 N))

/-- **`OrderT3` と `SeqEmbT3` は同値。** -/
theorem OrderT3_iff_seqemb {conv3 : TrioSeq → TrioSeq} :
    OrderT3 conv3 ↔ SeqEmbT3 conv3 := by
  constructor
  · intro hO M N hM hN
    by_cases h : M = N
    · subst h
      exact iff_of_false (seqlex_irrefl _) (seqlex_irrefl _)
    · exact ((olt_ST_iff_seqlex hM hN h).symm).trans (hO hM hN)
  · intro hE M N hM hN
    by_cases h : M = N
    · subst h
      exact iff_of_false (olt_irrefl _) (seqlex_irrefl _)
    · exact (olt_ST_iff_seqlex hM hN h).trans (hE hM hN)

end TRIO

#print axioms TRIO.not_olt_len_one_T
#print axioms TRIO.diag_cofinal_T
#print axioms TRIO.ST_D3_conv3_diag
#print axioms TRIO.ST_D3_descend
#print axioms TRIO.ST_D3_conv3
#print axioms TRIO.ST_D3_conv3_holds
#print axioms TRIO.Conv3.b2d3_diagSeqT
#print axioms TRIO.ConvDiagT3_b2d3
#print axioms TRIO.ST_D3_b2d3

#print axioms TRIO.seqlex_oper
#print axioms TRIO.ole_of_sle3
#print axioms TRIO.conv3_injective
#print axioms TRIO.ReindexT1_of_sandwich
#print axioms TRIO.ReindexT1_of_block
#print axioms TRIO.ST_D3_conv3_of_parts
#print axioms TRIO.OrderT3_of_read
#print axioms TRIO.OrderT3_iff_seqemb
