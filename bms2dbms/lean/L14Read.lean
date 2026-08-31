/-
課題 L14: **`read3` / `dok` の設計**（`OrderT3` の律速）。

`Dbms3.OrderT3_of_read`（**証明ずみ・3 行**）は

    ReadT3 read3 conv3   read3 (conv3 M) = translate M
    ImgDokT3 dok conv3   dok (conv3 M)
    ReadLexT3 read3 dok  dok の上で read3 は seqlex への順序同型
    ⟹ OrderT3 conv3

を与える。仕事は全部読み `read3` の側にある。この file はその**設計**である。
（`Dbms3.lean` は `lakefile.toml` の `roots` に入っていないので import できない。
`read3` / `dok` は `conv3` に依存しない純粋な関数・述語なので、`Term` だけを
import して単体で書ける。通ったら `Dbms3.lean` に移せばよい。）

## 1. 2 行の逐語版は 3 行では**原理的に不可能**（測って確かめた）

2 行の `readD`（`Dbms.lean:131`）は段を**そのまま**読む:

    readD (p :: r) first plev =
      if first ∧ p.2 = plev ∧ r.headI = p + (1,1) then readD r true plev   -- 影
      else P p.2 (readD 子 true p.2) (readD 兄弟 false p.2)

これで済むのは `convD` が本体の柱に BMS の段 `p.2` を**そのまま書く**からである。
3 行の `conv3` は

    e2 = s2                行 2 は**そのまま**
    e1 = 梯子の表から計算   行 1 は**そのままではない**

最小の反例が対角にある:

    M   = (0,0,0)(1,1,1)                    translate M = P 0 0 (P 1 1 Z Z) Z
    像  = (0,0,0)(1,0,0)(2,1,0)(3,2,1)
    像の (行1,行2) は (0,0) (0,0) (1,0) (2,1) で **(1,1) がどこにも無い**

⟹ 逐語読みでは `read3 (conv3 M) = translate M` は書けない。
**像の行 1 は BMS の添字ではなく「行 1 の木での順位」である。**

## 2. 設計: 影を捨てて、**順位に直して**から `translate`

    readMat B := rankify (survivors B true (0,0))
    read3 B   := translate (readMat B)

* `survivors` … `readD` と同じ再帰で影を捨てる。節は**2 つ**:
    - 行 1 の梯子 … `first ∧ (p の段) = plev ∧ 次 = p + (1,1,0)`
    - 行 2 の梯子 … `first ∧ p の行 2 = plev の行 2 ∧ 次 = p + (1,1,1)`
* `rankify` … 各行の値を**その行の木での順位**に置き換える。
  BMS 標準形の上では恒等なので、`readMat (conv3 M) = M` が言えれば
  `ReadT3` は無料になる。

## 3. 実測（`tools/probe_read3.py`、母集団は**真の `ST_TS` 展開閉包**）

    (INV) readMat (conv3 M) = M

| | 母数 | 一致 | **破れ** |
|---|---|---|---|
| `v<=4, len<=10` 本番 | 415218 | 406564 | **8654（2.1%）** |
| 陽性対照 1（影を捨てない） | 415218 | 36 | 415182 |
| 陽性対照 2（順位に直さない） | 415218 | 36 | 415182 |

⟹ **順位に直す段も影を捨てる段も、どちらも必須**（対照が両方とも落ちる）。

破れ 8654 の内訳（`v<=4, len<=9` の 44063 個で分解、破れ 973）:

    短い像（|conv3 M| < |M|）  239
    像は十分長い              734
    **縮約が発火した**         601   ← **一致した中に縮約ありは 0 個**
    縮約なし                   372

## 4. 判定: **この設計では `ReadT3` は出ない**（1 段落）

`conv3` の**縮約**が発火すると像が `M` より短くなる（実測 239 例）。`translate M`
の節点は `|M|` 個あるので、**1 列 1 節点で読むどんな `read3` でも
`read3 (conv3 M) = translate M` は成り立ちえない**。しかも縮約が発火した行列は
**一致が 1 つも無い**（601/601 が破れ）。縮約は捨てられない（止めるとシートが
1354 -> 1021 に落ちる）。残る 372 は影の節の**取り違え**で、局所の
「次 = `p + (1,1,1)`」だけでは本体の柱と梯子の柱を分けられないためである
（`okPlace` 相当の「その深さにその段を直に書けたか」を見ないと決まらない）。
⟹ **`read3` / `dok` の道は、縮約を読み戻せる `read3`（1 列を複数節点に開く）を
設計しないかぎり閉じている。** `OrderT3` には `SeqEmbT3`（`OrderT3_iff_seqemb`
で同値、読みを一切使わない）から攻めるほうが良い。
-/
import Term
import Seqlex

namespace TRIO
namespace L14

open Three

/-! ## 影を捨てる（`readD` と同じ再帰。節が 2 つ） -/

/-- `readD` の 3 行版の「影を捨てる」段。生き残った柱を**元の順**で返す。 -/
def survivors : TrioSeq → Bool → ℕ × ℕ → TrioSeq
  | [], _, _ => []
  | p :: r, first, plev =>
      if first = true ∧ (p.2.1, p.2.2) = plev ∧
          r.headI = ((p.1 + 1, p.2.1 + 1, p.2.2) : ℕ × ℕ × ℕ) then
        survivors r true plev
      else if first = true ∧ p.2.2 = plev.2 ∧
          r.headI = ((p.1 + 1, p.2.1 + 1, p.2.2 + 1) : ℕ × ℕ × ℕ) then
        survivors r true plev
      else
        p :: (survivors (r.takeWhile fun q => p.1 < q.1) true (p.2.1, p.2.2)
              ++ survivors (r.dropWhile fun q => p.1 < q.1) false (p.2.1, p.2.2))
  termination_by l => l.length
  decreasing_by
    all_goals simp only [List.length_cons]
    all_goals
      first
        | omega
        | exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
        | exact Nat.lt_succ_of_le (List.length_dropWhile_le _ _)

/-! ## 順位に直す（計算できる版の親） -/

/-- 行 `y` の親をたどる補助（燃料つき）。 -/
def climb (B : TrioSeq) (y : ℕ) (pf : ℕ → Option ℕ) (x : ℕ) :
    ℕ → Option ℕ → Option ℕ
  | 0, _ => none
  | _, none => none
  | (f + 1), some q =>
      if entry B y q < entry B y x then some q else climb B y pf x f (pf q)

/-- 行 `y` の親（`Trio.parent` の計算できる版）。 -/
def parB (B : TrioSeq) : ℕ → ℕ → Option ℕ
  | 0, x => ((List.range x).reverse).find?
      (fun p => decide (entry B 0 p < entry B 0 x))
  | (y + 1), x => climb B (y + 1) (parB B y) x x (parB B y x)

/-- 行 `y` の木での順位（燃料つき）。 -/
def rankB (B : TrioSeq) (y : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | (f + 1), j => match parB B y j with
      | none => 0
      | some q => rankB B y f q + 1

/-- 各行の値を「その行の木での順位」に置き換える。BMS 標準形の上では恒等。 -/
def rankify (B : TrioSeq) : TrioSeq :=
  (List.range B.length).map fun j =>
    ((rankB B 0 B.length j, rankB B 1 B.length j, rankB B 2 B.length j) :
      ℕ × ℕ × ℕ)

/-- DBMS の行列を BMS の行列として読み戻す。 -/
def readMat (B : TrioSeq) : TrioSeq := rankify (survivors B true (0, 0))

/-- **DBMS の読み**。`ReadT3` の `read3` の候補。 -/
def read3 (B : TrioSeq) : Three := translate (readMat B)

/-- **像の作法**（`ImgDokT3` の `dok` の候補）。`blockok 0` に加えて
「影を捨てて順位に直したものが BMS 標準形である」ことを要求する。
⚠ §4 のとおり `conv3` の像はこれを 2.1% で満たさない。 -/
def dok (B : TrioSeq) : Prop := blockok 0 B ∧ ST_TS (readMat B)

/-! ## 対角での確認（`#guard`）

    conv3 (diagSeqT 0 v) = ddiagSeqT (v+2)   （`Dbms3.ConvDiagT3_b2d3`）

なので、対角の像を読み戻すと BMS の対角に戻るはずである。 -/

#guard readMat [(0,0,0)] = [(0,0,0)]
#guard readMat [(0,0,0), (1,0,0), (2,1,0), (3,2,1)] = [(0,0,0), (1,1,1)]
#guard readMat [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1)]
    = [(0,0,0), (1,1,1), (2,2,1)]
#guard readMat [(0,0,0), (1,0,0), (2,1,0), (3,2,1), (4,3,1), (5,4,1)]
    = [(0,0,0), (1,1,1), (2,2,1), (3,3,1)]

-- 対角では読みが `translate` と一致する。
#guard read3 [(0,0,0), (1,0,0), (2,1,0), (3,2,1)] = translate [(0,0,0), (1,1,1)]

end L14
end TRIO
