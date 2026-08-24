/-
DBMS（Dimensional BMS）の 2 行版と、BMS -> DBMS の変換関数。

BMS と DBMS は**展開規則が完全に同一**で、違うのは標準形の対角だけ。

    対角 diag[x][y]     BMS: x        DBMS: max(x-y, 0)

2 行なら BMS の対角は (0,0)(1,1)(2,2)... 、DBMS の対角は (0,0)(1,0)(2,1)(3,2)... 。
行 y は位置 y からしか立ち上がれないので、DBMS の列は「0 でない成分が厳密に減る」。

目標は ψ_0(Ω_ω) 未満、すなわち **2 行 BMS の全体**で変換が正しいこと。
その範囲で必要な機構は「階段」と「逐語重複の削除」だけである
（深さ規則・梯子の敷き直し・後始末はどれも 3 行でしか要らない。
tools/dbms/verify_gen.py --rows2 で生成した 4668 個で確認済み）。

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

/-! ## 2. 親（計算できる形）

`Pair/Pss.lean` の `nextrel0` / `nextrel1` は命題なので、変換を定義するために
計算できる版を置く。`pim`（yaBMS の C 実装と同じ）と同じもの:

* 行 0 の親 = `p < x` で `M[p].1 < M[x].1` となる最大の `p`
* 行 1 の親 = 行 0 の親の鎖を遡り、最初に `M[p].2 < M[x].2` となる `p`
-/

/-- 行 0 の親。無ければ `none`。 -/
def par0 (M : PairSeq) (x : ℕ) : Option ℕ :=
  let a := (M.getD x (0, 0)).1
  let rec go : ℕ → Option ℕ
    | 0 => none
    | Nat.succ p => if (M.getD p (0, 0)).1 < a then some p else go p
  go x

/-- 行 0 の親の鎖を `fuel` 段まで遡り、最初に行 1 の値が `b` 未満になる位置。 -/
def climb (M : PairSeq) (b : ℕ) : ℕ → Option ℕ → Option ℕ
  | _, none => none
  | 0, some _ => none
  | Nat.succ fuel, some p =>
      if (M.getD p (0, 0)).2 < b then some p else climb M b fuel (par0 M p)

/-- 行 1 の親。行 1 の値が `0` なら親なし。 -/
def par1 (M : PairSeq) (x : ℕ) : Option ℕ :=
  let b := (M.getD x (0, 0)).2
  if b = 0 then none else climb M b (x + 1) (par0 M x)

/-! ## 3. 変換（階段）

元の列 `x` を 1 本ずつ写す。段が足りないところには**影の列**を挿す。
影は親ごとに 1 回だけ作って使い回す（同じ親に吊るす 2 本目の列は既存の影に乗る）。

2 行では列 `(a,b)` の像はこうなる。

* `(0,0)`      -> `(0,0)`
* `b = 0`      -> `(img(行0の親).1 + 1, 0)`
* `b > 0`      -> 影 `s` を用意して `(max (img(行0の親).1 + 1) (s.1 + 1), s.2 + 1)`
  影 `s` は「行 1 の親の像」。ただしその像が `(0,0)` のときだけ、
  新しい列 `(1,0)` を挿してそれを影にする。
-/

/-- 変換の途中状態。 -/
structure CSt where
  /-- ここまでに書いた DBMS の列（順方向）。 -/
  out : PairSeq
  /-- 元の列 `i` の像（順方向、`i` 番目が元の列 `i` に対応）。 -/
  img : PairSeq
  /-- 影を作った親の位置と、その影の値。 -/
  sh : List (ℕ × ℕ × ℕ)
  deriving Repr

/-- 空の状態。 -/
def CSt.init : CSt := ⟨[], [], []⟩

/-- 親 `p` の影を引く。無ければ `none`。 -/
def CSt.lookSh (s : CSt) (p : ℕ) : Option (ℕ × ℕ) :=
  (s.sh.find? (fun t => t.1 = p)).map (fun t => t.2)

/-- 位置 `p` の像。 -/
def CSt.imgAt (s : CSt) : Option ℕ → ℕ × ℕ
  | none => (0, 0)
  | some p => s.img.getD p (0, 0)

/-- 列 `x` を 1 本写す。 -/
def convStep (M : PairSeq) (s : CSt) (x : ℕ) : CSt :=
  let c := M.getD x (0, 0)
  if c = (0, 0) then
    ⟨s.out ++ [(0, 0)], s.img ++ [(0, 0)], s.sh⟩
  else if c.2 = 0 then
    let v : ℕ × ℕ := ((s.imgAt (par0 M x)).1 + 1, 0)
    ⟨s.out ++ [v], s.img ++ [v], s.sh⟩
  else
    let p1 := par1 M x
    let pv := s.imgAt p1
    -- 影: 親の像がそのまま使えるか、`(1,0)` を挿すか
    match p1, s.lookSh (p1.getD 0) with
    | some p, some sv =>
        let v : ℕ × ℕ := (max ((s.imgAt (par0 M x)).1 + 1) (sv.1 + 1), sv.2 + 1)
        ⟨s.out ++ [v], s.img ++ [v], s.sh⟩
    | some p, none =>
        if 1 ≤ pv.1 then
          let v : ℕ × ℕ := (max ((s.imgAt (par0 M x)).1 + 1) (pv.1 + 1), pv.2 + 1)
          ⟨s.out ++ [v], s.img ++ [v], (p, pv) :: s.sh⟩
        else
          let sv : ℕ × ℕ := (pv.1 + 1, 0)
          let v : ℕ × ℕ := (max ((s.imgAt (par0 M x)).1 + 1) (sv.1 + 1), sv.2 + 1)
          ⟨s.out ++ [sv, v], s.img ++ [v], (p, sv) :: s.sh⟩
    | none, _ =>
        let v : ℕ × ℕ := ((s.imgAt (par0 M x)).1 + 1, 1)
        ⟨s.out ++ [v], s.img ++ [v], s.sh⟩

/-- 階段。影の列を挿しながら元の列を 1 本ずつ写す。 -/
def stair (M : PairSeq) : PairSeq :=
  ((List.range M.length).foldl (convStep M) CSt.init).out

/-! ### 動作確認 -/

-- `(0,0)(1,1)` -> `(0,0)(1,0)(2,1)`
#guard stair [(0,0),(1,1)] = [(0,0),(1,0),(2,1)]
-- 2 本目の `(1,1)` は既存の影に乗る
#guard stair [(0,0),(1,1),(1,1)] = [(0,0),(1,0),(2,1),(2,1)]
-- `(0,0)` で区切ると影が作り直される
#guard stair [(0,0),(1,1),(0,0),(1,1)] = [(0,0),(1,0),(2,1),(0,0),(1,0),(2,1)]
-- 対角
#guard stair [(0,0),(1,1),(2,2)] = [(0,0),(1,0),(2,1),(3,2)]
-- 行 1 が 0 の列はそのまま
#guard stair [(0,0),(1,1),(1,0)] = [(0,0),(1,0),(2,1),(1,0)]
#guard stair [(0,0),(1,1),(1,0),(2,1)] = [(0,0),(1,0),(2,1),(1,0),(2,1)]

/-! ## 4. DBMS の読み `translateD`

`Pair/Term.lean` の `translate` は「行 1 = 添字、行 0 = 森」で BMS の行列を項に読む。
DBMS では対角が `(j, j-1)` なので、読み方が変わる。264 件のシートの対で確かめた形:

* 添字は行 1、森は行 0（ここは同じ）
* **`(+1,+1)` で続く連**（DBMS の対角の段）は、添字を引数側に入れ子にした鎖になる。
  例: `(1,0)(2,1)(3,2)` は `P1(P2(Z,Z),Z)`
* 連を取るのは「親の最初の子」かつ「**底の段が親と同じ**」ときだけ。
  段が下がっていればそれは影ではなく新しい加算項の頭
* 連のあとに続く列は、その**行 0（深さ）に対応する段**のノードの後続になる。
  連より浅い列は連全体の後続
* 連の長さが 1 で、兄弟が尽きたあと**同じ深さで段が下がる**列が来るときは、
  その連は BMS 側で「梯子」と「本体」の二役を兼ねている（縮約で 1 本に潰れている）ので
  `P 影の段 (頂上から読み直したもの) (残り)` と開き直す

Python 版は `tools/dbms/translateD_search.py` の `mk_chain4`（264/264）。
-/

/-- `p` から始まる連の長さ。`(+1,+1)` で続く限り伸びる。 -/
def runLen (p : ℕ × ℕ) : PairSeq → ℕ
  | [] => 0
  | q :: r => if q.1 = p.1 + 1 ∧ q.2 = p.2 + 1 then runLen q r + 1 else 0

/-- 連の頂上。 -/
def runTop (p : ℕ × ℕ) : PairSeq → ℕ × ℕ
  | [] => p
  | q :: r => if q.1 = p.1 + 1 ∧ q.2 = p.2 + 1 then runTop q r else p

/-- 連は先頭からの**接頭辞**である。あとで `seqlex` との整合を示すときに効く。 -/
theorem runLen_le (p : ℕ × ℕ) (l : PairSeq) : runLen p l ≤ l.length := by
  induction l generalizing p with
  | nil => simp [runLen]
  | cons q r ih =>
    by_cases h : q.1 = p.1 + 1 ∧ q.2 = p.2 + 1
    · simpa [runLen, h] using Nat.succ_le_succ (ih q)
    · simp [runLen, h]

/-! ### 動作確認（連） -/

#guard runLen (1, 0) [(2,1),(3,2)] = 2
#guard runTop (1, 0) [(2,1),(3,2)] = (3, 2)
#guard runLen (1, 0) [(2,1),(3,0)] = 1
#guard runLen (0, 0) [(1,0)] = 0

/-! ### translateD 本体 -/

/-- 深さ `a` の子（引数）になる先頭部分の長さ。 -/
def argLen (a : ℕ) : PairSeq → ℕ
  | [] => 0
  | q :: r => if a < q.1 then argLen a r + 1 else 0

/-- 同じ深さ・同じ段の兄弟の数。 -/
def sibLen (t : ℕ × ℕ) : PairSeq → ℕ
  | [] => 0
  | q :: r => if q.1 = t.1 ∧ q.2 = t.2 then sibLen t r + 1 else 0

/-- 深さが `a` 以上で続く先頭部分の長さ。 -/
def deepLen (a : ℕ) : PairSeq → ℕ
  | [] => 0
  | q :: r => if a ≤ q.1 then deepLen a r + 1 else 0

/-- 長さの上界（停止性に使う）。 -/
theorem argLen_le (a : ℕ) (l : PairSeq) : argLen a l ≤ l.length := by
  induction l with
  | nil => simp [argLen]
  | cons q r ih =>
    by_cases h : a < q.1
    · simpa [argLen, h] using Nat.succ_le_succ ih
    · simp [argLen, h]

theorem sibLen_le (t : ℕ × ℕ) (l : PairSeq) : sibLen t l ≤ l.length := by
  induction l with
  | nil => simp [sibLen]
  | cons q r ih =>
    by_cases h : q.1 = t.1 ∧ q.2 = t.2
    · simpa [sibLen, h] using Nat.succ_le_succ ih
    · simp [sibLen, h]

theorem deepLen_le (a : ℕ) (l : PairSeq) : deepLen a l ≤ l.length := by
  induction l with
  | nil => simp [deepLen]
  | cons q r ih =>
    by_cases h : a ≤ q.1
    · simpa [deepLen, h] using Nat.succ_le_succ ih
    · simp [deepLen, h]

/-- 連の列そのもの `[c_1, …, c_k]`（先頭 `p` は含まない）。 -/
def runList (p : ℕ × ℕ) : PairSeq → PairSeq
  | [] => []
  | q :: r => if q.1 = p.1 + 1 ∧ q.2 = p.2 + 1 then q :: runList q r else []

theorem runList_length (p : ℕ × ℕ) (l : PairSeq) : (runList p l).length ≤ l.length := by
  induction l generalizing p with
  | nil => simp [runList]
  | cons q r ih =>
    by_cases h : q.1 = p.1 + 1 ∧ q.2 = p.2 + 1
    · simpa [runList, h] using Nat.succ_le_succ (ih q)
    · simp [runList, h]

open YAPSS.Three in
/-- 同じ段のノードを `n` 個、後続の向きに重ねる（連の兄弟ぶん）。 -/
def wrapN : ℕ → ℕ → Three → Three
  | 0, _, t => t
  | Nat.succ n, s, t => P s Z (wrapN n s t)

open YAPSS.Three in
mutual

/-- DBMS の読み（燃料つき）。`first` は「親の最初の子か」、`plev` は「親の段」。

燃料は列の本数を渡す。`transD` がそれを噛ませる。停止性を構造で示すかわりに
燃料で回すのは、連の切れ目が後続を見て決まるため（`runLen`）で、
証明の側では `transD_spec`（燃料が足りていれば値が変わらない）で吸収する。 -/
def transDF : ℕ → PairSeq → Bool → ℕ → Three
  | _, [], _, _ => Z
  | 0, _, _, _ => Z
  | Nat.succ fuel, p :: rest, first, plev =>
      let k := if first = true ∧ p.2 = plev then runLen p rest else 0
      let top := if k = 0 then p else runTop p rest
      let tail := rest.drop k
      let i := argLen top.1 tail
      let arg := transDF fuel (tail.take i) true top.2
      let after := tail.drop i
      let j := sibLen top after
      let r2 := after.drop j
      if k = 1 ∧ r2 ≠ [] ∧ (r2.headI).1 = top.1 ∧ (r2.headI).2 < top.2 then
        -- 連が「梯子 + 本体」の二役。頂上から読み直す
        let m := deepLen top.1 r2
        let inner := transDF fuel (top :: (tail.take i ++ after.take j ++ r2.take m)) true p.2
        P top.2 arg
          (wrapN j top.2 (P p.2 inner (transDF fuel (r2.drop m) false plev)))
      else if k ≤ 1 then
        -- 段が 1 つなら振り分けるものがない。残りは全部この段の後続
        P top.2 arg (transDF fuel after false top.2)
      else
        -- 連の各段に、後続を深さで振り分けて鎖にする
        let n0 := deepLen top.1 after
        let node0 := P top.2 arg (transDF fuel (after.take n0) false top.2)
        chainDF fuel ((runList p rest).dropLast.reverse) node0 (after.drop n0) plev

/-- 連の途中の段を、内側から外へ積む。後続はその段の深さで切り分ける。
一番外の段には、連より浅い列（残り全部）が後続として付く。 -/
def chainDF : ℕ → PairSeq → Three → PairSeq → ℕ → Three
  | _, [], node, _, _ => node
  | 0, _, node, _, _ => node
  | Nat.succ fuel, [c], node, rest, plev =>
      P c.2 node (transDF fuel rest false plev)
  | Nat.succ fuel, c :: cs, node, rest, plev =>
      let n := deepLen c.1 rest
      chainDF fuel cs (P c.2 node (transDF fuel (rest.take n) false c.2))
        (rest.drop n) plev

end

/-- DBMS の読み。 -/
def transD (l : PairSeq) : Three := transDF (l.length + 1) l true 0

/-! ### 動作確認（264 件のうちの代表） -/

open YAPSS.Three in
#guard transD [(0,0)] = P 0 Z Z
open YAPSS.Three in
#guard transD [(0,0),(1,0),(2,1)] = P 0 (P 1 Z Z) Z
open YAPSS.Three in
#guard transD [(0,0),(1,0)] = P 0 (P 0 Z Z) Z
open YAPSS.Three in
#guard transD [(0,0),(1,0),(2,1),(3,2)] = P 0 (P 1 (P 2 Z Z) Z) Z
open YAPSS.Three in
#guard transD [(0,0),(1,0),(2,1),(2,0)]
    = P 0 (P 1 Z (P 0 (P 1 Z (P 0 Z Z)) Z)) Z

/-! ### 264 件の全数検査

シートの 2 行の対 264 件すべてで、`transD`（DBMS の読み）が
`translate`（BMS の読み）と一致することを確かめる。
値は `tools/dbms/translateD_search.py` の `mk_chain4`（264/264）から生成した。
シート 128/129 行の DBMS 列の誤記は `check_sheet` の補正を反映してある。
-/
open YAPSS.Three in
section
open YAPSS.Three
#guard transD [(0,0)] = P 0 (Z) (Z)
#guard transD [(0,0),(0,0)] = P 0 (Z) (P 0 (Z) (Z))
#guard transD [(0,0),(0,0),(0,0)] = P 0 (Z) (P 0 (Z) (P 0 (Z) (Z)))
#guard transD [(0,0),(0,0),(0,0),(0,0)] = P 0 (Z) (P 0 (Z) (P 0 (Z) (P 0 (Z) (Z))))
#guard transD [(0,0),(0,0),(0,0),(0,0),(0,0)] = P 0 (Z) (P 0 (Z) (P 0 (Z) (P 0 (Z) (P 0 (Z) (Z)))))
#guard transD [(0,0),(1,0)] = P 0 (P 0 (Z) (Z)) (Z)
#guard transD [(0,0),(1,0),(0,0)] = P 0 (P 0 (Z) (Z)) (P 0 (Z) (Z))
#guard transD [(0,0),(1,0),(0,0),(0,0)] = P 0 (P 0 (Z) (Z)) (P 0 (Z) (P 0 (Z) (Z)))
#guard transD [(0,0),(1,0),(0,0),(0,0),(0,0)] = P 0 (P 0 (Z) (Z)) (P 0 (Z) (P 0 (Z) (P 0 (Z) (Z))))
#guard transD [(0,0),(1,0),(0,0),(1,0)] = P 0 (P 0 (Z) (Z)) (P 0 (P 0 (Z) (Z)) (Z))
#guard transD [(0,0),(1,0),(0,0),(1,0),(0,0)] = P 0 (P 0 (Z) (Z)) (P 0 (P 0 (Z) (Z)) (P 0 (Z) (Z)))
#guard transD [(0,0),(1,0),(0,0),(1,0),(0,0),(1,0)] = P 0 (P 0 (Z) (Z)) (P 0 (P 0 (Z) (Z)) (P 0 (P 0 (Z) (Z)) (Z)))
#guard transD [(0,0),(1,0),(1,0)] = P 0 (P 0 (Z) (P 0 (Z) (Z))) (Z)
#guard transD [(0,0),(1,0),(1,0),(0,0)] = P 0 (P 0 (Z) (P 0 (Z) (Z))) (P 0 (Z) (Z))
#guard transD [(0,0),(1,0),(1,0),(0,0),(1,0)] = P 0 (P 0 (Z) (P 0 (Z) (Z))) (P 0 (P 0 (Z) (Z)) (Z))
#guard transD [(0,0),(1,0),(1,0),(0,0),(1,0),(1,0)] = P 0 (P 0 (Z) (P 0 (Z) (Z))) (P 0 (P 0 (Z) (P 0 (Z) (Z))) (Z))
#guard transD [(0,0),(1,0),(1,0),(1,0)] = P 0 (P 0 (Z) (P 0 (Z) (P 0 (Z) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,0)] = P 0 (P 0 (P 0 (Z) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,0),(0,0)] = P 0 (P 0 (P 0 (Z) (Z)) (Z)) (P 0 (Z) (Z))
#guard transD [(0,0),(1,0),(2,0),(0,0),(1,0)] = P 0 (P 0 (P 0 (Z) (Z)) (Z)) (P 0 (P 0 (Z) (Z)) (Z))
#guard transD [(0,0),(1,0),(2,0),(0,0),(1,0),(1,0)] = P 0 (P 0 (P 0 (Z) (Z)) (Z)) (P 0 (P 0 (Z) (P 0 (Z) (Z))) (Z))
#guard transD [(0,0),(1,0),(2,0),(0,0),(1,0),(2,0)] = P 0 (P 0 (P 0 (Z) (Z)) (Z)) (P 0 (P 0 (P 0 (Z) (Z)) (Z)) (Z))
#guard transD [(0,0),(1,0),(2,0),(1,0)] = P 0 (P 0 (P 0 (Z) (Z)) (P 0 (Z) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,0),(1,0),(1,0)] = P 0 (P 0 (P 0 (Z) (Z)) (P 0 (Z) (P 0 (Z) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,0),(1,0),(2,0)] = P 0 (P 0 (P 0 (Z) (Z)) (P 0 (P 0 (Z) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,0),(2,0)] = P 0 (P 0 (P 0 (Z) (P 0 (Z) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,0),(3,0)] = P 0 (P 0 (P 0 (P 0 (Z) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,0),(3,0),(4,0)] = P 0 (P 0 (P 0 (P 0 (P 0 (Z) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1)] = P 0 (P 1 (Z) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(0,0)] = P 0 (P 1 (Z) (Z)) (P 0 (Z) (Z))
#guard transD [(0,0),(1,0),(2,1),(0,0),(1,0)] = P 0 (P 1 (Z) (Z)) (P 0 (P 0 (Z) (Z)) (Z))
#guard transD [(0,0),(1,0),(2,1),(0,0),(1,0),(2,0)] = P 0 (P 1 (Z) (Z)) (P 0 (P 0 (P 0 (Z) (Z)) (Z)) (Z))
#guard transD [(0,0),(1,0),(2,1),(0,0),(1,0),(2,1)] = P 0 (P 1 (Z) (Z)) (P 0 (P 1 (Z) (Z)) (Z))
#guard transD [(0,0),(1,0),(2,1),(0,0),(1,0),(2,1),(0,0),(1,0),(2,1)] = P 0 (P 1 (Z) (Z)) (P 0 (P 1 (Z) (Z)) (P 0 (P 1 (Z) (Z)) (Z)))
#guard transD [(0,0),(1,0),(2,1),(1,0)] = P 0 (P 1 (Z) (P 0 (Z) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(1,0),(0,0),(1,0),(2,1)] = P 0 (P 1 (Z) (P 0 (Z) (Z))) (P 0 (P 1 (Z) (Z)) (Z))
#guard transD [(0,0),(1,0),(2,1),(1,0),(0,0),(1,0),(2,1),(1,0)] = P 0 (P 1 (Z) (P 0 (Z) (Z))) (P 0 (P 1 (Z) (P 0 (Z) (Z))) (Z))
#guard transD [(0,0),(1,0),(2,1),(1,0),(1,0)] = P 0 (P 1 (Z) (P 0 (Z) (P 0 (Z) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,1),(1,0),(2,0)] = P 0 (P 1 (Z) (P 0 (P 0 (Z) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(1,0),(2,0),(3,0)] = P 0 (P 1 (Z) (P 0 (P 0 (P 0 (Z) (Z)) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(1,0),(2,1)] = P 0 (P 1 (Z) (P 0 (P 1 (Z) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(1,0),(2,1),(1,0)] = P 0 (P 1 (Z) (P 0 (P 1 (Z) (Z)) (P 0 (Z) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,1),(1,0),(2,1),(1,0),(2,0)] = P 0 (P 1 (Z) (P 0 (P 1 (Z) (Z)) (P 0 (P 0 (Z) (Z)) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,1),(1,0),(2,1),(1,0),(2,1)] = P 0 (P 1 (Z) (P 0 (P 1 (Z) (Z)) (P 0 (P 1 (Z) (Z)) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,0)] = P 0 (P 1 (Z) (P 0 (P 1 (Z) (P 0 (Z) (Z))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,0),(1,0)] = P 0 (P 1 (Z) (P 0 (P 1 (Z) (P 0 (Z) (Z))) (P 0 (Z) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,0),(1,0),(2,1)] = P 0 (P 1 (Z) (P 0 (P 1 (Z) (P 0 (Z) (Z))) (P 0 (P 1 (Z) (Z)) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,0),(1,0),(2,1),(2,0)] = P 0 (P 1 (Z) (P 0 (P 1 (Z) (P 0 (Z) (Z))) (P 0 (P 1 (Z) (P 0 (Z) (Z))) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,0),(2,0)] = P 0 (P 1 (Z) (P 0 (P 1 (Z) (P 0 (Z) (P 0 (Z) (Z)))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,0),(3,0)] = P 0 (P 1 (Z) (P 0 (P 1 (Z) (P 0 (P 0 (Z) (Z)) (Z))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,0),(3,1)] = P 0 (P 1 (Z) (P 0 (P 1 (Z) (P 0 (P 1 (Z) (Z)) (Z))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,0),(3,1),(2,0)] = P 0 (P 1 (Z) (P 0 (P 1 (Z) (P 0 (P 1 (Z) (Z)) (P 0 (Z) (Z)))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,0),(3,1),(2,0),(3,1)] = P 0 (P 1 (Z) (P 0 (P 1 (Z) (P 0 (P 1 (Z) (Z)) (P 0 (P 1 (Z) (Z)) (Z)))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,0),(3,1),(3,0)] = P 0 (P 1 (Z) (P 0 (P 1 (Z) (P 0 (P 1 (Z) (P 0 (Z) (Z))) (Z))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,0),(3,1),(3,0),(3,0)] = P 0 (P 1 (Z) (P 0 (P 1 (Z) (P 0 (P 1 (Z) (P 0 (Z) (P 0 (Z) (Z)))) (Z))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,0),(3,1),(3,0),(4,0)] = P 0 (P 1 (Z) (P 0 (P 1 (Z) (P 0 (P 1 (Z) (P 0 (P 0 (Z) (Z)) (Z))) (Z))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,0),(3,1),(3,0),(4,1)] = P 0 (P 1 (Z) (P 0 (P 1 (Z) (P 0 (P 1 (Z) (P 0 (P 1 (Z) (Z)) (Z))) (Z))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,1)] = P 0 (P 1 (Z) (P 1 (Z) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,1),(0,0)] = P 0 (P 1 (Z) (P 1 (Z) (Z))) (P 0 (Z) (Z))
#guard transD [(0,0),(1,0),(2,1),(2,1),(0,0),(1,0),(2,1),(2,1)] = P 0 (P 1 (Z) (P 1 (Z) (Z))) (P 0 (P 1 (Z) (P 1 (Z) (Z))) (Z))
#guard transD [(0,0),(1,0),(2,1),(2,1),(1,0)] = P 0 (P 1 (Z) (P 1 (Z) (P 0 (Z) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,1),(1,0),(2,1),(2,1)] = P 0 (P 1 (Z) (P 1 (Z) (P 0 (P 1 (Z) (P 1 (Z) (Z))) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,1),(2,0)] = P 0 (P 1 (Z) (P 1 (Z) (P 0 (P 1 (Z) (P 1 (Z) (P 0 (Z) (Z)))) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,1),(2,0),(3,1),(3,1)] = P 0 (P 1 (Z) (P 1 (Z) (P 0 (P 1 (Z) (P 1 (Z) (P 0 (P 1 (Z) (P 1 (Z) (Z))) (Z)))) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,1),(2,1)] = P 0 (P 1 (Z) (P 1 (Z) (P 1 (Z) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,1),(2,1),(2,1),(2,1)] = P 0 (P 1 (Z) (P 1 (Z) (P 1 (Z) (P 1 (Z) (Z))))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0)] = P 0 (P 1 (P 0 (Z) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(0,0)] = P 0 (P 1 (P 0 (Z) (Z)) (Z)) (P 0 (Z) (Z))
#guard transD [(0,0),(1,0),(2,1),(3,0),(0,0),(1,0),(2,1),(3,0)] = P 0 (P 1 (P 0 (Z) (Z)) (Z)) (P 0 (P 1 (P 0 (Z) (Z)) (Z)) (Z))
#guard transD [(0,0),(1,0),(2,1),(3,0),(1,0)] = P 0 (P 1 (P 0 (Z) (Z)) (P 0 (Z) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(1,0),(2,1),(3,0)] = P 0 (P 1 (P 0 (Z) (Z)) (P 0 (P 1 (P 0 (Z) (Z)) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(2,0)] = P 0 (P 1 (P 0 (Z) (Z)) (P 0 (P 1 (P 0 (Z) (Z)) (P 0 (Z) (Z))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(2,0),(3,1),(4,0)] = P 0 (P 1 (P 0 (Z) (Z)) (P 0 (P 1 (P 0 (Z) (Z)) (P 0 (P 1 (P 0 (Z) (Z)) (Z)) (Z))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(2,1)] = P 0 (P 1 (P 0 (Z) (Z)) (P 1 (Z) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(2,1),(2,1)] = P 0 (P 1 (P 0 (Z) (Z)) (P 1 (Z) (P 1 (Z) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(2,1),(3,0)] = P 0 (P 1 (P 0 (Z) (Z)) (P 1 (P 0 (Z) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(3,0)] = P 0 (P 1 (P 0 (Z) (P 0 (Z) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(4,0)] = P 0 (P 1 (P 0 (P 0 (Z) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(4,1)] = P 0 (P 1 (P 0 (P 1 (Z) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(4,1),(2,1)] = P 0 (P 1 (P 0 (P 1 (Z) (Z)) (Z)) (P 1 (Z) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(4,1),(2,1),(3,0),(4,1)] = P 0 (P 1 (P 0 (P 1 (Z) (Z)) (Z)) (P 1 (P 0 (P 1 (Z) (Z)) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(4,1),(3,0)] = P 0 (P 1 (P 0 (P 1 (Z) (Z)) (P 0 (Z) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(4,1),(3,0),(4,1)] = P 0 (P 1 (P 0 (P 1 (Z) (Z)) (P 0 (P 1 (Z) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(4,1),(4,0)] = P 0 (P 1 (P 0 (P 1 (Z) (P 0 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(4,1),(4,0),(5,1)] = P 0 (P 1 (P 0 (P 1 (Z) (P 0 (P 1 (Z) (Z)) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(4,1),(4,1)] = P 0 (P 1 (P 0 (P 1 (Z) (P 1 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(4,1),(5,0)] = P 0 (P 1 (P 0 (P 1 (P 0 (Z) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,0),(4,1),(5,0),(6,1)] = P 0 (P 1 (P 0 (P 1 (P 0 (P 1 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1)] = P 0 (P 1 (P 1 (Z) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(0,0)] = P 0 (P 1 (P 1 (Z) (Z)) (Z)) (P 0 (Z) (Z))
#guard transD [(0,0),(1,0),(2,1),(3,1),(0,0),(1,0),(2,1),(3,1)] = P 0 (P 1 (P 1 (Z) (Z)) (Z)) (P 0 (P 1 (P 1 (Z) (Z)) (Z)) (Z))
#guard transD [(0,0),(1,0),(2,1),(3,1),(1,0)] = P 0 (P 1 (P 1 (Z) (Z)) (P 0 (Z) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(1,0),(2,1),(3,1)] = P 0 (P 1 (P 1 (Z) (Z)) (P 0 (P 1 (P 1 (Z) (Z)) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(2,0)] = P 0 (P 1 (P 1 (Z) (Z)) (P 0 (P 1 (P 1 (Z) (Z)) (P 0 (Z) (Z))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(2,0),(3,1),(4,1)] = P 0 (P 1 (P 1 (Z) (Z)) (P 0 (P 1 (P 1 (Z) (Z)) (P 0 (P 1 (P 1 (Z) (Z)) (Z)) (Z))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(2,1)] = P 0 (P 1 (P 1 (Z) (Z)) (P 1 (Z) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(2,1),(2,1)] = P 0 (P 1 (P 1 (Z) (Z)) (P 1 (Z) (P 1 (Z) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(2,1),(3,0)] = P 0 (P 1 (P 1 (Z) (Z)) (P 1 (P 0 (Z) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(2,1),(3,0),(4,1)] = P 0 (P 1 (P 1 (Z) (Z)) (P 1 (P 0 (P 1 (Z) (Z)) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(2,1),(3,0),(4,1),(5,1)] = P 0 (P 1 (P 1 (Z) (Z)) (P 1 (P 0 (P 1 (P 1 (Z) (Z)) (Z)) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(2,1),(3,0),(4,1),(5,1),(3,0)] = P 0 (P 1 (P 1 (Z) (Z)) (P 1 (P 0 (P 1 (P 1 (Z) (Z)) (Z)) (P 0 (Z) (Z))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(2,1),(3,0),(4,1),(5,1),(3,0),(4,1),(5,1)] = P 0 (P 1 (P 1 (Z) (Z)) (P 1 (P 0 (P 1 (P 1 (Z) (Z)) (Z)) (P 0 (P 1 (P 1 (Z) (Z)) (Z)) (Z))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(2,1),(3,0),(4,1),(5,1),(4,0)] = P 0 (P 1 (P 1 (Z) (Z)) (P 1 (P 0 (P 1 (P 1 (Z) (Z)) (P 0 (Z) (Z))) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(2,1),(3,0),(4,1),(5,1),(4,0),(5,1),(6,1)] = P 0 (P 1 (P 1 (Z) (Z)) (P 1 (P 0 (P 1 (P 1 (Z) (Z)) (P 0 (P 1 (P 1 (Z) (Z)) (Z)) (Z))) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(2,1),(3,0),(4,1),(5,1),(4,1)] = P 0 (P 1 (P 1 (Z) (Z)) (P 1 (P 0 (P 1 (P 1 (Z) (Z)) (P 1 (Z) (Z))) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(2,1),(3,1)] = P 0 (P 1 (P 1 (Z) (Z)) (P 1 (P 1 (Z) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(2,1),(3,1),(2,1),(3,1)] = P 0 (P 1 (P 1 (Z) (Z)) (P 1 (P 1 (Z) (Z)) (P 1 (P 1 (Z) (Z)) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,0)] = P 0 (P 1 (P 1 (Z) (P 0 (Z) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,0),(3,0)] = P 0 (P 1 (P 1 (Z) (P 0 (Z) (P 0 (Z) (Z)))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,0),(4,0)] = P 0 (P 1 (P 1 (Z) (P 0 (P 0 (Z) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,0),(4,1)] = P 0 (P 1 (P 1 (Z) (P 0 (P 1 (Z) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,0),(4,1),(4,1)] = P 0 (P 1 (P 1 (Z) (P 0 (P 1 (Z) (P 1 (Z) (Z))) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,0),(4,1),(5,0)] = P 0 (P 1 (P 1 (Z) (P 0 (P 1 (P 0 (Z) (Z)) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,0),(4,1),(5,0),(6,1)] = P 0 (P 1 (P 1 (Z) (P 0 (P 1 (P 0 (P 1 (Z) (Z)) (Z)) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,0),(4,1),(5,1)] = P 0 (P 1 (P 1 (Z) (P 0 (P 1 (P 1 (Z) (Z)) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,0),(4,1),(5,1),(4,1),(5,1)] = P 0 (P 1 (P 1 (Z) (P 0 (P 1 (P 1 (Z) (Z)) (P 1 (P 1 (Z) (Z)) (Z))) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,0),(4,1),(5,1),(5,0)] = P 0 (P 1 (P 1 (Z) (P 0 (P 1 (P 1 (Z) (P 0 (Z) (Z))) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,0),(4,1),(5,1),(5,0),(6,1)] = P 0 (P 1 (P 1 (Z) (P 0 (P 1 (P 1 (Z) (P 0 (P 1 (Z) (Z)) (Z))) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,0),(4,1),(5,1),(5,0),(6,1),(7,1)] = P 0 (P 1 (P 1 (Z) (P 0 (P 1 (P 1 (Z) (P 0 (P 1 (P 1 (Z) (Z)) (Z)) (Z))) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,1)] = P 0 (P 1 (P 1 (Z) (P 1 (Z) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,1),(2,1)] = P 0 (P 1 (P 1 (Z) (P 1 (Z) (Z))) (P 1 (Z) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,1),(2,1),(3,1)] = P 0 (P 1 (P 1 (Z) (P 1 (Z) (Z))) (P 1 (P 1 (Z) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,1),(2,1),(3,1),(3,1)] = P 0 (P 1 (P 1 (Z) (P 1 (Z) (Z))) (P 1 (P 1 (Z) (P 1 (Z) (Z))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,1),(3,0)] = P 0 (P 1 (P 1 (Z) (P 1 (Z) (P 0 (Z) (Z)))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,1),(3,0),(4,1)] = P 0 (P 1 (P 1 (Z) (P 1 (Z) (P 0 (P 1 (Z) (Z)) (Z)))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,1),(3,0),(4,1),(5,1)] = P 0 (P 1 (P 1 (Z) (P 1 (Z) (P 0 (P 1 (P 1 (Z) (Z)) (Z)) (Z)))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,1),(3,0),(4,1),(5,1),(5,1)] = P 0 (P 1 (P 1 (Z) (P 1 (Z) (P 0 (P 1 (P 1 (Z) (P 1 (Z) (Z))) (Z)) (Z)))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,1),(3,1)] = P 0 (P 1 (P 1 (Z) (P 1 (Z) (P 1 (Z) (Z)))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(3,1),(3,1),(3,1)] = P 0 (P 1 (P 1 (Z) (P 1 (Z) (P 1 (Z) (P 1 (Z) (Z))))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,0)] = P 0 (P 1 (P 1 (P 0 (Z) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,0),(2,1)] = P 0 (P 1 (P 1 (P 0 (Z) (Z)) (Z)) (P 1 (Z) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,0),(2,1),(3,1)] = P 0 (P 1 (P 1 (P 0 (Z) (Z)) (Z)) (P 1 (P 1 (Z) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,0),(2,1),(3,1),(3,1)] = P 0 (P 1 (P 1 (P 0 (Z) (Z)) (Z)) (P 1 (P 1 (Z) (P 1 (Z) (Z))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,0),(2,1),(3,1),(4,0)] = P 0 (P 1 (P 1 (P 0 (Z) (Z)) (Z)) (P 1 (P 1 (P 0 (Z) (Z)) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,0),(3,0)] = P 0 (P 1 (P 1 (P 0 (Z) (Z)) (P 0 (Z) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,0),(3,0),(4,1),(5,1),(6,0)] = P 0 (P 1 (P 1 (P 0 (Z) (Z)) (P 0 (P 1 (P 1 (P 0 (Z) (Z)) (Z)) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,0),(3,1)] = P 0 (P 1 (P 1 (P 0 (Z) (Z)) (P 1 (Z) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,0),(3,1),(4,0)] = P 0 (P 1 (P 1 (P 0 (Z) (Z)) (P 1 (P 0 (Z) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,0),(4,0)] = P 0 (P 1 (P 1 (P 0 (Z) (P 0 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,0),(5,0)] = P 0 (P 1 (P 1 (P 0 (P 0 (Z) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,0),(5,1)] = P 0 (P 1 (P 1 (P 0 (P 1 (Z) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,0),(5,1),(6,1)] = P 0 (P 1 (P 1 (P 0 (P 1 (P 1 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,0),(5,1),(6,1),(7,0)] = P 0 (P 1 (P 1 (P 0 (P 1 (P 1 (P 0 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1)] = P 0 (P 1 (P 1 (P 1 (Z) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(2,1)] = P 0 (P 1 (P 1 (P 1 (Z) (Z)) (Z)) (P 1 (Z) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(2,1),(3,1)] = P 0 (P 1 (P 1 (P 1 (Z) (Z)) (Z)) (P 1 (P 1 (Z) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(2,1),(3,1),(4,0)] = P 0 (P 1 (P 1 (P 1 (Z) (Z)) (Z)) (P 1 (P 1 (P 0 (Z) (Z)) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(2,1),(3,1),(4,0),(5,1),(6,1),(7,1)] = P 0 (P 1 (P 1 (P 1 (Z) (Z)) (Z)) (P 1 (P 1 (P 0 (P 1 (P 1 (P 1 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(2,1),(3,1),(4,0),(5,1),(6,1),(7,1),(3,1)] = P 0 (P 1 (P 1 (P 1 (Z) (Z)) (Z)) (P 1 (P 1 (P 0 (P 1 (P 1 (P 1 (Z) (Z)) (Z)) (Z)) (Z)) (P 1 (Z) (Z))) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(2,1),(3,1),(4,1)] = P 0 (P 1 (P 1 (P 1 (Z) (Z)) (Z)) (P 1 (P 1 (P 1 (Z) (Z)) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(3,0)] = P 0 (P 1 (P 1 (P 1 (Z) (Z)) (P 0 (Z) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(3,0),(4,1),(5,1),(6,1)] = P 0 (P 1 (P 1 (P 1 (Z) (Z)) (P 0 (P 1 (P 1 (P 1 (Z) (Z)) (Z)) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(3,1)] = P 0 (P 1 (P 1 (P 1 (Z) (Z)) (P 1 (Z) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(3,1),(3,1)] = P 0 (P 1 (P 1 (P 1 (Z) (Z)) (P 1 (Z) (P 1 (Z) (Z)))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(3,1),(4,0)] = P 0 (P 1 (P 1 (P 1 (Z) (Z)) (P 1 (P 0 (Z) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(3,1),(4,1)] = P 0 (P 1 (P 1 (P 1 (Z) (Z)) (P 1 (P 1 (Z) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(4,0)] = P 0 (P 1 (P 1 (P 1 (Z) (P 0 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(4,1)] = P 0 (P 1 (P 1 (P 1 (Z) (P 1 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(4,1),(4,1)] = P 0 (P 1 (P 1 (P 1 (Z) (P 1 (Z) (P 1 (Z) (Z)))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(5,0)] = P 0 (P 1 (P 1 (P 1 (P 0 (Z) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(5,0),(4,0)] = P 0 (P 1 (P 1 (P 1 (P 0 (Z) (Z)) (P 0 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(5,0),(4,1)] = P 0 (P 1 (P 1 (P 1 (P 0 (Z) (Z)) (P 1 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(5,0),(4,1),(5,0)] = P 0 (P 1 (P 1 (P 1 (P 0 (Z) (Z)) (P 1 (P 0 (Z) (Z)) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(5,0),(5,0)] = P 0 (P 1 (P 1 (P 1 (P 0 (Z) (P 0 (Z) (Z))) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(5,0),(6,0)] = P 0 (P 1 (P 1 (P 1 (P 0 (P 0 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(5,0),(6,1)] = P 0 (P 1 (P 1 (P 1 (P 0 (P 1 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(5,1)] = P 0 (P 1 (P 1 (P 1 (P 1 (Z) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(5,1),(4,1)] = P 0 (P 1 (P 1 (P 1 (P 1 (Z) (Z)) (P 1 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(5,1),(4,1),(5,0)] = P 0 (P 1 (P 1 (P 1 (P 1 (Z) (Z)) (P 1 (P 0 (Z) (Z)) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(5,1),(4,1),(5,1)] = P 0 (P 1 (P 1 (P 1 (P 1 (Z) (Z)) (P 1 (P 1 (Z) (Z)) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(5,1),(5,0)] = P 0 (P 1 (P 1 (P 1 (P 1 (Z) (P 0 (Z) (Z))) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(5,1),(5,0),(6,1)] = P 0 (P 1 (P 1 (P 1 (P 1 (Z) (P 0 (P 1 (Z) (Z)) (Z))) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(5,1),(5,1)] = P 0 (P 1 (P 1 (P 1 (P 1 (Z) (P 1 (Z) (Z))) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(5,1),(6,0)] = P 0 (P 1 (P 1 (P 1 (P 1 (P 0 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(5,1),(6,0),(7,1)] = P 0 (P 1 (P 1 (P 1 (P 1 (P 0 (P 1 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(5,1),(6,1)] = P 0 (P 1 (P 1 (P 1 (P 1 (P 1 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)] = P 0 (P 1 (P 1 (P 1 (P 1 (P 1 (P 1 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2)] = P 0 (P 1 (P 2 (Z) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(1,0)] = P 0 (P 1 (P 2 (Z) (Z)) (P 0 (Z) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(2,1)] = P 0 (P 1 (P 2 (Z) (Z)) (P 1 (Z) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(2,1),(2,1)] = P 0 (P 1 (P 2 (Z) (Z)) (P 1 (Z) (P 1 (Z) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(2,1),(3,0)] = P 0 (P 1 (P 2 (Z) (Z)) (P 1 (P 0 (Z) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(2,1),(3,1)] = P 0 (P 1 (P 2 (Z) (Z)) (P 1 (P 1 (Z) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(2,1),(3,1),(4,0)] = P 0 (P 1 (P 2 (Z) (Z)) (P 1 (P 1 (P 0 (Z) (Z)) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(2,1),(3,1),(4,1)] = P 0 (P 1 (P 2 (Z) (Z)) (P 1 (P 1 (P 1 (Z) (Z)) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(2,1),(3,2)] = P 0 (P 1 (P 2 (Z) (Z)) (P 1 (P 2 (Z) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(2,1),(3,2),(2,1),(3,2)] = P 0 (P 1 (P 2 (Z) (Z)) (P 1 (P 2 (Z) (Z)) (P 1 (P 2 (Z) (Z)) (Z)))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(3,0)] = P 0 (P 1 (P 2 (Z) (P 0 (Z) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(3,1)] = P 0 (P 1 (P 2 (Z) (P 1 (Z) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(3,1),(3,1)] = P 0 (P 1 (P 2 (Z) (P 1 (Z) (P 1 (Z) (Z)))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(3,1),(4,0)] = P 0 (P 1 (P 2 (Z) (P 1 (P 0 (Z) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(3,1),(4,1)] = P 0 (P 1 (P 2 (Z) (P 1 (P 1 (Z) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(3,1),(4,2)] = P 0 (P 1 (P 2 (Z) (P 1 (P 2 (Z) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(3,1),(4,2),(3,1)] = P 0 (P 1 (P 2 (Z) (P 1 (P 2 (Z) (Z)) (P 1 (Z) (Z)))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(3,1),(4,2),(3,1),(4,2)] = P 0 (P 1 (P 2 (Z) (P 1 (P 2 (Z) (Z)) (P 1 (P 2 (Z) (Z)) (Z)))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(3,1),(4,2),(4,0)] = P 0 (P 1 (P 2 (Z) (P 1 (P 2 (Z) (P 0 (Z) (Z))) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(3,1),(4,2),(4,1)] = P 0 (P 1 (P 2 (Z) (P 1 (P 2 (Z) (P 1 (Z) (Z))) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(3,1),(4,2),(4,1),(5,2)] = P 0 (P 1 (P 2 (Z) (P 1 (P 2 (Z) (P 1 (P 2 (Z) (Z)) (Z))) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(3,2)] = P 0 (P 1 (P 2 (Z) (P 2 (Z) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(3,2),(3,2)] = P 0 (P 1 (P 2 (Z) (P 2 (Z) (P 2 (Z) (Z)))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,0)] = P 0 (P 1 (P 2 (P 0 (Z) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,1)] = P 0 (P 1 (P 2 (P 1 (Z) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,1),(3,2)] = P 0 (P 1 (P 2 (P 1 (Z) (Z)) (P 2 (Z) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,1),(3,2),(4,0)] = P 0 (P 1 (P 2 (P 1 (Z) (Z)) (P 2 (P 0 (Z) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,1),(3,2),(4,1)] = P 0 (P 1 (P 2 (P 1 (Z) (Z)) (P 2 (P 1 (Z) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,1),(4,0)] = P 0 (P 1 (P 2 (P 1 (Z) (P 0 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,1),(4,1)] = P 0 (P 1 (P 2 (P 1 (Z) (P 1 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,1),(5,0)] = P 0 (P 1 (P 2 (P 1 (P 0 (Z) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,1),(5,1)] = P 0 (P 1 (P 2 (P 1 (P 1 (Z) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,1),(5,1),(6,1)] = P 0 (P 1 (P 2 (P 1 (P 1 (P 1 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,1),(5,2)] = P 0 (P 1 (P 2 (P 1 (P 2 (Z) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,1),(5,2),(6,1)] = P 0 (P 1 (P 2 (P 1 (P 2 (P 1 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,1),(5,2),(6,1),(7,2)] = P 0 (P 1 (P 2 (P 1 (P 2 (P 1 (P 2 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2)] = P 0 (P 1 (P 2 (P 2 (Z) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(3,2)] = P 0 (P 1 (P 2 (P 2 (Z) (Z)) (P 2 (Z) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(3,2),(4,2)] = P 0 (P 1 (P 2 (P 2 (Z) (Z)) (P 2 (P 2 (Z) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(4,0)] = P 0 (P 1 (P 2 (P 2 (Z) (P 0 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(4,1)] = P 0 (P 1 (P 2 (P 2 (Z) (P 1 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(4,2)] = P 0 (P 1 (P 2 (P 2 (Z) (P 2 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,0)] = P 0 (P 1 (P 2 (P 2 (P 0 (Z) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,1)] = P 0 (P 1 (P 2 (P 2 (P 1 (Z) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,1),(6,2)] = P 0 (P 1 (P 2 (P 2 (P 1 (P 2 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,2)] = P 0 (P 1 (P 2 (P 2 (P 2 (Z) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,2),(3,2),(4,2),(5,2)] = P 0 (P 1 (P 2 (P 2 (P 2 (Z) (Z)) (Z)) (P 2 (P 2 (P 2 (Z) (Z)) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,2),(4,0)] = P 0 (P 1 (P 2 (P 2 (P 2 (Z) (Z)) (P 0 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,2),(4,1)] = P 0 (P 1 (P 2 (P 2 (P 2 (Z) (Z)) (P 1 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,2),(4,2)] = P 0 (P 1 (P 2 (P 2 (P 2 (Z) (Z)) (P 2 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,2),(4,2),(5,0)] = P 0 (P 1 (P 2 (P 2 (P 2 (Z) (Z)) (P 2 (P 0 (Z) (Z)) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,2),(4,2),(5,1)] = P 0 (P 1 (P 2 (P 2 (P 2 (Z) (Z)) (P 2 (P 1 (Z) (Z)) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,2),(4,2),(5,2)] = P 0 (P 1 (P 2 (P 2 (P 2 (Z) (Z)) (P 2 (P 2 (Z) (Z)) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,2),(5,0)] = P 0 (P 1 (P 2 (P 2 (P 2 (Z) (P 0 (Z) (Z))) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,2),(5,1)] = P 0 (P 1 (P 2 (P 2 (P 2 (Z) (P 1 (Z) (Z))) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,2),(5,2)] = P 0 (P 1 (P 2 (P 2 (P 2 (Z) (P 2 (Z) (Z))) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,2),(5,2),(5,2)] = P 0 (P 1 (P 2 (P 2 (P 2 (Z) (P 2 (Z) (P 2 (Z) (Z)))) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,2),(6,0)] = P 0 (P 1 (P 2 (P 2 (P 2 (P 0 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,2),(6,1)] = P 0 (P 1 (P 2 (P 2 (P 2 (P 1 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,2),(6,2)] = P 0 (P 1 (P 2 (P 2 (P 2 (P 2 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,2),(5,2),(6,2),(7,2)] = P 0 (P 1 (P 2 (P 2 (P 2 (P 2 (P 2 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3)] = P 0 (P 1 (P 2 (P 3 (Z) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(2,1)] = P 0 (P 1 (P 2 (P 3 (Z) (Z)) (Z)) (P 1 (Z) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(2,1),(3,2)] = P 0 (P 1 (P 2 (P 3 (Z) (Z)) (Z)) (P 1 (P 2 (Z) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(2,1),(3,2),(4,3)] = P 0 (P 1 (P 2 (P 3 (Z) (Z)) (Z)) (P 1 (P 2 (P 3 (Z) (Z)) (Z)) (Z))) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(3,0)] = P 0 (P 1 (P 2 (P 3 (Z) (Z)) (P 0 (Z) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(3,1)] = P 0 (P 1 (P 2 (P 3 (Z) (Z)) (P 1 (Z) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(3,2)] = P 0 (P 1 (P 2 (P 3 (Z) (Z)) (P 2 (Z) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(3,2),(4,3)] = P 0 (P 1 (P 2 (P 3 (Z) (Z)) (P 2 (P 3 (Z) (Z)) (Z))) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(4,0)] = P 0 (P 1 (P 2 (P 3 (Z) (P 0 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(4,1)] = P 0 (P 1 (P 2 (P 3 (Z) (P 1 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(4,2)] = P 0 (P 1 (P 2 (P 3 (Z) (P 2 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(4,3)] = P 0 (P 1 (P 2 (P 3 (Z) (P 3 (Z) (Z))) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(5,0)] = P 0 (P 1 (P 2 (P 3 (P 0 (Z) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(5,1)] = P 0 (P 1 (P 2 (P 3 (P 1 (Z) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(5,2)] = P 0 (P 1 (P 2 (P 3 (P 2 (Z) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(5,3)] = P 0 (P 1 (P 2 (P 3 (P 3 (Z) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(5,3),(5,3)] = P 0 (P 1 (P 2 (P 3 (P 3 (Z) (P 3 (Z) (Z))) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(5,3),(6,0)] = P 0 (P 1 (P 2 (P 3 (P 3 (P 0 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(5,3),(6,3)] = P 0 (P 1 (P 2 (P 3 (P 3 (P 3 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(5,3),(6,3),(7,3)] = P 0 (P 1 (P 2 (P 3 (P 3 (P 3 (P 3 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(5,4)] = P 0 (P 1 (P 2 (P 3 (P 4 (Z) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(5,4),(5,4)] = P 0 (P 1 (P 2 (P 3 (P 4 (Z) (P 4 (Z) (Z))) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(5,4),(6,4)] = P 0 (P 1 (P 2 (P 3 (P 4 (P 4 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(5,4),(6,4),(7,4)] = P 0 (P 1 (P 2 (P 3 (P 4 (P 4 (P 4 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(5,4),(6,5)] = P 0 (P 1 (P 2 (P 3 (P 4 (P 5 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
#guard transD [(0,0),(1,0),(2,1),(3,2),(4,3),(5,4),(6,5),(7,6)] = P 0 (P 1 (P 2 (P 3 (P 4 (P 5 (P 6 (Z) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)) (Z)
end

end DBMS
