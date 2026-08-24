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

end DBMS
